#---------------------------------------------------------------------------
# Topic 2: 
# Two-piece distribution based semiparametric quantile regression for right censored data 
# This is the code for part II simulation of Model I:  
# comparing the new proposed method with existing competitors 
# in estimating the conditional quantile of the survival time 
#---------------------------------------------------------------------------
#Libraries 
rm(list = ls())
library(rqPen)
library(nloptr)
library(quantreg)
library(survival) 
library(gamlss)
library(gamlss.cens)
library(KernSmooth)
library(locpol)
library(pec)
library(locfit)
library(dplyr)# for case_when function 
# Kernel function 
ker <- function(ktype, x) {
  if(ktype=="uniform"){
    result <- dunif(x, -1, 1)
  }
  if (ktype == "normal") {
    result <- dnorm(x)
    
  }
  else if (ktype == "ep") {
    result <- ifelse(abs(x) <= 1 , 3/4*(1 - x^2), 0 )
    
  }
  else if (ktype == "biweight") {
    result <- ifelse(abs(x) <= 1 , 15/16*(1 - x^2)^2, 0 )
    
  }
  else if (ktype == "triweight") {
    result <- ifelse(abs(x) <= 1 , 35/32*(1 - x^2)^3, 0 )
  } else if(ktype =="cosine"){
    result <- ifelse(abs(x) <= 1 , pi/4*cos(pi/2*x), 0 )
  }
  return(result)
}

# Standard Laplace distribution 
f0_La <- function(s){0.5*exp(-abs(s))} #  density
F0_La <- function(s){0.5+0.5*sign(s)*(1-exp(-abs(s)))} #  CDF 
QF_La <- function(tau){-sign(tau-0.5)*log(1-2*abs(tau-0.5))}#  quantile 
# Link function
gid      <- function(s){s}# identity link function 
gid.inv  <- function(s){s}# inverse of gid
# glog      <- function(s){log(s)}# identity link function 
# glog.inv  <- function(s){exp(s)}# inverse of gid
# glogit    <-function(s){log(exp(s)-1)}
# glogit.inv<-function(s){log(exp(s)+1)}

#--------------------------------------------------------
# eta: location parameter
# phi: scale parameter 
# alpha: index parameter
#--------------------------------------------------------
# the error distribution follows TPA Laplace with identity link function 
# density for TPA with 

dtpa <-function(y,  eta, phi, alpha, f0 = f0_La, g = gid)
{
  g.prime <- Deriv::Deriv(g, "s")
  coeff <- 2*alpha*(1-alpha)*g.prime(y)/phi
  den <-   ifelse(y < eta,(coeff*f0((1-alpha)*(g(eta)-g(y))/phi)),
                  (coeff*f0(alpha*(g(y)-g(eta))/phi)))
  return(den=den)
}
# CDF/Survival 
ptpa <- function(q,  eta, phi, alpha, F0 = F0_La, g = gid, lower.tail = TRUE) {
  p <- ifelse(q < eta, (2*alpha*F0((1 - alpha)*(g(q) - g(eta))/phi)),
              (2*alpha - 1 + 2*(1 - alpha)*F0(alpha*(g(q) - g(eta))/phi)))
  ifelse(test = lower.tail == TRUE, yes = return(p), no = return(1-p))
}
# quantile function 
qtpa <- function(tau, eta, phi, alpha, F0=F0_La, QF = QF_La, g=gid, g.inv=gid.inv){
  # if (is.null(QF)){
  #   QF <- GoFKernel::inverse(F0, lower =0, upper = Inf)
  # }
  # g.inv <- GoFKernel::inverse(g,lower,upper)
  # 
  q <-ifelse(tau< alpha, g.inv(g(eta) + (phi/(1-alpha))*QF(tau/(2*alpha))),
            g.inv(g(eta) + (phi/alpha)*QF((1+tau-2*alpha)/(2*(1-alpha)))))
  return(q=q)
}

# Random number generation
rtpa<- function(n, eta, phi, alpha,F0 = F0_La, QF = QF_La, g = gid, g.inv = gid.inv){
  u <- runif(n, min = 0, max = 1)
  # if (is.null(QF)){
  #   QF <- GoFKernel::inverse(F0, lower =0, upper = Inf)
  # }
  # g.inv <- GoFKernel::inverse(g,lower = 0,upper = Inf)
  r <- ifelse(u< alpha, g.inv(g(eta)+(phi/(1-alpha))*QF(u/(2*alpha))),
              g.inv(g(eta)+(phi/alpha)*QF((1+u-2*alpha)/(2*(1-alpha)))))
  return(r=r)
}

#  data generation 
PII_MI_data <- function(n, beta1, tau,  alpha = 0.5, theta_c){
  x11 <- as.matrix(runif(n, 0, 1))
  x12 <- as.matrix(runif(n, 0, 1))
  x2 <- as.matrix(runif(n, 0, 2))
  eps <- suppressWarnings(rtpa(n=n, eta = 0, phi = 1, alpha = alpha))
  q_eps <- qtpa(tau = tau, eta = 1, phi = 1, alpha = alpha)
  eps_star <- eps - q_eps
  nonpar <- exp(sin(2*pi*x2) - 1.5)
  Q_z <- cbind(x11, x12)%*%as.vector(beta1) + nonpar*q_eps
  ST <- Q_z + nonpar*(eps - q_eps)
  CT <- rnorm(n, theta_c, 1)
  y <- pmin(ST,CT)
  d <- as.matrix(as.numeric(ST<= CT))
  data <- as.data.frame(cbind(x11,  x12,  x2,  y,  d, ST, CT))
  colnames(data) <- c("x11", "x12", "x2", "y", "d", "ST", "CT")
  return(data)
}
# set.seed(2021)
# theta_c: censoring parameter 
# beta1 = c(1, 2); tau <- 0.5; n <- 100
# test.data <- PII_MI_data(n, beta1, tau,  alpha = 0.25, theta_c = 3.5)
# sum(test.data$d==0)/n
# plot(test.data$x11, test.data$y)

#-----------------------------------------------------------------------------
# Codes recieved from  
# Christou, E., & Akritas, M. G. (2019). Single index quantile regression for censored data. Statistical
# Methods & Applications, 28(4), 655-678.
#-------------------------------------------------------------------------------
#  Nadaraya-Watson estimator (proposed parametrization) 
#  used to estimat the index or ghat^new_cd
#-------------------------------------------------------------------------------
hatQ_NW_beta1 <- function(x, Q_LL, tau, beta1, h, ktype){
  n = dim(x)[1]
  p = dim(x)[2]
  
  hatQ_NW_beta = as.null(n)
  for (i in 1:n){
    z = x - t(matrix(rep(x[i,],p*n),p,n))
    K = apply(z%*%(c(1, beta1))/h, 1, ker, ktype = ktype)
    # K = apply(z%*%c(1,beta1)/h, 1, ker, ktype = ktype)
    hatQ_NW_den = sum(K)
    hatQ_NWi = (sum(K*Q_LL))/(hatQ_NW_den)
    hatQ_NW_beta[i] = hatQ_NWi
  }
  return(hatQ_NW_beta)
}

#----------------------------------------------------------------------------
# non-parametric /local linear conditional quantile with censored data
#----------------------------------------------------------------------------

llqr_nq = function(x, z, d, h, tau, hatGn, ktype){
  x = as.matrix(x)
  n = length(z)
  p = dim(x)[2]
  fv = as.null(n)
  dv = matrix(0, n, p)
  #  if(length(h)<=1) stop("h must be a vector") # for this model only. 
  
  for(i in 1:n){
    newx = matrix(0,n,p)
    newx = x - t(matrix(rep(x[i,],p*n),p,n)) 
    if(p == 1) {
      wx = (d/hatGn)*ker(ktype = ktype, x = newx/h)
    } else{  
      ker.w <- apply(newx/h, MARGIN = 2, FUN = ker, ktype = ktype)
      wx <- (d/hatGn)*apply(ker.w, 1, prod)
    }
    r = rq(z~newx, weights = wx, tau = tau, ci = FALSE)
    fv[i] = r$coef[1]
    dv[i,] = r$coef[-1]
  }
  list(x = x, fv = fv, dv = dv)
}

#----------------------------------------------------------------------------
# local linear conditional quantile with censored data
#----------------------------------------------------------------------------
llrq_cd = function(x, z, d, h, tau, hatGn, ktype){
  n = length(z)
  p = dim(x)[2]
  fv = as.null(n)
  dv = matrix(0,n,p)
  for(i in 1:dim(x)[1]){
    newx = matrix(0,n,p)
    newx = x-t(matrix(rep(x[i,],p*n),p,n))
    ker.w <- apply(newx/h, MARGIN = 2, FUN = ker, ktype = ktype)
    wx <- (d/hatGn)*apply(ker.w, 1, prod)
    r = rq(z~newx, weights=wx, tau=tau, ci = FALSE)
    fv[i] = r$coef[1]
    dv[i,] = r$coef[-1]
  }
  list(x = x, fv = fv, dv = dv)
}

#----------------------------------------------------------------------------
#  lprq0: local polynomial regression quantile. 
#          this estimates the quantile and its derivative at the point x_0
#----------------------------------------------------------------------------

lprq0 <- function(x, y,d, hatGn, h,  tau = 0.5, x0, ktype="ep")  
{
  require(quantreg)
  fv <- x0
  dv <- x0
  
  z <- x - x0
  wx <- (d/hatGn)*ker(ktype = ktype, x=z/h)
  r <- rq(y ~ z, weights = wx, tau = tau, ci = FALSE)
  fv <- r$coef[1]
  dv <- r$coef[2]
  list(x0 = x0, fv = fv, dv = dv)
}
#------------------------------------------------------------------------------------
# partially linear  local-likelihood function
#------------------------------------------------------------------------------------
par.nll <- function(beta, betahat = NULL, phihat = NULL, alpha = 0.25,
                    y, d, x1, x2 = NULL, ker = NULL) {
  y <- as.matrix(y)# observed survival time 
  d <- as.matrix(d)# censoring indicator 
  p1 <- dim(x1)[2] # set of covariates for the parametric component
  p2 <- dim(x2)[2] # set of covariates for the nonparametric component
  p <- p1 + p2
  
  if (!is.null(betahat) & is.null(phihat)){
    x1 <- as.matrix(x1)
    x2 <- as.matrix(x2)
    #  profile  log-likeihood function for local estimation/stage  1  and final stage
    fix.mu <- x1%*%as.vector(betahat)
    phi <- exp(x2%*%as.vector(beta))
    logL <- (d*log(dtpa(y, eta = fix.mu, phi = phi, alpha = alpha)) + 
               (1-d)*log(ptpa(q = y, eta = fix.mu, phi = phi, alpha = alpha, lower.tail = FALSE)))*ker
  } else if(is.null(betahat) & !is.null(phihat)){
    #  profile  log-likeihood function for global estimation/stage  2
    x1 <- as.matrix(x1)
    mu <- x1%*%as.vector(beta)
    logL <- (d*log(dtpa(y, eta = mu, phi = phihat, alpha = alpha)) + 
               (1-d)*log(ptpa(q = y, eta = mu, phi = phihat, alpha = alpha, lower.tail = F)))
  } 
  return(-sum(logL[!is.infinite(logL)]))
}
#------------------------------------------------------------------------------------
# partial linear fitting  
#------------------------------------------------------------------------------------
partial.fit <- function(y, d, x1, x2, alpha = 0.25,  h, x0, ktype = "ep"){
  # checks if y is univariate
  if (dim(y)[2] > 1 |dim(d)[2]>1) {
    stop(paste("y and d need to be  univariate response and indicator. y is a", dim(y)[2], "-dimensional response in this case."))
  }
  # checks if the data  are arranged in matrix format 
  if (!is.matrix(x1)) {
    stop(paste("x's, y and d  should be arranged in matrix format."))
  }
  # initialization
  in_fit <- suppressWarnings(gamlss(Surv(y, d) ~x1[,1] + x1[,2] -1,
                                    sigma.formula = ~x2-1, nu.fix = TRUE,   nu.start = 1,  
                                    family = cens(PE2), trace = FALSE))
  int_beta1 <- as.numeric(coef(in_fit))
  int_beta2 <- c(log(QBAsyDist::mleALaD(y)$phi.ALaD), as.numeric(in_fit$sigma.coefficients))
  
  
  # perform the estimation at the entire design matrix X2 
  n <- dim(y)[1]
  p1 <- dim(x1)[2]
  p2 <- dim(x2)[2]
  x0 <- as.matrix(x0); m <- dim(x0)[1]
  
  beta2_hat_stage1 <- matrix(0, nrow = m, ncol = p2+1)
  phihat_stage1 <- as.null(n)
  
  for(i in 1:m) {
    new.x2 <- matrix(0, n, p2)
    z <- x2 - t(matrix(rep(x0[i,], p2*n), p2, n))
    new.x2 <- cbind(1, z) # small x2
    w <- apply(z/h, 2, FUN =  ker, ktype = ktype )
    w <- as.matrix(apply(w, 1, prod))
    # stage  1/local estimates: Fix the parametric component and estimate the non-paramteric component 
    start.beta <- int_beta2
    
    opts <- list("algorithm" = "NLOPT_LN_NELDERMEAD",
                 "xtol_rel" = rep(1.0e-8, length(start.beta)),
                 "xtol_abs" = rep(1.0e-8, length(start.beta)),
                 "maxeval" = 10000, "print_level" = 0)
    fit_local_stage1 <- nloptr(x0 = start.beta, eval_f  = par.nll, opts = opts,
                                   betahat = int_beta1, phihat = NULL,   alpha = alpha,
                                   y = y, d = d, x1 = x1, x2 = new.x2, ker = w,
                                   lb = rep(-Inf, length(start.beta)), 
                                   ub = rep(Inf, length(start.beta)))
    beta2_hat_stage1[i,] <-  fit_local_stage1$solution 
    phihat_stage1[i] <- exp(beta2_hat_stage1[i,1])
  }
  # Stage 2/global estimates: Fix the non-parametric  at stage 1  and estimate the parametric component
  start.beta <- int_beta1 # initial value 
  phi_hat <- as.matrix(phihat_stage1)

    fit_global_stage2 <- nloptr(x0 = start.beta, eval_f  = par.nll, opts = opts,
                                  betahat = NULL, phihat = phi_hat,  alpha = alpha,
                                  y = y, d = d, x1 = x1, x2 = NULL,  ker = NULL,
                                  lb = rep(-Inf, length(start.beta)), 
                                  ub = rep(Inf, length(start.beta)))
    beta1_hat <- fit_global_stage2$solution
  # Stage 3/final local estimates: update the nonparametric component 
  beta2_hat <- matrix(0, m, p2+1)
  phihat <- as.null(m)
  for (i in 1:m) {
    new.x2 <- matrix(0, n, p2)
    z <- x2 - t(matrix(rep(x0[i,], p2*n), p2, n))
    new.x2 <- cbind(1, z) # small x2
    w <- apply(z/h, 2, FUN =  ker, ktype = ktype )
    w <- as.matrix(apply(w, 1, prod))        
    # initial  value 
    start.beta <- as.vector(apply(beta2_hat_stage1, 2, mean, na.rm=TRUE))
    
    fit_local_stage3 <- nloptr(x0 = start.beta, eval_f  = par.nll, opts = opts,
                                   betahat = beta1_hat, phihat = NULL,  alpha = alpha,
                                   y = y, d = d, x1 = x1, x2 = new.x2, ker = w,
                                   lb = rep(-Inf, length(start.beta)), 
                                   ub = rep(Inf, length(start.beta)))
        beta2_hat[i,] <-  fit_local_stage3$solution
        phihat[i] <-   exp(beta2_hat[i,1])
  }
  return(list(x0 = x0, beta1_hat =  beta1_hat, beta2_hat = beta2_hat, phihat = phihat)) 
}

#---------------------------------------------------------------
# cross- validation for bandwidth selection  
#---------------------------------------------------------------
cv_tpa <- function(data, beta1, tau, alpha = 0.25, ncv, nbw, ktype){
  # beta1: true parameter value
  dftrain <- data[sample(nrow(data)),]
  folds <- cut(seq(1,nrow(data)), breaks = ncv, labels = FALSE)
  WAQRL_cv <- matrix(0, nrow = ncv, ncol = nbw)
  # grid of h
  h_vector <- round(seq(0.05, 0.75, length.out = nbw), 3 )
  # Do the cross validation for each fold
  for(i in 1:ncv){
    # Segement the data by fold using the which() function 
    test_indexes <- which(folds == i, arr.ind = TRUE)
    testdata <- dftrain[test_indexes, ]
    traindata <- dftrain[-test_indexes, ]
    traindata <- traindata[order(traindata$y),]
    # For each fold, fit a local polynomial  and calculate the ISE
    x1 <- cbind(traindata$x11, traindata$x12)
    x2 <- as.matrix(traindata$x2)
    y <- as.matrix(traindata$y)
    d <- as.matrix(traindata$d)
    n <- dim(y)[1]
    # estimate Gnhat 
    WKM = ipcw(Hist(y,d)~1, data = traindata, method="marginal",
               times = sort(unique(traindata$y)),
               subjectTimes = traindata$y, subjectTimesLag  =0)$IPCW.subjectTimes
    hatGn <- as.matrix(case_when(WKM == 0 ~ 1/(2*n), TRUE ~ WKM))
    # true values 
    q_eps <- qtpa(tau = tau, eta = 0, phi = 1, alpha = alpha)
    phi <- exp(sin(2*pi*x2) - 1.5) 
    qtrue <- x1%*%beta1 + phi*q_eps
    #
    WAQRL_h <- sapply(1:nbw, function(j) { 
      cv.fit <- partial.fit(y = y, d = d, x1 = x1, x2 = x2, alpha = alpha, 
                            h = h_vector[j], x0 = x2, ktype =  ktype)
      qhat <- x1%*%c(beta1[1], cv.fit$beta1_hat[2]) + as.matrix(cv.fit$phihat*q_eps)
      mean((d/hatGn)*check(qtrue - qhat, tau = tau), na.rm = T)
    })
    WAQRL_cv[i,] <- c(WAQRL_h)
  }
  WAQRL <- apply(  WAQRL_cv, 2, mean, na.rm =TRUE)
  cv <- as.data.frame(cbind(h_vector,   WAQRL))
  h_cv <- cv$h_vector[which.min(cv$  WAQRL)]
  return(list("h_cv" = h_cv, "cv" = cv))
}
#------------------------------------------------------------------------
## Bravo (SPQR) Method: MM algorithm 
#------------------------------------------------------------------------

# Global part: parametric component 
Bravo_Global <- function(z, d, x1, tau, beta,  theta, 
                         hatGn, toler = 1e-6, maxit = 5000){
  # initialization 
  i <- 0
  n <- dim(z)[1]
  df.matX <- x1 
  zz <- z - theta# theta should have same length as z
  # Calculation of epsilon
  tn  <- toler/n
  e0  <- -tn/log(tn)
  eps <- (e0 - tn)/(1 + log(e0))  
  # Initialization of condition for break
  cond <- TRUE
  while(cond)
  { 
    beta.prev <- beta
    r     <- zz  - df.matX%*%as.matrix(beta)
    w     <- c(d/hatGn) # censoring weight 
    W.entries <- c(w*(1/(eps + abs(r))))
    W.mat    <- diag(W.entries) # nxn matrix
    d.mat    <- as.matrix(c(1 - 2*tau - r/(eps + abs(r))))# nx1 matrix
    beta     <- as.matrix(beta.prev) - (0.5)^i*solve(t(df.matX)%*%W.mat%*%df.matX)%*%(t(df.matX)%*%d.mat)
    cond     <- max(abs(beta -  beta.prev)) > toler
    #cond <- norm(beta12 - beta12.prev, type = "2") > toler # euclidean norm 
    i <- i + 1
    
    if(i > maxit){warning("WARNING: Algorithm did not converge"); break} 
  }
  return(list("beta_hat"= c(beta), "Iter" = i))
}

# local part: nonparametric component 

Bravo_local <- function(z, d, x1, x2, tau, beta,  theta,  
                        h, x0, hatGn, ktype, toler = 1e-6, maxit = 5000){
  # Initialization of condition for break
  i <- 0
  
  n <- dim(z)[1]
  
  beta.fixed = x1%*%as.matrix(beta) #cbind(1, x1)%*%as.vector(beta)
  zz <-  z - beta.fixed # response  for Model I
  new.x2 <- x2 - x0
  df.matX <- cbind(1, new.x2) # local covariate matrix
  Kn <- as.matrix(ker(ktype = ktype, x = new.x2/h)) # scaled kernel 
  
  # Calculation of epsilon
  tn  <- toler/n
  e0  <- -tn/log(tn)
  eps <- (e0 - tn)/(1 + log(e0))
  
  
  cond <- TRUE
  while(cond)
  { 
    theta.prev <- theta
    r <-  zz - df.matX%*%as.matrix(theta)
    w <- (d/hatGn)*(1/(eps + abs(r)))*Kn
    W.entries <- c(w)
    W.mat    <- diag(W.entries) 
    d.mat    <- as.matrix(c(1 - 2*tau - r/(eps + abs(r)))*Kn)
    theta <- as.matrix(theta.prev) - 0.5^i*solve(t(df.matX)%*%W.mat%*%df.matX)%*%(t(df.matX)%*%d.mat)
    
    cond <- max(abs(theta - theta.prev)) > toler
    i <- i + 1
    if(i > maxit){warning("WARNING: Algorithm did not converge"); break} 
  }
  return(list("thetahat"= c(theta),   "x0" = x0, "Iter" = i))
}
# combined the two (global and local)  

Bravo_all <- function(z, d, x1, x2, tau, alpha = 0.25, beta0, theta0, 
                      h, hatGn, ktype, toler = 1e-6, maxit = 5000) {
  # beta0; initial values for the parameteric component
  # theta0: initial values for the nonparametric component 
  
  # Step I 
  grid <- sort(x2)
  n <- length(grid)
  thetahat0 <- matrix(0, nrow = n, ncol = dim(x2)[2] + 1)
  
  for (k in 1:n) {
    fit_local <- Bravo_local(z = z, d = d, x1 = x1, x2 = x2, tau = tau, 
                             beta = beta0, theta = theta0, h = h, x0 = grid[k],  hatGn = hatGn,  
                             ktype = ktype,  toler = toler, maxit = maxit)
    thetahat0[k,] <- fit_local$thetahat
  }
  # Step II
  fit_global <- Bravo_Global(z = z, d = d, x1 = x1, tau = tau, 
                             beta = beta0, theta  = as.matrix(thetahat0[,1]), 
                             hatGn = hatGn, toler = toler, maxit = maxit)
  beta_hat <- as.vector(fit_global$beta_hat)
  Iter_global <- fit_global$Iter
  
  # Step III
  thetahat <- Iter_local <- as.null(n)
  theta0 <- apply(thetahat0, 2, mean, na.rm=TRUE)
  for (k in 1:n) {
    fit_local <- Bravo_local(z = z, d = d, x1 = x1, x2 = x2, tau = tau, 
                             beta = beta_hat, theta = theta0, h = h, x0 = grid[k],   
                             hatGn = hatGn, ktype = ktype,  toler = toler, maxit = maxit)
    thetahat[k] <- fit_local$thetahat[1]
    Iter_local[k] <- fit_local$Iter
  }
  return(list("beta_hat" = beta_hat, "thetahat"= thetahat,
              "Iter_global"= Iter_global, "Iter_local" = Iter_local))
}

# Cross-validation for Bandwidth selection for SPQR/Bravo
cv_bravo <- function(data, tau,  alpha = 0.25, beta1,
                     beta0, theta0, ncv, nbw, ktype){
  # beta1: true parameters value
  dftrain <- data[sample(nrow(data)),]
  folds <- cut(seq(1,nrow(data)), breaks = ncv, labels = FALSE)
  WAQRL_cv <- matrix(0, nrow = ncv, ncol = nbw)
  h_vector <- round(seq(0.15, 0.75, length.out = nbw), 3 )
  # Do the cross validation for each fold
  for(i in 1:ncv){
    # Segement the data by fold using the which() function 
    test_indexes <- which(folds == i, arr.ind = TRUE)
    testdata <- dftrain[test_indexes, ]
    traindata <- dftrain[-test_indexes, ]
    traindata <- traindata[order(traindata$y),]
    # final data
    x1 <- cbind(traindata$x11, traindata$x12)
    x2 <- as.matrix(traindata$x2)
    y <- as.matrix(traindata$y)
    d <- as.matrix(traindata$d)  
    n <- dim(y)[1]
    # estimate Gn
    WKM = ipcw(Hist(y,d)~1, data = traindata, method="marginal",
               times = sort(unique(traindata$y)),
               subjectTimes = traindata$y, subjectTimesLag  =0)$IPCW.subjectTimes
    hatGn <- as.matrix(case_when(WKM == 0 ~ 1/(2*n), TRUE ~ WKM))
    # true values 
    q_eps <- qgad_La(p = tau, eta = 0, phi = 1, alpha = alpha)
    qtrue <- x1%*%as.matrix(beta1)  + exp(sin(2*pi*x2) - 1.5)*q_eps
    WAQRL_h <- sapply(1:nbw, function(j){
      cv.fit <-  Bravo_all(z = y, d = d, x1 = x1, x2 = x2, tau = tau, alpha = alpha, 
                           beta0 = beta0,  theta0 = theta0, 
                           hatGn = hatGn, h = h_vector[j], ktype = ktype,  toler = 1e-6, maxit = 5000)
      qhat <- x1%*%as.matrix(c(beta1[1], cv.fit$beta_hat[2])) + as.matrix(cv.fit$thetahat)
      mean((d/hatGn)*check(qtrue - qhat, tau = tau),na.rm=T)
    })
    WAQRL_cv[i,] <- WAQRL_h
  }
  WAQRL <- apply(WAQRL_cv, 2, mean, na.rm = TRUE)
  cv <- as.data.frame(cbind(h_vector, WAQRL))
  h_cv <- cv$h_vector[which.min(cv$WAQRL)]
  return(list("h_cv" = h_cv, "cv" = cv))
}

# Approximating E(log(|eps|)) and q(log(|eps|))
Eq <- function(n, tau){
  set.seed(20220701)
  eps <- rtpa(n=n, eta=0, phi = 1, alpha = 0.25)
  E  <- log(abs(eps))
  q <- as.numeric(quantile(abs(eps), prob=tau))
  return(list(E = mean(E), q = log(q)))
}

#------------------------------------------------------------------------#
# Start the simulation 
#------------------------------------------------------------------------#
do_sim <- function(n, beta1, tau, alpha, theta_c, ncv, nbw, ktype = "ep"){
  # generate the data
  sv.data <- PII_MI_data(n, beta1 = beta1, tau = tau, alpha = alpha, theta_c)
  # final data
  sv.data <- sv.data[order(sv.data$y),]
  x1 <- cbind(sv.data$x11, sv.data$x12)
  x2 <- as.matrix(sv.data$x2)
  x <- cbind(x1, x2)
  y <- as.matrix(sv.data$y)
  d <- as.matrix(sv.data$d)
  ST <- as.matrix(sv.data$ST)
  # Estimate Gnhat
  WKM = ipcw(Hist(y,d)~1,
             data = sv.data,
             method="marginal",
             times = sort(unique(sv.data$y)),
             subjectTimes = sv.data$y, subjectTimesLag = 0)$IPCW.subjectTimes
  hatGn <- as.matrix(case_when(WKM == 0 ~ 1/(2*n), TRUE ~ WKM))
  #-------------------------------------------------------------
  # fit the nonparametric:  local linear quantile #
  #-------------------------------------------------------------
  # Method I
  loc_fit <- locfit.censor(x = x1, y = y, cens = 1-d,  km = "T", kern = "epan", kt = "prod")
  mhat_I <- fitted(loc_fit, data = NULL, what = "coef", type = "fit")
  res <- residuals(loc_fit)
  #estimate the scale 
  scale_fit <- locfit.censor(x=x2, log(abs(res)), cens = 1-d,  km="T", kern ="epan")
  logscalehat_I <- fitted(scale_fit, data = NULL, what = "coef", type = "fit")
  #Method II: similar to method I for mhat but nonparametric qr for scale
  loc_fit <- locfit.censor(x = x1, y=y, cens = 1-d,  km="T", kern ="epan", kt = "prod")
  mhat_II <- fitted(loc_fit, data = NULL, what = "coef", type = "fit")
  res <- residuals(loc_fit)
  h_res <- thumbBw(x2,log(abs(res)), deg = 1, weig = d/hatGn, kernel = EpaK)
  scale_fit <- llqr_nq(x = x2, z = log(abs(res)), d= d, h = h_res, tau = tau,
                       hatGn = hatGn, ktype = ktype)
  logscalehat_II <- scale_fit$fv
  # Method III: estimate quantiles directly 
  b0 <- lm(y~x-1, weights = d/hatGn)$coefficients
  h_mean <- thumbBw(x%*%as.vector(b0),y, deg = 1, weig = d/hatGn, kernel = EpaK)
  h_np <- h_mean*(tau*(1 - tau)/(dnorm(qnorm(tau)))^2)^(1/(2+3))
  fit_np <-  llqr_nq(x = x, z = y, d = d, h = h_np, tau =  tau, 
                     hatGn = hatGn, ktype = ktype)
  #-------------------------------------------------------------
  # fit the new method #
  #-------------------------------------------------------------
  cv_n <- try(cv_tpa(data = sv.data, beta1 = beta1, tau = tau, alpha = alpha, 
                     ncv = ncv, nbw = nbw, ktype = ktype)$h_cv, silent = TRUE)
  if(class(cv_n)=="try-error"){h_new = thumbBw(x2, y, deg = 1, weig = d/hatGn, kernel = EpaK)} else {h_new = cv_n}
  fit_new <- partial.fit(y = y, d = d, x1 = x1, x2 = x2, alpha = alpha,
                         h = h_new, x0 = sort(x2), ktype = ktype)
  #-------------------------------------------------------------
  # fit the Bravo (2020) method #
  #-------------------------------------------------------------
  # starting values
  beta0 <- c(fit_new$beta1_hat);
  theta0 <- c(mean(fit_new$phihat), mean(fit_new$beta2_hat[,2]))
  cv_b <- try(cv_bravo(data = sv.data, tau = tau, alpha = alpha,
                       beta1 = beta1,  beta0 = beta0, theta = theta0, 
                       ncv = ncv, nbw = nbw, ktype = ktype)$h_cv, silent = TRUE)
  if(class(cv_b)=="try-error"){h_bravo = thumbBw(x2, y, deg = 1, weig = d/hatGn, kernel = EpaK)} else {h_bravo = cv_b}
  fit_bravo <- Bravo_all(z = y, d = d, x1 = x1, x2 = as.matrix(sort(x2)), tau = tau, alpha = alpha, 
                         beta0 = beta0, theta0 = theta0, hatGn = hatGn, h = h_bravo,
                         ktype = ktype,  toler = 1e-6, maxit = 5000)  
  
  #-------------------------------------------------------------
  # fit single index model SIQR
  #-------------------------------------------------------------
  #get initial values 
  in_beta <- c(fit_new$beta1_hat[2], mean(fit_new$phihat))
  x <- x # taking all covariates 
  # estimate the multivariate local linear conditional quantile
  hp <- sd(c(1, in_beta)%*%t(x))*n^(-1/5)*4 # singular matrix if we remove 4
  fit_cd <- llrq_cd(x = x, z = y, d = d, h = hp, tau = tau,  hatGn = hatGn, ktype = ktype)
  hatQ_LL <- fit_cd$fv
  #run the SIQR
  weights <- d/hatGn
  newy <- weights*y
  h2 <- dpill(x, newy)
  #h2 = bw.nrd0(x)
  fit_SIQR <- nlrq(newy~(weights)*hatQ_NW_beta1(x, hatQ_LL, tau = tau, beta1, h = h2, ktype = ktype), 
                   tau = tau, start = list(beta1 = in_beta), trace = F)
  # the final beta 
  newbeta = as.numeric(summary(fit_SIQR)$coefficients[,1])
  newbeta = case_when(newbeta < 0 ~ -newbeta, TRUE ~ newbeta)
  ## estimate the conditional quantiles: final estimate
  #index_NW = c(c(1, newbeta)%*%t(x))
  index_NW = c(c(1, newbeta)%*%t(x))
  
  hm_NW1 <- dpill(index_NW, y); 
  hm_NW2 <-   thumbBw(index_NW,ST, deg = 1, weig = d/hatGn, kernel = EpaK)
  h3_NW <- hm_NW1*(tau*(1 - tau)/(dnorm(qnorm(tau)))^2)^.2
  h3_NW2 <- hm_NW2*(tau*(1 - tau)/(dnorm(qnorm(tau)))^2)^.2
  
  finalhatQ_NW1 <-  try(sapply(1:n, function (k){
    fit_qhat = lprq0(x = index_NW, y = y ,d=d, hatGn = hatGn, h = h3_NW, 
                     tau = tau, x0 = index_NW[k], ktype = ktype)
    qhat = as.numeric(fit_qhat$fv) }), silent = TRUE)
  if(class(finalhatQ_NW1)=="try-error"){
    h3_NW <- h3_NW2
    finalhatQ_NW <-  sapply(1:n, function (k){
      fit_qhat = lprq0(x = index_NW, y = y ,d=d, hatGn = hatGn, h = h3_NW, 
                       tau = tau, x0 = index_NW[k], ktype = ktype)
      qhat = as.numeric(fit_qhat$fv) })}  else{finalhatQ_NW <- finalhatQ_NW1}
  # estimate the effect of X2
  #-------------------------------------------------------------
  # Saving Estimates for all methods #
  #-------------------------------------------------------------
  # saving estimates 
  time <- c(y)
  status <- c(d)
  x0 <- sort(x2)
  x11 <- x1[,1]; x12 <- x1[,2]; x2 <- x2
  h_cv <- c(h_new, h_bravo, h3_NW)
  betahat_new <- fit_new$beta1_hat
  betahat_bravo <- fit_bravo$beta_hat
  betahat_SIQR <- newbeta
  
  q_eps <- qtpa(tau = tau, eta = 0, phi = 1, alpha = alpha)
  E_q <- Eq(n=10000, tau=tau)
  
  phihat_new <- fit_new$phihat
  nonpar_new <- as.matrix(phihat_new)*q_eps
  nonpar_bravo <- as.matrix(fit_bravo$thetahat)
  
  par_new <- x1%*%c(1, betahat_new[2])
  par_bravo <- x1%*%c(1, betahat_bravo[2])
  
  qhat_np_I <- as.matrix(mhat_I + exp(logscalehat_I - E_q$E)*q_eps) 
  qhat_np_II <- as.matrix(mhat_II + exp(logscalehat_II - E_q$q)*q_eps) 
  qhat_np_III <- as.matrix(fit_np$fv)
  qhat_new <- par_new + nonpar_new
  qhat_bravo <- par_bravo + nonpar_bravo
  qhat_SIQR <- as.matrix(finalhatQ_NW)
  # true values 
  phi <- exp(sin(2*pi*x2) - 1.5)
  nonpar <- phi*q_eps 
  qtrue <- x1%*%as.vector(beta1) + nonpar
  #-------------------------------------------------------------
  # performance measures for all methods #
  #-------------------------------------------------------------
  # performance measures 
  Bias_new <- betahat_new[2] - beta1[2]
  Bias_bravo <- betahat_bravo[2] - beta1[2]
  Bias_SIQR <- betahat_SIQR[1] - beta1[2] 
  Bias <- c(Bias_new, Bias_bravo, Bias_SIQR)
  
  MSE_new <-  (betahat_new[2] - beta1[2])^2
  MSE_bravo <- (betahat_bravo[2]- beta1[2])^2
  MSE_SIQR <- (betahat_SIQR[1] - beta1[2])^2
  MSE <- c(MSE_new, MSE_bravo, MSE_SIQR)
  # phihat
  ISE_new <- mean((phihat_new - phi)^2, na.rm = T)
  ISE_bravo <- mean((nonpar_bravo - phi*q_eps)^2, na.rm = T)

  # Weighted approximate quantile residaul loss (WAQRL)
  WAQRL_np_I <- mean((d/hatGn)*check(qtrue - qhat_np_I, tau = tau), na.rm =T)
  WAQRL_np_II <- mean((d/hatGn)*check(qtrue - qhat_np_II, tau = tau), na.rm =T)
  WAQRL_np_III <- mean((d/hatGn)*check(qtrue - qhat_np_III, tau = tau), na.rm =T)
  WAQRL_new <-  mean((d/hatGn)*check(qtrue - qhat_new, tau = tau), na.rm =T)
  WAQRL_bravo <- mean((d/hatGn)*check(qtrue - qhat_bravo, tau = tau), na.rm =T)
  WAQRL_SIQR <-  mean((d/hatGn)*check(qtrue - qhat_SIQR, tau), na.rm =T)
  WAQRL <- cbind(WAQRL_new, WAQRL_bravo, WAQRL_SIQR,  WAQRL_np_I, WAQRL_np_II,  WAQRL_np_III)
  # return results
  
  return(list("x0" = x0,   "h_cv" = h_cv, "betahat_new" = betahat_new,
              "betahat_bravo" = betahat_bravo, "betahat_SIQR" = betahat_SIQR,
              "phihat_new" = phihat_new, "thetahat_bravo" = nonpar_bravo, 
              "Bias_all" = Bias,  "MSE_all" = MSE, 
              "ISE_new" = ISE_new, "ISE_bravo" = ISE_bravo, "WAQRL_all" = WAQRL))
}

# Note that the simulation has been done using HPC computer 
#----------------------------------------------------------
# parallel computation 
#----------------------------------------------------------
# library(foreach)
# library(doParallel)
# library(parallel)

# cl <- makeCluster(6)
# registerDoParallel(cl)
# 
# # 
# n = 300
# nsim = 6# number of simulated samples
# beta1 = c(1, 2)
# alpha = 0.25
# theta_c = 3.5
# ncv = 5 # 5-fold cross validation 
# nbw = 10 # grid values of bandwidth parameter 
# tau = 0.1
# ktype = "ep"
# #
# test.sim <- foreach(i=1:nsim, .errorhandling ="pass",
#                        .packages = c("dplyr","locpol", "nloptr","quantreg", "pec", "locfit",
#                                      "rqPen","gamlss", "gamlss.cens","KernSmooth", "QBAsyDist"),
#                        .export = c("hatQ_NW_beta1")) %dopar% {
#                          set.seed(i)
#                          do_sim(n = n, beta1 = beta1, tau = tau, alpha = alpha, 
#                                 theta_c = theta_c, ncv = ncv, nbw = nbw, ktype = ktype)
#                        }
# stopCluster(cl)



