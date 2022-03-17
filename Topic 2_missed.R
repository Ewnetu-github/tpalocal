# libraries 
library(truncnorm)  
library(nloptr)
library(rgr)# for logit function
library(rqPen) 
library(gamlss)
library(gamlss.cens)
library(KernSmooth)
library(GoFKernel)
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
# Standard Laplace
f0_La <- function(s){0.5*exp(-abs(s))} 
F0_La <- function(s){0.5+0.5*sign(s)*(1-exp(-abs(s)))} 
QF_La <- function(tau){-sign(tau-0.5)*log(1-2*abs(tau-0.5))}
S0_La <- function(s){ifelse(s<0, 1-0.5*exp(s), 0.5*exp(-s))}
# Link function
glog      <-function(s){log(s)}
glog.inv  <-function(s){exp(s)}
glogit    <-function(s){log(exp(s)-1)}
glogit.inv<-function(s){log(exp(s)+1)}
# density
dtpa <-function(y, eta = 1, phi = 1, alpha = 0.5, f0, g)
{
  g.prime <- Deriv::Deriv(g, "s")
  coeff <- 2*alpha*(1-alpha)*g.prime(y)/phi
  den <-   ifelse(y < eta,(coeff*f0((1-alpha)*(g(eta)-g(y))/phi)),
                  (coeff*f0(alpha*(g(y)-g(eta))/phi)))
  return(den=den)
}
# CDF/Survival 
ptpa <- function(y, eta=1, phi=1, alpha=0.5,
                 F0, g, lower.tail = TRUE) {
  p <- ifelse(y < eta, (2*alpha*F0((1 - alpha)*(g(y) - g(eta))/phi)),
              (2*alpha - 1 + 2*(1 - alpha)*F0(alpha*(g(y) - g(eta))/phi)))
  ifelse(test = lower.tail == TRUE, yes = return(p), no = return(1-p))
}
# quantile function 
qtpa <- function(tau, eta=1, phi=1, alpha = 0.5, 
                 F0, g, g.inv, QF = NULL){
  if (is.null(QF)){
    QF <- GoFKernel::inverse(F0, lower =0, upper = Inf)
  }
  #g.inv <- GoFKernel::inverse(g,lower,upper)
  
  q<-ifelse(tau< alpha, g.inv(g(eta) + (phi/(1-alpha))*QF(tau/(2*alpha))),
            g.inv(g(eta) + (phi/alpha)*QF((1+tau-2*alpha)/(2*(1-alpha)))))
  return(q=q)
}

# Random number generation
rtpa<- function(n,eta=1,phi=1,alpha=0.5, F0, QF=NULL, g, g.inv){
  u <- runif(n, min = 0, max = 1)
  if (is.null(QF)){
    QF <- GoFKernel::inverse(F0, lower =0, upper = Inf)
  }
  #g.inv <- GoFKernel::inverse(g,lower = 0,upper = Inf)
  r <- ifelse(u< alpha, g.inv(g(eta)+(phi/(1-alpha))*QF(u/(2*alpha))),
              g.inv(g(eta)+(phi/alpha)*QF((1+u-2*alpha)/(2*(1-alpha)))))
  return(r=r)
}
#------------------------------------------------------------------------#
# Model 1
Model <- function(x){
  beta1 <- x + 2*exp(-16*x^2)
  beta2 <- sin(2*x) - 3
  beta3 <- x^2 - sin(x) - 2*x
  return(list(beta1 = beta1, beta2 = beta2, beta3 = beta3))
}

# # Model 2
# Model <- function(x){
#   beta1 <- x + sin(2*x)+2*exp(-16*x^2)
#   beta2<- -x-1.5
#   beta3<- sin(pi*x)+x^2
#   return(list(beta1 = beta1, beta2 = beta2, beta3 = beta3))
# }
#-----------------------------------------------------------------------#
# Data generation
# the data is generated  from TPA Laplace with logit-type link function
#-----------------------------------------------------------------------#
tpa_data <- function(n, theta_c, F0 = F0_La, QF = QF_La, 
                     g = glogit, g.inv = glogit.inv)
{
  x <-  rtruncnorm(n, a = 0, b = 2, mean =  0, sd = 2)
  eta <- glogit.inv(Model(x)$beta1) 
  phi <- exp(Model(x)$beta2)
  alpha <- expit(Model(x)$beta3)
  ST <- suppressWarnings(rtpa(n=n, eta=eta, phi=phi, alpha=alpha,
                              F0=F0, QF = QF, g =g, g.inv = g.inv))
  CT <-  sapply(1:n, function(i) rexp(1,theta_c*x[i]))
  y <- pmin(ST,CT)
  d <- as.numeric(ST <= CT)
  dat <- data.frame(x,y,d,ST,CT)
  return(dat)
}
# n <- 100
# set.seed(1235)
# test.data <- tpa_data(n=n, theta_c = .40)
# y <- test.data$y
# x<- test.data$x
# d<- test.data$d
# sum(d==0)/n
# 
# boxplot(test.data$y)


# local likelihood 
local_nll <- function(beta,  y, d, x,  ker.w = NULL) {
  y <- as.matrix(y)
  d <- as.matrix(d)
  x <- as.matrix(x)
  p <- dim(x)[2] # no.covariates 
  p1 = 1  #local linear 
  eta  <- glog.inv(x%*%as.vector(beta[1:(p1+1)]))
  phi  <- exp(x%*%as.vector(beta[(p1+2):(p1+3)]))
  alpha<- expit(x%*%as.vector(beta[(p1+4):(p1+5)]))# expit is Inverse-logit transformation
  # local log-likelihood function 
  if(is.null(ker.w)){
    logL <- (d*log(dtpa(y, eta, phi, alpha, f0_ALa, glog)) + 
               (1-d)*log(ptpa(y, eta, phi, alpha, F0_ALa, glog, lower.tail = FALSE)))
  } else { logL <- (d*log(dtpa(y, eta, phi, alpha, f0_ALa, glog)) + 
                      (1-d)*log(ptpa(y, eta, phi, alpha, F0_ALa, glog, lower.tail = FALSE)))*ker.w
  }
  return(-sum(logL[!is.infinite(logL)]))
}

#---------------------------------------------------------------------------------------
#                           Estimation                               
#---------------------------------------------------------------------------------------
# Analysis has been done by TPA Laplace with log-link function
# init: initial values 
# tau: order of quantiles 
# x: vector of covariate
# y: vector of observed time  
# d: vector of censoring status 
# h: bandwidth parameter
# m: number of grid points of x0 
# m=n in this simulation 
# ktype: type of kernel function 
#---------------------------------------------------------------------------------------
local.fit <- function(init, tau,  x,  y, d,  h, m, ktype) 
{  
  n <- length(y)
  x <- as.matrix(x)
  p <- dim(x)[2]
  
  etahat <- phihat <- alphahat <- matrix(0, nrow = m, ncol = length(h))
  qhat1 <- qhat2 <- qhat3 <- matrix(0, nrow = m, ncol = length(h))
  for (j in 1:length(h)) {
    #x0 <- seq(min(x)+0.025*h[j], max(x)-0.025*h[j], length = m)
    x0 <- sort(c(x))
    for(i in 1:m){
      newx = matrix(0,n,p)
      newx = x - t(matrix(rep(x0[i],p*n),p,n))
      ker.h <- apply(newx/h[j], MARGIN = 2, FUN = ker, ktype = ktype)

      opts <- list("algorithm"="NLOPT_LN_NELDERMEAD","xtol_rel"=1.0e-7)
      fit <-  nloptr(x0 = init, eval_f = local_nll, opts = opts, 
                     y = y, d = d,  x = cbind(1, newx), ker.w = ker.h,
                     lb = rep(-Inf, length(init)), ub = rep(Inf, length(init)))
      etahat[i,j] <- glog.inv(fit$solution[1])
      phihat[i,j] <- exp(fit$solution[3])
      alphahat[i,j] <- expit(fit$solution[5])
      qhat1[i,j] <- qtpa(tau = tau[1], eta =  etahat[i,j], phi = phihat[i,j], alpha = alphahat[i,j], 
                         F0 = F0_La, g = glog, g.inv = glog.inv, QF = QF_La)
      qhat2[i,j] <- qtpa(tau = tau[2], eta =  etahat[i,j], phi = phihat[i,j], alpha = alphahat[i,j], 
                         F0 = F0_La, g = glog, g.inv = glog.inv, QF = QF_La)
      qhat3[i,j] <- qtpa(tau = tau[3], eta =  etahat[i,j], phi = phihat[i,j], alpha = alphahat[i,j], 
                         F0 = F0_La, g = glog, g.inv = glog.inv, QF = QF_La)
    }
  }
  return(list(x0 = x0, etahat = etahat, phihat = phihat, alphahat = alphahat, 
              qhat1 = qhat1, qhat2 = qhat2, qhat3 = qhat3))
}
#---------------------------------------------------------------------------------------
# start the simulation analysis
do_sim <- function(tau, n, theta_c, h, m, ktype){
  sim_data <- tpa_data(n=n, theta_c = theta_c)
  sim_data <- sim_data[order(sim_data$y),]
  x <- sim_data$x
  y <- sim_data$y
  d <- sim_data$d
  
  in_fit <- suppressWarnings(gamlss(Surv(log(y), d) ~x,
                                    sigma.formula = ~x, nu.formula = ~x,   nu.start = 1,  
                                    family = cens(PE2), trace = FALSE))
  int_beta1 <- as.numeric(in_fit$mu.coefficients)
  int_beta2 <- as.numeric(in_fit$sigma.coefficients)
  int_beta3 <- as.numeric(in_fit$nu.coefficients)
  
  init0 <- c(int_beta1, int_beta2,  int_beta3)
  
  opts <- list("algorithm"="NLOPT_LN_NELDERMEAD","xtol_rel"=1.0e-8)
  
  fit.full <- nloptr(x0 = init0, eval_f = local_nll, opts = opts,
                     y = y, d = d,  x = cbind(1,x),  ker.w = NULL,
                     lb = rep(-Inf, length(init0)), ub = rep(Inf, length(init0)))
  init <- fit.full$solution
  
  fit <- try(local.fit(tau = tau,  x = x, y = y, d = d,
                       init = init, h = h, m = m,  ktype = ktype), silent = TRUE)
  if(class(fit)=="try-error"){
    fit2 <- local.fit(tau = tau,  x = x, y = y, d = d,
                      init = init0, h = h, m = m,  ktype = ktype)
    fit = fit2
  }
  
  # true values
  eta <- glogit.inv(Model(fit$x0)$beta1)
  phi <- exp(Model(fit$x0)$beta2)
  alpha <- expit(Model(fit$x0)$beta3)
  # quantiles 
  q1_true <- suppressWarnings(qtpa(tau = tau[1], eta = eta, phi = phi, alpha = alpha, 
                                   F0 = F0_La, g = glogit, g.inv = glogit.inv, QF = QF_La))
  q2_true <- suppressWarnings(qtpa(tau = tau[2], eta = eta, phi = phi, alpha = alpha, 
                                   F0 = F0_La, g = glogit, g.inv = glogit.inv, QF = QF_La))
  q3_true <- suppressWarnings(qtpa(tau = tau[3], eta = eta, phi = phi, alpha = alpha, 
                                   F0 = F0_La, g = glogit, g.inv = glogit.inv, QF = QF_La))
  qtrue <- cbind(q1_true, q2_true, q3_true)  
  # approximate Integrate squared error  
  ISE_eta <-  sapply(1:length(h), function(i) (fit$etahat[,i] -eta)^2)
  ISE_phi <-  sapply(1:length(h), function(i) (fit$phihat[,i] -phi)^2)
  ISE_alpha <- sapply(1:length(h), function(i) (fit$alphahat[,i] - alpha)^2)
  
  AISE_eta <- apply(ISE_eta, 2, sum)*diff(range(fit$x0))/(m)
  AISE_phi <- apply(ISE_phi, 2, sum)*diff(range(fit$x0))/(m)
  AISE_alpha <- apply(ISE_alpha, 2, sum)*diff(range(fit$x0))/(m)
  AISE <- rbind(AISE_eta, AISE_phi, AISE_alpha)
  #Quantile loss 
  loss1 <- sapply(1:length(h), function(i) d*check(fit$qhat1[,i] - q1_true, tau = tau[1]))
  loss2 <- sapply(1:length(h), function(i) d*check(fit$qhat2[,i] - q2_true, tau = tau[2]))
  loss3 <- sapply(1:length(h), function(i) d*check(fit$qhat3[,i] - q3_true, tau = tau[3]))
  AQRL1 <- apply(loss1, 2, sum, na.rm=T)*diff(range(fit$x0))/(m)
  AQRL2 <- apply(loss2, 2, sum, na.rm=T)*diff(range(fit$x0))/(m)
  AQRL3 <- apply(loss3, 2, sum, na.rm=T)*diff(range(fit$x0))/(m)
  AQRL <- rbind(AQRL1, AQRL2, AQRL3)
  
  return(list("etahat" = fit$etahat, "phihat"= fit$phihat, "alphahat" = fit$alphahat,
              "qhat1" = fit$qhat1, "qhat2" = fit$qhat2,"qhat3" = fit$qhat3,
              "theta"  = cbind(eta, phi, alpha), "qtrue" = qtrue, 
              "AISE_all" = AISE, "AQRL_all" = AQRL))
}

# set.seed(234245)
# test.sim <-  do_sim(tau = c(0.25, 0.5, 0.75), n = 100,
#                     theta_c = 0.17, h = c(0.25, 0.35),  m = 10, ktype = "ep")
# 



