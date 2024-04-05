###################################################
# Thesis code
# Last updated: Mar 15

library(rpart)
library(spBayesSurv)
library(survival)
library(pec)
library(ggplot2)
library(tidyr)
library(dplyr)
library(MASS)
library(mvtnorm)
library(mice)
library(caret)
library(modelr)
library(ggplot2)
library(survival)
library(ROCR)
library(data.table)
library(SurvMetrics)
library(simsurv)
library(psych)
library(VIM)
library(mitools)
library(smcfcs)

#-------------------- Data generation----------------------#
Gendata <- function(N,p){
  #x  <- rnorm(N*p, 0, 1)
  mu.star <- (1:p)/2
  
  # standard deviations
  sd <- seq(1,2,0.125)   
  
  # Create a 9x9 correlation matrix with additional correlations
  C <- matrix(c(
    1.00, 0.10, 0.00, 0.00, 0.00, 0.00, 0.00, 0.20, 0.00,
    0.10, 1.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.30, 0.00,
    0.00, 0.00, 1.00, 0.30, 0.20, 0.00, 0.00, 0.00, 0.40,
    0.00, 0.00, 0.30, 1.00, 0.35, 0.00, 0.00, 0.00, 0.25,
    0.00, 0.00, 0.20, 0.35, 1.00, 0.00, 0.00, 0.00, 0.30,
    0.00, 0.00, 0.00, 0.00, 0.00, 1.00, 0.15, 0.00, 0.00,
    0.00, 0.00, 0.00, 0.00, 0.00, 0.15, 1.00, 0.20, 0.00,
    0.20, 0.30, 0.00, 0.00, 0.00, 0.00, 0.20, 1.00, 0.10,
    0.00, 0.00, 0.40, 0.25, 0.30, 0.00, 0.00, 0.10, 1.00
  ), nrow = 9)
  
  Sigma.star <- diag(sd)%*%C%*%diag(sd) 
  x = matrix(rnorm(N*p), nrow=N)%*%chol(Sigma.star) + matrix(rep(mu.star,N), 
                                                             nrow=N, byrow = TRUE)
  trt <- rbinom(N, 1, 0.5) 
  cov <- data.frame(matrix(c(x,trt),ncol=10,byrow = FALSE))
  pars = c(X1=0.2, X2= -0.4, X3= 1.3, X4= 0.1, X5= -1.5, 
           X6 = 0.15, X7 = 0.2, X8 = 0.23, X9 = -0.1, X10 = 0.5)
  
  RU <- runif(N)
  lambdat <- 0.005
  times <- -log(RU)/(lambdat*exp(as.matrix(cov) %*% as.matrix(pars)))
  censor <- -log(RU)/(lambdat)
  
  death <- as.numeric(times) <= censor
  os <- pmin(as.numeric(times), censor)
  sample.data <- data.frame(cov, os = os,death = death)
  sample.data <- round(sample.data,digits = 5)
  return(sample.data)
}

#------------------ Missingness generation-----------------#
generate_data_MCAR <- function(p.miss,data_all) {
  # generate patterns
  n = dim(data_all)[1]
  p = dim(data_all)[2]-2
  p.del = p/2
  patterns = runif(n*p.del)<p.miss
  # generate data
  data_all = data_all
  y=data_all[,c((p+1),(p+2))]
  X.complete.l1 <- data_all[,1:p.del]
  X.complete.l2 <- data_all[,(p.del+1):p]
  X.complete.l1 <- as.matrix(X.complete.l1)
  X.complete.l1[patterns] <- NA
  data.obs <- cbind(X.complete.l1,X.complete.l2,y)
  return(data.obs)
}

generate_data_MAR <- function(cols,data_all){
  n = dim(data_all)[1]
  p = dim(data_all)[2]-2
  X.complete <- as.matrix(data_all[,1:p])
  y=data_all[,(p+1):(p+2)]
  X.obs <- X.complete
  miss.b <- matrix(c(
    0.8,-1.2,0.3, 0.4, 0.2,
    -1.5,0.3, 1.8,-0.1,0.3,
    0.76,-0.99,-0.7,1.2,-0.1,
    -0.2,0.5, -0.2,0.4,0.2,
    -0.4,0.7,0.5,-0.2,-0.1,
    0,0,0,0,0,
    0,0,0,0,0,
    0,0,0,0,0,
    0,0,0,0,0,
    0,0,0,0,0
  ), nrow = 5, ncol = 10)
  for(i in cols){
    # linear combination 
    z <- cbind(X.complete[,c(6,7,8,9,10)]) %*% miss.b[,i] # change fixed coeff
    # pass through an exp function
    pr <- 1/(1+exp(z))
    # bernoulli response variable
    r <- rbinom(n,1,pr) # r=1 is missing
    X.obs[r==1,i] <- NA
  }
  cat('percentage of NA in columns', cols, ':', mean(is.na(X.obs[,1])),mean(is.na(X.obs[,2])),mean(is.na(X.obs[,3])),mean(is.na(X.obs[,4])),
      mean(is.na(X.obs[,5])),'\n')
  data.obs <- cbind(X.obs,y)
  return(data.obs)
}

generate_data_MNARX <- function(cols,data_all) {
  n = dim(data_all)[1]
  p = dim(data_all)[2]-2
  X.complete <- as.matrix(data_all[,1:p])
  y=data_all[,(p+1):(p+2)]
  miss.gamma = c(1,0.8,0.6,0.4,0.2)
  X.obs <- X.complete
  for(i in cols){
    # linear combination 
    z <- X.complete[,i] * miss.gamma[i] # fixed coeff
    # pass through an inv-logit function
    pr <- 1/(1+exp(1+z))     
    # bernoulli response variable
    r <- rbinom(n,1,pr) # r=1 is missing
    X.obs[r==1,i] <- NA
  }
  data.obs <- cbind(X.obs,y)
  cat('percentage of NA in columns', cols, ':', mean(is.na(X.obs[,1])),mean(is.na(X.obs[,2])),mean(is.na(X.obs[,3])),mean(is.na(X.obs[,4])),
      mean(is.na(X.obs[,5])),'\n')
  return(data.obs)
}

generate_data_MNARY <- function(cols,data_all) {
  n = dim(data_all)[1]
  p = dim(data_all)[2]-2
  X.complete <- as.matrix(data_all[,1:p])
  y=data_all[,(p+1):(p+2)]
  miss.gamma = 0.001
  X.obs <- X.complete
  for(i in cols){
    # linear combination 
    z <- y[,1] * miss.gamma # fixed coeff
    # pass through an inv-logit function
    pr <- 1/(1+exp(1+z))     
    # bernoulli response variable
    r <- rbinom(n,1,pr) # r=1 is missing
    X.obs[r==1,i] <- NA
  }
  data.obs <- cbind(X.obs,y)
  cat('percentage of NA in columns', cols, ':', mean(is.na(X.obs[,1])),mean(is.na(X.obs[,2])),mean(is.na(X.obs[,3])),mean(is.na(X.obs[,4])),
      mean(is.na(X.obs[,5])),'\n')
  return(data.obs)
}

generate_data_MARXY <- function(cols,data_all){
  n = dim(data_all)[1]
  p = dim(data_all)[2]-2
  X.complete <- as.matrix(data_all[,0:p+1])
  y=data_all[,(p+1):(p+2)]
  X.obs <- X.complete[,-11]
  miss.b <- matrix(c(
    0.8,-1.2,0.3, -0.4, 1.2,0.2,
    1.2,-0.3,-1.3,-0.1,0.3,0.2,
    0.4,-0.99,-0.7,1.2,-0.1,0.2,
    -0.5,-1.7, -0.2,0.4,0.2,0.2,
    0.4,-1.3,0.5,-0.2,-0.1,0.2,
    0,0,0,0,0,
    0,0,0,0,0,
    0,0,0,0,0,
    0,0,0,0,0,
    0,0,0,0,0,
    0,0,0,0,0
  ), nrow = 6, ncol = 10)
  for(i in cols){
    # linear combination 
    z <- cbind(X.complete[,c(6,7,8,9,10,11)]) %*% miss.b[,i] # change fixed coeff
    # pass through an exp function
    pr <- 1/(1+exp(z))
    # bernoulli response variable
    r <- rbinom(n,1,pr) # r=1 is missing
    X.obs[r==1,i] <- NA
  }
  cat('percentage of NA in columns', cols, ':', mean(is.na(X.obs[,1])),mean(is.na(X.obs[,2])),mean(is.na(X.obs[,3])),mean(is.na(X.obs[,4])),
      mean(is.na(X.obs[,5])),'\n')
  data.obs <- cbind(X.obs,y)
  return(data.obs)
}
#--------------------- Regression imputation---------------#
# regress X on Z

reg_Z <- function(data, i, iterations = 5) {
  name <- colnames(data[, 1:5])[[i]]
  imputed_values <- replicate(iterations, {
    # Separate the data into two data frames: one with missing X1 and one without
    model_data <- data %>%
      filter(!is.na(.[[name]])) %>% dplyr::select(X6:X10, all_of(name))
    
    model <- lm(as.formula(paste0(name, " ~ X6 + X7 + X8 + X9 + X10")), data = model_data)
    
    # Predict missing values in X1 using the fitted model
    predicted <- predict(model, newdata = data)
    # Replace missing values in the original data with the predicted value 
    ifelse(is.na(data[, i]), predicted, data[, i])
  })
  
  # Return the mean of imputed values
  return(rowMeans(imputed_values))
}

# regress X on Z, D and logT
reg_ZDlT <- function(data,i) {
  # Separate the data into two data frames: one with missing X1 and one without
  name = colnames(data[,1:5])[[i]]
  model <- lm(as.formula(paste0(name,"~","X6+X7+X8+X9+X10+log(os)+death")), data = data)
  
  # Predict missing values in X1 using the fitted model
  predicted <- predict(model, newdata = data)
  # Replace missing values in the original data with the predicted value 
  data.new<- ifelse(is.na(data[,i])==TRUE,predicted,data[,i])
  return(data.new)
}

## regress X on Z,D,T^2
reg_ZDT2 <- function(data,i) {
  # Separate the data into two data frames: one with missing X1 and one without
  name = colnames(data[,1:5])[[i]]
  model <- lm(as.formula(paste0(name,"~","X6+X7+X8+X9+X10+os^2+death")), data = data)
  
  # Predict missing values in X1 using the fitted model
  predicted <- predict(model, newdata = data)
  # Replace missing values in the original data with the predicted value 
  data.new<- ifelse(is.na(data[,i])==TRUE,predicted,data[,i])
  return(data.new)
}

## regress X on Z,D,T
reg_ZDT <- function(data,i) {
  # Separate the data into two data frames: one with missing X1 and one without
  name = colnames(data[,1:5])[[i]]
  model <- lm(as.formula(paste0(name,"~","X6+X7+X8+X9+X10+os+death")), data = data)
  
  # Predict missing values in X1 using the fitted model
  predicted <- predict(model, newdata = data)
  # Replace missing values in the original data with the predicted value 
  data.new<- ifelse(is.na(data[,i])==TRUE,predicted,data[,i])
  return(data.new)
}

## regress X on Z,D,H(T)
reg_ZDHT <- function(data,i) {
  # Separate the data into two data frames: one with missing X1 and one without
  name = colnames(data[,1:5])[[i]]
  data$naest = nelsonaalen(data, os, death)
  model <- lm(as.formula(paste0(name,"~","X6+X7+X8+X9+X10+naest+death")), data = data)
  
  # Predict missing values in X1 using the fitted model
  predicted <- predict(model, newdata = data)
  # Replace missing values in the original data with the predicted value 
  data.new<- ifelse(is.na(data[,i])==TRUE,predicted,data[,i])
  return(data.new)
}

## regress X on Z,D,H(T) and zxH(T)
reg_ZDZHT <- function(data,i) {
  # Separate the data into two data frames: one with missing X1 and one without
  name = colnames(data[,1:5])[[i]]
  data$naest = nelsonaalen(data, os, death)
  model <- lm(as.formula(paste0(name,"~","X6+X7+X8+X9+X10+naest+X6:naest+X7:naest+X8:naest+X8:naest+X10:naest+death")), data = data)
  
  # Predict missing values in X1 using the fitted model
  predicted <- predict(model, newdata = data)
  # Replace missing values in the original data with the predicted value 
  data.new<- ifelse(is.na(data[,i])==TRUE,predicted,data[,i])
  return(data.new)
}

## regress X on Z,D,and H0(T)
reg_ZDH0T <- function(data,i) {
  # Separate the data into two data frames: one with missing X1 and one without
  name = colnames(data[,1:5])[[i]]
  data$h0 <- basehaz(coxph(Surv(data$os,data$death)~1))[,1]
  model <- lm(as.formula(paste0(name,"~","X6+X7+X8+X9+X10+h0+death")), data = data)
  # Predict missing values in X1 using the fitted model
  predicted <- predict(model, newdata = data)
  # Replace missing values in the original data with the predicted value 
  data.new<- ifelse(is.na(data[,i])==TRUE,predicted,data[,i])
  return(data.new)
}


fn_c_index <-function(data.train,data.test){
  median_surv <- summary(survfit(Surv(data.test$os, data.test$death) ~ 1))[["table"]][["median"]]
  cox1 <- coxph(Surv(os,death)~ X1+X2+X3+X4+X5+X6+X7+X8+X9+X10, data=data.train,x=T,y=T)
  Brier <- brier(cox1,newdata = data.test, times = median_surv)
  data.test$lp <- predict(cox1, newdata = data.test)
  gval <- coxph(Surv(os, death) ~ lp, data = data.test)
  calslope_summary <- c(
    "calibration slope" = gval$coef,
    "2.5 %" = gval$coef - qnorm(0.975) * sqrt(gval$var),
    "97.5 %" = gval$coef + qnorm(0.975) * sqrt(gval$var)
  )
  # Calibration in the large
  p <- predict(cox1, newdata = data.test, type = "expected")
  pfit1 <- glm(death ~ offset(log(p)), 
               family = poisson, 
               data = data.test,
               subset = (p > 0))
  int_summary <- summary(pfit1)$coefficients[,1:2]
  
  return(c(cox1$concordance[6:7],calslope_summary,int_summary,Brier$rsquared,Brier$brier,median_surv))
}


#-------------------------------SIMULATION-------------------------------------#

set.seed(1)
Result_MAR <- vector(mode = "list", length = 5000)
for (k in 1:5000){
  cat("iteration",k)
  
  #Generate data
  repeat {
    sample.data <- Gendata(1000, 9)
    # Check if os variable has very similar values
    if (any(diff(sort(sample.data$os)) < 0.000001) || any(sample.data$os < 0.0001)) {
      cat("Similar values found in os. Regenerating data...\n")
      next  # Skip the rest of the loop and regenerate data
    } else {
      break  # No similar values found, continue with the loop
    }
  }
  death_KM = survfit(Surv(sample.data$os, sample.data$death) ~ 1)
  #median_surv <- summary(death_KM)[["table"]][["median"]]
  
  x <- nrow(sample.data) %>% runif() 
  orig <- transform(sample.data,sample=order(x)) %>% dplyr::arrange(sample) 
  data.PERFECT <- orig[1:(nrow(orig)*0.6),] %>% dplyr::select(c(-sample))
  data.test <- orig[((nrow(orig)*0.6)+1):nrow(orig),] %>% dplyr::select(c(-sample))
  
  data.MAR <- generate_data_MAR(c(1,2,3,4,5), data.PERFECT)
  #md.pattern(data.MAR)
  
  # Run regressions
  data.reg_z = NULL
  data.reg_zdlt = NULL
  data.reg_zdt = NULL
  data.reg_zdt2 = NULL
  data.reg_zdht = NULL
  data.reg_zdzht = NULL
  data.reg_zdh0t = NULL
  
  
  for (i in 1:5){
    # 1.
    reg1 = reg_Z(data.MAR,i)
    data.reg_z =cbind(data.reg_z,reg1)
    # 2.
    reg2 = reg_ZDlT(data.MAR,i)
    data.reg_zdlt =cbind(data.reg_zdlt,reg2)
    # # 3.
    reg3 = reg_ZDT(data.MAR,i)
    data.reg_zdt =cbind(data.reg_zdt,reg3)
    # # 4.
    reg4 = reg_ZDT2(data.MAR,i)
    data.reg_zdt2 =cbind(data.reg_zdt2,reg4)
    # # 5.
    reg5 = reg_ZDHT(data.MAR,i)
    data.reg_zdht =cbind(data.reg_zdht,reg5)
    # # 6.
    reg6 = reg_ZDZHT(data.MAR,i)
    data.reg_zdzht =cbind(data.reg_zdzht,reg6)
    # # 7.
    reg7 = reg_ZDH0T(data.MAR,i)
    data.reg_zdh0t =cbind(data.reg_zdh0t,reg7)
  }
  
  data.reg_z= cbind(data.reg_z, data.MAR[,6:12])
  data.reg_zdlt= cbind(data.reg_zdlt, data.MAR[,6:12])
  data.reg_zdt= cbind(data.reg_zdt, data.MAR[,6:12])
  data.reg_zdt2= cbind(data.reg_zdt2, data.MAR[,6:12])
  data.reg_zdht= cbind(data.reg_zdht, data.MAR[,6:12])
  data.reg_zdzht= cbind(data.reg_zdzht, data.MAR[,6:12])
  data.reg_zdh0t= cbind(data.reg_zdh0t,data.MAR[,6:12])
  
  # Generate cc datasets
  data.cc <- tidyr::drop_na(data.MAR)
  
  # Multiple imputation
  miceMod1 <- mice(data.MAR, method='norm',m=5)
  data.MAR.mice <- complete(miceMod1,action="long")
  final_dataset_X <- split(data.MAR.mice[3:7], rep(1:5, each = 600))
  data.mice <- cbind(Reduce(function(x, y) x + y, final_dataset_X) / length(final_dataset_X),data.MAR[-(1:5)])
  
  #smcfcs # specifies a substansive model
  imps <- smcfcs(data.MAR, smtype="coxph", smformula="Surv(os,death)~X1+X2+X3+X4+X5+X6+X7+X8+X9+X10",
                 method=c("norm","norm","norm","norm","norm","","","","","","",""))
  data.smcfcs <- data.frame(matrix(nrow=600, ncol=12))
  improj <- imputationList(imps$impDatasets)
  names(data.smcfcs) <- names(improj$imputations[[1]])
  for (row in 1:600) {
    for (col in 1:12) {
      avg_value <- mean(sapply(improj$imputations, function(dataset) dataset[row, col]))
      data.smcfcs[row, col] <- avg_value
    }
  }
  data.smcfcs$X10 <- ifelse(data.smcfcs$X10>0.5,1,0)
  
  
  namelist <- list(data.PERFECT,data.cc,data.mice,data.smcfcs,data.reg_z,data.reg_zdlt,data.reg_zdt,data.reg_zdt2,data.reg_zdht,data.reg_zdzht,data.reg_zdh0t)
  
  metric_df <- NULL
  for (j in namelist){
    colnames(j)[1:5] <- c("X1","X2","X3","X4","X5")
    metric<- fn_c_index(j, data.test)
    metric_df <- rbind(metric_df, metric)
  }
  rownames(metric_df) <- c("PERFECT","cc","mice","smcfcs","NO-T","LOG-T","T","T^2","NA","NA-INT","COX")
  colnames(metric_df) <- c("C-index","C-sd","Cali slope","slope_2.5","slope_97.5","CITL","CITL.sd","R^2","Brier","median")
  Result_MAR[[k]] <- as.data.frame(metric_df)
}

saveRDS(Result_MAR,file = "Result_MAR")