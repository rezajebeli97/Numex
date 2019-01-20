;; PL Project - Fall 2018
;; NUMEX interpreter

#lang racket
(provide (all-defined-out)) ;; so we can put tests in a second file

;; definition of structures for NUMEX programs

;; CHANGE add the missing ones
(struct var  (string)    #:transparent)
(struct num  (num)    #:transparent)  ;; a constant number, e.g., (num 17)
(struct bool  (b)    #:transparent)  ;; a constant boolean, e.g., (boolean #f)
(struct munit ()      #:transparent) ;; unit value -- good for ending a list

(struct plus  (e1 e2)  #:transparent)  ;; add two expressions
(struct mult (e1 e2)  #:transparent)  ;; multiply two expressions
(struct neg  (e)    #:transparent)

(struct orelse (e1 e2) #:transparent)
(struct andalso (e1 e2) #:transparent)
(struct cnd (e1 e2 e3) #:transparent)

(struct iseq (e1 e2)    #:transparent)
(struct ifnzero (e1 e2 e3)    #:transparent)
(struct ifleq (e1 e2 e3 e4)    #:transparent)
(struct ismunit (e)     #:transparent) ;; if e1 is unit then 1 else 0

(struct with (s e1 e2)    #:transparent)

(struct apair (e1 e2) #:transparent)
(struct 1st (e1) #:transparent)
(struct 2nd (e1) #:transparent)

(struct lam  (s1 s2 e) #:transparent) ;; a recursive(?) 1-argument function
(struct apply (funexp actual)       #:transparent) ;; function call
(struct closure (env fun) #:transparent) ;; a closure is not in "source" programs; it is what functions evaluate to
;; Problem 1

(define (racketlist->numexlist xs)
  (cond [(null? xs) (munit)]
        [(list? xs) (apair (car xs) (racketlist->numexlist (cdr xs)))]
        [true (error "Not a Racket list")]
    )
 )
(define (numexlist->racketlist xs)
  (cond [(munit? xs) null]
        [(apair? xs) (cons (apair-e1 xs) (numexlist->racketlist (apair-e2 xs)))]
        [true (error "Not a Numex list")]         
    )
)

;; Problem 2

;; lookup a variable in an environment
;; Complete this function
(define (envlookup env str)
  (cond [(null? env) (error "unbound variable during evaluation" str)])
  (cond [(equal? str (car (car env))) (cdr (car env))]
        [else (envlookup (cdr env) str)]
  )
)

;; Complete more cases for other kinds of NUMEX expressions.
;; We will test eval-under-env by calling it directly even though
;; "in real life" it would be a helper function of eval-exp.
(define (eval-under-env e env)
  (cond [(var? e) (envlookup env (var-string e))]
        [(num? e)
         (cond [(integer? (num-num e)) e]
               [else (error "NUMEX num applied to non racket integer")])]
        [(bool? e)
         (cond [(boolean? (bool-b e)) e]
               [else (error "NUMEX bool applied to non racket integer")])]
        [(munit? e) e]
        [(plus? e)
         (let ([v1 (eval-under-env (plus-e1 e) env)]
               [v2 (eval-under-env (plus-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (+ (num-num v1)
                       (num-num v2)))
               (error "NUMEX addition applied to non-number")))]
        [(mult? e)
         (let ([v1 (eval-under-env (mult-e1 e) env)]
               [v2 (eval-under-env (mult-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (* (num-num v1)
                       (num-num v2)))
               (error "NUMEX multiplication applied to non-number")))]
        [(neg? e)
         (let ([v (eval-under-env (neg-e e) env)])
           (if (num? v) (num (- 0 (num-num v)))
           (if (bool? v) (bool (not (bool-b v)))
               (error "NUMEX negation applied to non-number or non-bool"))))]
        [(cnd? e)
         (let ([v1 (eval-under-env (cnd-e1 e) env)])
           (if (bool? v1)
                           (if (equal? (bool-b v1) #t) (let ([v2 (eval-under-env (cnd-e2 e) env)]) v2)
                           (let ([v3 (eval-under-env (cnd-e3 e) env)]) v3)
                           )
           (error "None bool condition")
           ))]
        [(iseq? e)
         (let ([v1 (eval-under-env (iseq-e1 e) env)]
               [v2 (eval-under-env (iseq-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))

               (if (equal? (num-num v1) (num-num v2)) (bool #t) (bool #f))

               (if (and (bool? v1)
                    (bool? v2))

               (if (equal? (bool-b v1) (bool-b v2)) (bool #t) (bool #f))
               
               (error "NUMEX iseq applied to non-number and non-boolean")

               )
               
               ))]

        [(ifnzero? e)
         (let ([v1 (eval-under-env (ifnzero-e1 e) env)])
           (if (num? v1)
               (if (equal? (num-num v1) 0)
                   (eval-under-env (ifnzero-e3 e) env)
                   (eval-under-env (ifnzero-e2 e) env))
               (error "NUMEX isnotzero applied to non-number")))]
        
        [(ifleq? e)
         (let ([v1 (eval-under-env (ifleq-e1 e) env)]
               [v2 (eval-under-env (ifleq-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (if (> (num-num v1) (num-num v2))
                   (eval-under-env (ifleq-e4 e) env)
                   (eval-under-env (ifleq-e3 e) env))
               (error "NUMEX ifleq applied to non-number")))]
        
        [(with? e)
         (let ([v1 (eval-under-env (with-e1 e) env)]
               [s (with-s e)])
           (if (string? s)
               (eval-under-env (with-e2 e) (cons (cons s v1) env))
               (error "NUMEX with applied to non-number or the variable name is not string")))]
        [(apair? e)
         (let ([v1 (eval-under-env (apair-e1 e) env)]
               [v2 (eval-under-env (apair-e2 e) env)])
                (apair v1 v2)
               )]
        [(1st? e)
         (let ([v (eval-under-env (1st-e1 e) env)])
           (if (apair? v)
               (apair-e1 v)
               (error "NUMEX 1st applied to non-apair" e)
               ))]
        [(2nd? e)
         (let ([v (eval-under-env (2nd-e1 e) env)])
           (if (apair? v)
               (apair-e2 v)
               (error "NUMEX 2nd applied to non-apair")
               ))]
        [(ismunit? e)
         (let ([v (eval-under-env (ismunit-e e) env)])
           (if (munit? v) (bool #t) (bool #f)))]

        [(lam? e)
         (let ([s1 (lam-s1 e)]
               [s2 (lam-s2 e)])
         (if (and (or (string? s1) (null? s1)) (string? s2))
             (closure env e)
             (error "NUMEX function name and parameter name must be string")))]
        
        [(apply? e)
         (let ([actual (eval-under-env (apply-actual e) env)]
               [clsr (eval-under-env (apply-funexp e) env)])
           (if (closure? clsr)
               (let* ([clsrFun (closure-fun clsr)]
                     [funname (lam-s1 clsrFun)]
                     [arg (lam-s2 clsrFun)]
                     [body (lam-e clsrFun)])
                 (if (null? funname)
                     (eval-under-env body (cons (cons arg actual) (closure-env clsr)))
                     (eval-under-env body (cons (cons funname clsr) (cons (cons arg actual) (closure-env clsr))))))
               (error "NUMEX apply applied to non-function" e)))]
        
        [(closure? e) e]

        [#t (error (format "bad NUMEX expression: ~v" e))]))

;; Do NOT change
(define (eval-exp e)
  (eval-under-env e null))

;;Problem3
(define (ifmunit e1 e2 e3) (cnd (ismunit e1) e2 e3))

(define (with* bs e2) (
                        cond
                         [(null? bs) e2]
                         [#t (with (caar bs) (cdar bs) (with* (cdr bs) e2))]
                         ))

(define (ifneq e1 e2 e3 e4) (
                             cnd (iseq e1 e2) e4 e3
                             )
)
(define (ifneq2 e1 e2 e3 e4)
  (with "_x" e1 (with "_y" e2
                      (ifleq (var "_y")(var "_x") e3
                               (ifleq (var "_x") (var "_y") e3 e4)))))
;;Problem4
(define numex-filter (
                       lam null "func"
                           (lam "map" "list"
                                (cnd (ismunit (var "list")) (munit)
                                     (with "res" (apply (var "func") (1st (var "list")))
                                                                        (ifnzero (var "res")
                                                                             (apair (var "res") (apply (var "map") (2nd (var "list"))))
                                                                             (apply (var "map") (2nd (var "list"))))
                                                                             ))
                           )
                       ))

(define numex-all-gt (
                      lam null "i"
                          (lam null "list"
                               (apply (apply numex-filter (lam null "inp" (ifleq (var "inp") (var "i") (num 0) (num (var "inp")) ))) (var "list"))
                               )
                          ))

 