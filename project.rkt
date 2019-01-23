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
(struct minus  (e1 e2)  #:transparent)  ;; subtract two expressions
(struct mult (e1 e2)  #:transparent)  ;; multiply two expressions
(struct div (e1 e2)  #:transparent)  ;; divide two expressions
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
        [(minus? e)
         (let ([v1 (eval-under-env (minus-e1 e) env)]
               [v2 (eval-under-env (minus-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (- (num-num v1)
                       (num-num v2)))
               (error "NUMEX subtraction applied to non-number")))]
        [(mult? e)
         (let ([v1 (eval-under-env (mult-e1 e) env)]
               [v2 (eval-under-env (mult-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (* (num-num v1)
                       (num-num v2)))
               (error "NUMEX multiplication applied to non-number")))]
        [(div? e)
         (let ([v1 (eval-under-env (div-e1 e) env)]
               [v2 (eval-under-env (div-e2 e) env)])
           (if (and (num? v1)(num? v2)) (if (equal? v2 (num 0)) (error "Division by zero") (num (quotient (num-num v1)(num-num v2))))
               (error "NUMEX division applied to non-number")))]
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
        [(orelse? e)
         (let ([v1 (eval-under-env (orelse-e1 e) env)])
           (if (bool? v1)
                           (if (equal? (bool-b v1) #t) (bool #t) (let ([v2 (eval-under-env (orelse-e2 e) env)])
                                                            (if (bool? v2) (if (equal? (bool-b v2) #t) (bool #t) (bool #f)) (error "None bool second expression")))
                           )
           (error "None bool first expression")
           ))]
        [(andalso? e)
         (let ([v1 (eval-under-env (andalso-e1 e) env)])
           (if (bool? v1)
                           (if (equal? (bool-b v1) #t) (let ([v2 (eval-under-env (andalso-e2 e) env)])
                                                            (if (bool? v2) (if (equal? (bool-b v2) #t) (bool #t) (bool #f)) (error "None bool second expression"))) (bool #f)
                           )
           (error "None bool first expression")
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

 ;; Challenge Problem

(struct fun-challenge (nameopt formal body freevars) #:transparent) ;; a recursive(?) 1-argument function

;; We will test this function directly, so it must do
;; as described in the assignment
(define (compute-free-vars e)
  (car (compute-free-vars-handler e)))


;; return a cons of computed 'e and free vars of 'e
(define (compute-free-vars-handler e)
   (cond [(var? e) (cons e (set (var-string e)))]
        [(num? e) (cons e (set))]
        [(bool? e) (cons e (set))]
        [(munit? e) (cons e (set))]
        [(plus? e)
         (let ([v1 (compute-free-vars-handler (plus-e1 e))]
               [v2 (compute-free-vars-handler (plus-e2 e))])
           (cons (plus (car v1) (car v2)) (set-union (cdr v1) (cdr v2))))]
        [(minus? e)
         (let ([v1 (compute-free-vars-handler (minus-e1 e))]
               [v2 (compute-free-vars-handler (minus-e2 e))])
           (cons (minus (car v1) (car v2)) (set-union (cdr v1) (cdr v2))))]
        [(mult? e)
         (let ([v1 (compute-free-vars-handler (mult-e1 e))]
               [v2 (compute-free-vars-handler (mult-e2 e))])
           (cons (mult (car v1) (car v2)) (set-union (cdr v1) (cdr v2))))]
        [(div? e)
         (let ([v1 (compute-free-vars-handler (div-e1 e))]
               [v2 (compute-free-vars-handler (div-e2 e))])
           (cons (div (car v1) (car v2)) (set-union (cdr v1) (cdr v2))))]
        [(neg? e)
         (let ([v1 (compute-free-vars-handler (neg-e e))])
           (cons (neg (car v1)) (cdr v1)))]
        [(cnd? e)
        (let ([v1 (compute-free-vars-handler (cnd-e1 e))]
              [v2 (compute-free-vars-handler (cnd-e2 e))]
              [v3 (compute-free-vars-handler (cnd-e2 e))])
           (cons (cnd (car v1) (car v2) (car v3)) (set-union (cdr v1) (cdr v2) (cdr v3))))]
        [(orelse? e)
        (let ([v1 (compute-free-vars-handler (orelse-e1 e))]
              [v2 (compute-free-vars-handler (orelse-e2 e))])
           (cons (orelse (car v1) (car v2)) (set-union (cdr v1) (cdr v2))))]
        [(andalso? e)
        (let ([v1 (compute-free-vars-handler (andalso-e1 e))]
              [v2 (compute-free-vars-handler (andalso-e2 e))])
           (cons (andalso (car v1) (car v2)) (set-union (cdr v1) (cdr v2))))]
        [(iseq? e)
        (let ([v1 (compute-free-vars-handler (iseq-e1 e))]
              [v2 (compute-free-vars-handler (iseq-e2 e))])
           (cons (iseq (car v1) (car v2)) (set-union (cdr v1) (cdr v2))))]
        [(ifnzero? e)
         (let ([v1 (compute-free-vars-handler (ifnzero-e1 e))]
               [v2 (compute-free-vars-handler (ifnzero-e2 e))]
               [v3 (compute-free-vars-handler (ifnzero-e3 e))])
           (cons (ifnzero (car v1) (car v2) (car v3)) (set-union (cdr v1) (cdr v2) (cdr v3))))]
        [(ifleq? e)
          (let ([v1 (compute-free-vars-handler (ifleq-e1 e))]
                [v2 (compute-free-vars-handler (ifleq-e2 e))]
                [v3 (compute-free-vars-handler (ifleq-e3 e))]
                [v4 (compute-free-vars-handler (ifleq-e4 e))])
           (cons (ifleq (car v1) (car v2) (car v3) (car v4)) (set-union (cdr v1) (cdr v2) (cdr v3) (cdr v4))))]
        [(with? e)
         (let ([v1 (compute-free-vars-handler (with-e1 e))]
               [v2 (compute-free-vars-handler (with-e2 e))])
            (cons (with (with-s e) (car v1) (car v2)) (set-union (set-remove (cdr v2) (with-s e)) (cdr v1))))]
        [(apair? e)
         (let ([v1 (compute-free-vars-handler (apair-e1 e))]
               [v2 (compute-free-vars-handler (apair-e2 e))])
           (cons (apair (car v1) (car v2)) (set-union (cdr v1) (cdr v2))))]
        [(1st? e)
         (let ([v1 (compute-free-vars-handler (1st-e1 e))])
           (cons (1st (car v1)) (cdr v1)))]
        [(2nd? e)
          (let ([v1 (compute-free-vars-handler (2nd-e1 e))])
           (cons (second (car v1)) (cdr v1)))]
        [(ismunit? e)
          (let ([v1 (compute-free-vars-handler (ismunit-e e))])
           (cons (neg (car v1)) (cdr v1)))]

        [(lam? e)
          (let ([cfvf (compute-free-vars-handler (lam-e e))])
            (let ([free-var-set (set-remove (set-remove (cdr cfvf) (lam-s2 e)) (lam-s1 e))])
               (cons (fun-challenge (lam-s1 e) (lam-s2 e) (car cfvf) free-var-set) free-var-set)))]
        [(apply? e)
         (let ([va (compute-free-vars-handler (apply-actual e))]
               [vf (compute-free-vars-handler (apply-funexp e))])
           (cons (apply (car vf) (car va)) (set-union (cdr vf) (cdr va))))]

        [#t (error (format "bad NUMEX expression: ~v" e))]))


(define (eval-under-env-c e env)
  (cond [(var? e) (envlookup env (var-string e))]
        [(num? e)
         (cond [(integer? (num-num e)) e]
               [else (error "NUMEX num applied to non racket integer")])]
        [(bool? e)
         (cond [(boolean? (bool-b e)) e]
               [else (error "NUMEX bool applied to non racket integer")])]
        [(munit? e) e]
        [(plus? e)
         (let ([v1 (eval-under-env-c (plus-e1 e) env)]
               [v2 (eval-under-env-c (plus-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (+ (num-num v1)
                       (num-num v2)))
               (error "NUMEX addition applied to non-number")))]
        [(minus? e)
         (let ([v1 (eval-under-env-c (minus-e1 e) env)]
               [v2 (eval-under-env-c (minus-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (- (num-num v1)
                       (num-num v2)))
               (error "NUMEX subtraction applied to non-number")))]
        [(mult? e)
         (let ([v1 (eval-under-env-c (mult-e1 e) env)]
               [v2 (eval-under-env-c (mult-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (* (num-num v1)
                       (num-num v2)))
               (error "NUMEX multiplication applied to non-number")))]
        [(div? e)
         (let ([v1 (eval-under-env-c (div-e1 e) env)]
               [v2 (eval-under-env-c (div-e2 e) env)])
           (if (and (num? v1)(num? v2)) (if (equal? v2 (num 0)) (error "Division by zero") (num (quotient (num-num v1)(num-num v2))))
               (error "NUMEX division applied to non-number")))]
        [(neg? e)
         (let ([v (eval-under-env-c (neg-e e) env)])
           (if (num? v) (num (- 0 (num-num v)))
           (if (bool? v) (bool (not (bool-b v)))
               (error "NUMEX negation applied to non-number or non-bool"))))]
        [(cnd? e)
         (let ([v1 (eval-under-env-c (cnd-e1 e) env)])
           (if (bool? v1)
                           (if (equal? (bool-b v1) #t) (let ([v2 (eval-under-env-c (cnd-e2 e) env)]) v2)
                           (let ([v3 (eval-under-env-c (cnd-e3 e) env)]) v3)
                           )
           (error "None bool condition")
           ))]
        [(orelse? e)
         (let ([v1 (eval-under-env-c (orelse-e1 e) env)])
           (if (bool? v1)
                           (if (equal? (bool-b v1) #t) (bool #t) (let ([v2 (eval-under-env-c (orelse-e2 e) env)])
                                                            (if (bool? v2) (if (equal? (bool-b v2) #t) (bool #t) (bool #f)) (error "None bool second expression")))
                           )
           (error "None bool first expression")
           ))]
        [(andalso? e)
         (let ([v1 (eval-under-env-c (andalso-e1 e) env)])
           (if (bool? v1)
                           (if (equal? (bool-b v1) #t) (let ([v2 (eval-under-env-c (andalso-e2 e) env)])
                                                            (if (bool? v2) (if (equal? (bool-b v2) #t) (bool #t) (bool #f)) (error "None bool second expression"))) (bool #f)
                           )
           (error "None bool first expression")
           ))]
        [(iseq? e)
         (let ([v1 (eval-under-env-c (iseq-e1 e) env)]
               [v2 (eval-under-env-c (iseq-e2 e) env)])
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
         (let ([v1 (eval-under-env-c (ifnzero-e1 e) env)])
           (if (num? v1)
               (if (equal? (num-num v1) 0)
                   (eval-under-env-c (ifnzero-e3 e) env)
                   (eval-under-env-c (ifnzero-e2 e) env))
               (error "NUMEX isnotzero applied to non-number")))]
        
        [(ifleq? e)
         (let ([v1 (eval-under-env-c (ifleq-e1 e) env)]
               [v2 (eval-under-env-c (ifleq-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (if (> (num-num v1) (num-num v2))
                   (eval-under-env-c (ifleq-e4 e) env)
                   (eval-under-env-c (ifleq-e3 e) env))
               (error "NUMEX ifleq applied to non-number")))]
        
        [(with? e)
         (let ([v1 (eval-under-env-c (with-e1 e) env)]
               [s (with-s e)])
           (if (string? s)
               (eval-under-env-c (with-e2 e) (cons (cons s v1) env))
               (error "NUMEX with applied to non-number or the variable name is not string")))]
        [(apair? e)
         (let ([v1 (eval-under-env-c (apair-e1 e) env)]
               [v2 (eval-under-env-c (apair-e2 e) env)])
                (apair v1 v2)
               )]
        [(1st? e)
         (let ([v (eval-under-env-c (1st-e1 e) env)])
           (if (apair? v)
               (apair-e1 v)
               (error "NUMEX 1st applied to non-apair" e)
               ))]
        [(2nd? e)
         (let ([v (eval-under-env-c (2nd-e1 e) env)])
           (if (apair? v)
               (apair-e2 v)
               (error "NUMEX 2nd applied to non-apair")
               ))]
        [(ismunit? e)
         (let ([v (eval-under-env-c (ismunit-e e) env)])
           (if (munit? v) (bool #t) (bool #f)))]

        [(lam? e)
         (let ([s1 (lam-s1 e)]
               [s2 (lam-s2 e)])
         (if (and (or (string? s1) (null? s1)) (string? s2))
             (closure env e)
             (error "NUMEX function name and parameter name must be string")))]
        [(fun-challenge? e)
         (let ([nameopt (fun-challenge-nameopt e)]
               [formal (fun-challenge-formal e)]
               [freevars (fun-challenge-freevars e)])
         (if (and (or (string? nameopt) (null? nameopt)) (string? formal))
             (closure (commons env freevars)  e)
             (error "NUMEX function name and parameter name must be string")))]
        
        [(apply? e)
         (let ([actual (eval-under-env-c (apply-actual e) env)]
               [clsr (eval-under-env-c (apply-funexp e) env)])
           (if (closure? clsr)
               (let* ([clsrFun (closure-fun clsr)]
                     [funname (lam-s1 clsrFun)]
                     [arg (lam-s2 clsrFun)]
                     [body (lam-e clsrFun)])
                 (if (null? funname)
                     (eval-under-env-c body (cons (cons arg actual) (closure-env clsr)))
                     (eval-under-env-c body (cons (cons funname clsr) (cons (cons arg actual) (closure-env clsr))))))
               (error "NUMEX apply applied to non-function" e)))]
        
        [(closure? e) e]

        [#t (error (format "bad NUMEX expression: ~v" e))]))


(define (commons env set)
  (if (equal? env null) null
      (if (set-member? set (car (car env)))
          (cons (car env) (commons (cdr env) set))
          (commons (cdr env) set))))

(define (eval-exp-c e)
  (eval-under-env-c (compute-free-vars e) null))