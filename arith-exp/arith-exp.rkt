#lang racket

(require redex/reduction-semantics)


;; definition of the language syntax

(define-language ArithExpL
  (e ::= zero
         (succ e)
         true
         false
         (is-zero e)
         (pred e)
         (if e e e))
  (t ::= nat
         bool))

;; definitions necessary for semantics

(define-extended-language ArithExpCtxL ArithExpL
  (E ::= hole
         (succ E)
         (is-zero E)
         (pred E)
         (if E e e))
  (bv ::= true
          false)
  (nv ::= zero
          (succ nv))
  (v  ::= bv
          nv))

;; semantics

(define ->
  (reduction-relation
   ArithExpCtxL

   ;; rules for is-zero

   (--> (in-hole E (is-zero zero))
        (in-hole E true)
        "E-is-zero-zero")
   
   (--> (in-hole E (is-zero (succ nv_1)))
        (in-hole E false)
        "E-is-zero-succ")
   
   ;; rules for pred
   (--> (in-hole E (pred zero))
        (in-hole E zero)
        "E-is-pred-zero")
   
   (--> (in-hole E (pred (succ nv_1)))
        (in-hole E nv_1)
        "E-is-pred-succ")
   
   ;; rules for if
   
   (--> (in-hole E (if true e_1 e_2))
        (in-hole E e_1)
        "E-if-true")
   
   (--> (in-hole E (if false e_1 e_2))
        (in-hole E e_2)
        "E-if-false")))

(define ->* (context-closure -> ArithExpCtxL E))

(define-metafunction ArithExpCtxL
    eval : e -> v
    [(eval e)
     ,(car (apply-reduction-relation* ->* (term e)))])


;; type rules

(define-judgment-form ArithExpCtxL
  #:contract (type-of e t)
  #:mode (type-of I I)
  
  [------------------"T-Zero"
   (type-of zero nat)]

  [    (type-of e nat)
   -----------------------"T-Succ"
   (type-of (succ e) nat)]

  [    (type-of e nat)
   ---------------------------"T-IsZero"
   (type-of (is-zero e) bool)]

  [   (type-of e nat)
   ---------------------------"T-Pred"
   (type-of (pred e) nat)]

  [    (type-of e_1 bool)
       (type-of e_2 T)
       (type-of e_3 T)
   ---------------------------"T-If"
   (type-of (if e_1 e_2 e_3) T)])


;; random meta-theory testing


(redex-check
   ArithExpCtxL
   #:satisfying (type-of e t)
   (redex-match? ArithExpCtxL v (term (eval e)))
   #:attempts 1000)