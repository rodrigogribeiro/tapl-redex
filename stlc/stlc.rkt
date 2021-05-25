#lang racket

(require redex/reduction-semantics)

;; syntax for the simply typed lambda calculus

(define-language STLCL
  (e ::= x
         (e e)
         (lam x t e)
         natural)
  (x ::= variable-not-otherwise-mentioned)
  (v ::= natural
         (lam x t e))
  (t ::= (-> t t)
         nat)
  #:binding-forms
  (lam x t e #:refers-to x))

;; semantics definitions

(define-extended-language STLC-CtxL STLCL
  (E ::= hole
         (v E)
         (E e)))

(define ->
  (reduction-relation
   STLCL
   #:domain e
   #:codomain e

   (--> ((lam x t e_1) v_2)
        (substitute e_1 x v_2)
        "Beta")))


(define ->* (context-closure -> STLC-CtxL E))
(define ->v (compatible-closure -> STLC-CtxL e))


(define-metafunction STLCL
  eval : e -> e
  [(eval e)
   ,(car (apply-reduction-relation* ->* (term e)))])

(define-metafunction STLC-CtxL
  normalize : e -> v
  [(normalize e)
   ,(car (apply-reduction-relation* ->v (term e)))])

;; typing judgment

(define-extended-language STLC-Ty-CtxL STLCL
  (G ::= nil
         (G (x : t))))

(define-metafunction STLCL
  different : x x -> boolean
  [(different x x) #f]
  [(different x y) #t])

(define-judgment-form STLC-Ty-CtxL
  #:contract (type-of G e t)
  #:mode (type-of I I O)
  
  [--------------------------"T-Nat"
     (type-of G natural nat)]

  [--------------------------"T-Var-Here"
   (type-of (G (x : t)) x t) ]

  [(type-of G x t)
   (where #t (different x y))
   ----------------------------"T-Var-There"
   (type-of (G (y : t_1)) x t)]

  [(type-of (G (x : t_1)) e t_2)
   ---------------------------------"T-Lam"
   (type-of G (lam x t_1 e) (-> t_1 t_2))]

  [(type-of G e_1 (-> t_1 t_2))
   (type-of G e_2 t_1)
   ---------------------------------"T-App"
   (type-of G (e_1 e_2) t_2)])

;; testing soundness.

(define (types? g e)
  (not (null? (judgment-holds (type-of ,g ,e t)
                              t))))

(define (reduces? e)
  (not (null? (apply-reduction-relation
               ->             (term (,e))))))


; progress property

(define (v? e)
  (redex-match? STLCL v))

(define (progress-holds? g e)
  (if (types? g e)
      (or (v? e)
          (reduces? e))
      #t))


(redex-check
   STLC-Ty-CtxL
   #:satisfying (type-of nil e t)
   (progress-holds? (term nil) (term e))
   #:attempts 100)

; preservation

(define (preservation-holds? g e)
  (define types1 (judgment-holds (type-of ,g ,e t) t))
  (unless (null? types1)
    (unless (= 1 (length types1)) (error 'preservation "multiple types! ~s" e)))
  (cond
    [(null? types1) #t]
    [else
     (for/and ([v (apply-reduction-relation* ->v e)])
       (equal? (judgment-holds (type-of ,g ,v t) t)
               types1))]))

(redex-check
   STLC-Ty-CtxL
   #:satisfying (type-of nil e t)
   (preservation-holds? (term nil) (term e))
   #:attempts 100)
