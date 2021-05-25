#lang racket

(require redex/reduction-semantics)

(provide all-defined-out)

;; syntax for the simply typed lambda calculus

(define-language STLC
  (e ::= x
         (e e)
         (lam x t e)
         natural)
  (x ::= variable-not-otherwise-mentioned)
  (v ::= natural
         (lam x t e))
  (t ::= (-> t t)
         nat)
  (E ::= hole
         (v E)
         (E e))
  #:binding-forms
  (lam x t e #:refers-to x))


;; syntax extension for unit

(define-extended-language STLC-Unit STLC
  (e ::= ....
         unit)
  (v ::= ....
         unit)
  (t ::= ....
         unit))

(define ->e
  (reduction-relation
   STLC-Unit
   #:domain e
   #:codomain e

   (--> ((lam x t e_1) v_2)
        (substitute e_1 x v_2)
        "Beta")))

(define ->e* (context-closure ->e STLC-Unit E))
(define ->ev (compatible-closure ->e STLC-Unit e))

(define-metafunction STLC-Unit
  eval : e -> e
  [(eval e)
   ,(car (apply-reduction-relation* ->e* (term e)))])  

;; type system

(define-extended-language STLC-Unit-Ctx STLC-Unit
  (G ::= nil
         (G (x : t))))

(define-metafunction STLC-Unit
  different : x x -> boolean
  [(different x x) #f]
  [(different x y) #t])

(define-judgment-form STLC-Unit-Ctx
  #:contract (type-of G e t)
  #:mode (type-of I I O)

  [--------------------------"T-Unit"
   (type-of G unit unit)]

    
  [--------------------------"T-Nat"
     (type-of G natural nat)]

  [--------------------------"T-Var-Here"
   (type-of (G (x : t)) x t) ]

  [(type-of G x t)
   (where #t (different x y))
   ----------------------------"T-Var-There"
   (type-of (G (y : t_1)) x t)]

  [(type-of (G (x : t_1)) e t_2)
   --------------------------------------"T-Lam"
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
               ->e              (term (,e))))))


; progress property

(define (v? e)
  (redex-match? STLC-Unit-Ctx v))

(define (progress-holds? g e)
  (if (types? g e)
      (or (v? e)
          (reduces? e))
      #t))


(redex-check
   STLC-Unit-Ctx
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
     (for/and ([v (apply-reduction-relation* ->e* e)])
       (equal? (judgment-holds (type-of ,g ,v t) t)
               types1))]))

(redex-check
   STLC-Unit-Ctx
   #:satisfying (type-of nil e t)
   (preservation-holds? (term nil) (term e))
   #:attempts 100)
