#lang typed/racket

(require racket/flonum
         racket/fixnum
         racket/match
         racket/unsafe/ops
         (for-syntax racket/base racket/syntax))



;                                                                                                     
;                                                                                                     
;                                                                                                     
;       ;;;  ;;;                                                   ;           ;                      
;      ;       ;                                                   ;           ;       ;              
;      ;       ;                                                   ;                   ;              
;    ;;;;;;    ;        ;;;    ; ;;;;   ;     ;  ;;;;;;            ; ;;;     ;;;     ;;;;;;    ;;;;;  
;      ;       ;       ;   ;   ;;   ;;  ;     ;  ;  ;  ;           ;;   ;      ;       ;      ;     ; 
;      ;       ;      ;     ;  ;     ;  ;     ;  ;  ;  ;           ;     ;     ;       ;      ;       
;      ;       ;      ;     ;  ;     ;  ;     ;  ;  ;  ;    ;;;;   ;     ;     ;       ;      ;;;;    
;      ;       ;      ;     ;  ;     ;  ;     ;  ;  ;  ;           ;     ;     ;       ;         ;;;; 
;      ;       ;      ;     ;  ;     ;  ;     ;  ;  ;  ;           ;     ;     ;       ;            ; 
;      ;       ;       ;   ;   ;     ;  ;;   ;;  ;  ;  ;           ;;   ;      ;       ;      ;     ; 
;      ;        ;;;     ;;;    ;     ;   ;;;; ;  ;  ;  ;           ; ;;;    ;;;;;;;     ;;;    ;;;;;  
;                                                                                                     
;                                                                                                     
;                                                                                                     
;                                                                                                     


(: flonum->bit-field (Flonum -> Natural))
(define (flonum->bit-field x)
  (assert (integer-bytes->integer (real->floating-point-bytes x (ann 8 8)) #f)
          exact-nonnegative-integer?))

(: bit-field->flonum (Integer -> Flonum))
(define (bit-field->flonum i)
  (cond [(and (i . >= . 0) (i . <= . #xffffffffffffffff))
         (floating-point-bytes->real (integer->integer-bytes i 8 #f))]
        [else
         (raise-argument-error 'bit-field->flonum "Integer in [0 .. #xffffffffffffffff]" i)]))

(define implicit-leading-one (arithmetic-shift 1 52))
(define max-significand (- implicit-leading-one 1))
(define max-exponent 2047)
(define max-signed-exponent 1023)
(define min-signed-exponent -1074)

(: flonum->fields (Flonum -> (Values (U 0 1) Index Natural)))
(define (flonum->fields x)
  (define n (flonum->bit-field x))
  (values (if (zero? (bitwise-bit-field n 63 64)) 0 1)
          (assert (bitwise-bit-field n 52 63) index?)
          (bitwise-bit-field n 0 52)))

(: fields->flonum (Integer Integer Integer -> Flonum))
(define (fields->flonum s e m)
  (cond [(not (or (= s 0) (= s 1)))
         (raise-argument-error 'fields->flonum "(U 0 1)" 0 s e m)]
        [(or (e . < . 0) (e . > . max-exponent))
         (raise-argument-error 'fields->flonum (format "Natural <= ~e" max-exponent) 1 s e m)]
        [(or (m . < . 0) (m . > . max-significand))
         (raise-argument-error 'fields->flonum (format "Natural <= ~a" max-significand) 2 s e m)]
        [else
         (bit-field->flonum (bitwise-ior (arithmetic-shift s 63)
                                         (arithmetic-shift e 52)
                                         m))]))

(: flonum->sig+exp (Flonum -> (Values Integer Fixnum)))
(define (flonum->sig+exp x)
  (define-values (s e m) (flonum->fields x))
  (let-values ([(sig exp)  (if (= e 0)
                               (values m -1074)
                               (values (bitwise-ior m implicit-leading-one)
                                       (assert (- e 1075) fixnum?)))])
    (values (if (zero? s) sig (- sig)) exp)))

(: sig+exp->flonum (Integer Integer -> Flonum))
(define (sig+exp->flonum sig exp)
  (cond [(= sig 0)  0.0]
        [(exp . > . max-signed-exponent)  (if (sig . < . 0) -inf.0 +inf.0)]
        [(exp . < . min-signed-exponent)  (if (sig . < . 0) -0.0 0.0)]
        [else  (real->double-flonum (* sig (expt 2 exp)))]))

(: flonum->ordinal (Flonum -> Integer))
(define (flonum->ordinal x)
  (cond [(x . fl< . 0.0)  (- (flonum->bit-field (fl- 0.0 x)))]
        [else             (flonum->bit-field (flabs x))])) ; abs for -0.0

(: ordinal->flonum (Integer -> Flonum))
(define (ordinal->flonum i)
  (cond [(and (i . >= . #x-7fffffffffffffff) (i . <= . #x7fffffffffffffff))
         (cond [(i . < . 0)  (fl- 0.0 (bit-field->flonum (- i)))]
               [else         (bit-field->flonum i)])]
        [else
         (raise-argument-error
          'ordinal->flonum "Integer in [#x-7fffffffffffffff .. #x7fffffffffffffff]" i)]))

(define +inf-ordinal (flonum->ordinal +inf.0))
(define -inf-ordinal (flonum->ordinal -inf.0))

(: flstep (Flonum Integer -> Flonum))
(define (flstep x n)
  (cond [(not (and (x . fl>= . -inf.0) (x . fl<= . +inf.0)))  +nan.0]
        [(and (fl= x +inf.0) (n . >= . 0))  +inf.0]
        [(and (fl= x -inf.0) (n . <= . 0))  -inf.0]
        [else  (define i (+ n (flonum->ordinal x)))
               (cond [(i . < . -inf-ordinal)  -inf.0]
                     [(i . > . +inf-ordinal)  +inf.0]
                     [else  (ordinal->flonum i)])]))

(: flnext (Flonum -> Flonum))
(define (flnext x) (flstep x 1))

(: flprev (Flonum -> Flonum))
(define (flprev x) (flstep x -1))

(: flonums-between (Flonum Flonum -> Integer))
(define (flonums-between x y)
  (- (flonum->ordinal y) (flonum->ordinal x)))

(: flulp (Flonum -> (U Flonum-Nan Nonnegative-Flonum)))
(define (flulp x)
  (let ([x  (flabs x)])
    (cond [(fl= x +inf.0)  +nan.0]
          [(eqv? x +nan.0)  +nan.0]
          [(fl= x 0.0)  0.0]
          [else
           (define ulp (flabs (fl- (flnext x) x)))
           (cond [(fl= ulp +inf.0)  (flabs (fl- x (flprev x)))]
                 [else  ulp])])))


;                                                                                                                                                  
;                                                                                                                                                  
;                                                                                                                                                  
;       ;;;  ;;;                                                                                                                                   
;      ;       ;                                                                                         ;                          ;              
;      ;       ;                                                                                         ;                          ;              
;    ;;;;;;    ;        ;;;    ; ;;;;   ;     ;  ;;;;;;              ;;;      ;;;    ; ;;;;    ;;;;;   ;;;;;;     ;;;;   ; ;;;;   ;;;;;;    ;;;;;  
;      ;       ;       ;   ;   ;;   ;;  ;     ;  ;  ;  ;            ;   ;    ;   ;   ;;   ;;  ;     ;    ;       ;    ;  ;;   ;;    ;      ;     ; 
;      ;       ;      ;     ;  ;     ;  ;     ;  ;  ;  ;           ;        ;     ;  ;     ;  ;          ;            ;  ;     ;    ;      ;       
;      ;       ;      ;     ;  ;     ;  ;     ;  ;  ;  ;    ;;;;   ;        ;     ;  ;     ;  ;;;;       ;       ;;;;;;  ;     ;    ;      ;;;;    
;      ;       ;      ;     ;  ;     ;  ;     ;  ;  ;  ;           ;        ;     ;  ;     ;     ;;;;    ;      ;;    ;  ;     ;    ;         ;;;; 
;      ;       ;      ;     ;  ;     ;  ;     ;  ;  ;  ;           ;        ;     ;  ;     ;        ;    ;      ;     ;  ;     ;    ;            ; 
;      ;       ;       ;   ;   ;     ;  ;;   ;;  ;  ;  ;            ;   ;    ;   ;   ;     ;  ;     ;    ;      ;    ;;  ;     ;    ;      ;     ; 
;      ;        ;;;     ;;;    ;     ;   ;;;; ;  ;  ;  ;             ;;;      ;;;    ;     ;   ;;;;;      ;;;    ;;;; ;  ;     ;     ;;;    ;;;;;  
;                                                                                                                                                  
;                                                                                                                                                  
;                                                                                                                                                  
;                                                                                                                                                  


(define -max.0 (assert (flnext -inf.0) negative?))
(define -min.0 (assert (flprev 0.0) negative?))
(define +min.0 (assert (flnext 0.0) positive?))
(define +max.0 (assert (flprev +inf.0) positive?))

(define +max-subnormal.0 (assert (ordinal->flonum #xfffffffffffff) positive?))
(define -max-subnormal.0 (- +max-subnormal.0))

;; The smallest flonum that can be added to 1.0 to get a result != 1.0
(define epsilon.0 (assert (flulp 1.0) positive?))




;                                                                                                                                                  
;                                                                                                                                                  
;                                                                                                                                                  
;       ;;;  ;;;                                                       ;;;                                         ;                               
;      ;       ;                                                      ;                                  ;         ;                               
;      ;       ;                                                      ;                                  ;                                         
;    ;;;;;;    ;        ;;;    ; ;;;;   ;     ;  ;;;;;;             ;;;;;;  ;     ;  ; ;;;;     ;;;    ;;;;;;    ;;;       ;;;    ; ;;;;    ;;;;;  
;      ;       ;       ;   ;   ;;   ;;  ;     ;  ;  ;  ;              ;     ;     ;  ;;   ;;   ;   ;     ;         ;      ;   ;   ;;   ;;  ;     ; 
;      ;       ;      ;     ;  ;     ;  ;     ;  ;  ;  ;              ;     ;     ;  ;     ;  ;          ;         ;     ;     ;  ;     ;  ;       
;      ;       ;      ;     ;  ;     ;  ;     ;  ;  ;  ;    ;;;;      ;     ;     ;  ;     ;  ;          ;         ;     ;     ;  ;     ;  ;;;;    
;      ;       ;      ;     ;  ;     ;  ;     ;  ;  ;  ;              ;     ;     ;  ;     ;  ;          ;         ;     ;     ;  ;     ;     ;;;; 
;      ;       ;      ;     ;  ;     ;  ;     ;  ;  ;  ;              ;     ;     ;  ;     ;  ;          ;         ;     ;     ;  ;     ;        ; 
;      ;       ;       ;   ;   ;     ;  ;;   ;;  ;  ;  ;              ;     ;;   ;;  ;     ;   ;   ;     ;         ;      ;   ;   ;     ;  ;     ; 
;      ;        ;;;     ;;;    ;     ;   ;;;; ;  ;  ;  ;              ;      ;;;; ;  ;     ;    ;;;       ;;;   ;;;;;;;    ;;;    ;     ;   ;;;;;  
;                                                                                                                                                  
;                                                                                                                                                  
;                                                                                                                                                  
;                                                                                                                                                  



(module syntax-defs racket/base
  (require (for-syntax racket/base)
           racket/flonum)
  (provide fl)
  (define-syntax (fl stx)
    ;; can't use a rename transformer: get error:
    ;; "unsealed local-definition or module context found in syntax object"
    (syntax-case stx ()
      [(_ . args)  (syntax/loc stx (real->double-flonum . args))]
      [_  (syntax/loc stx real->double-flonum)])))

(require 'syntax-defs)

(: flsubnormal? (Flonum -> Boolean))
(define (flsubnormal? x)
  (and ((flabs x) . fl<= . +max-subnormal.0)
       (not (fl= x 0.0))))

(define flrational?
  (λ: ([x : Flonum])
    (fl< (flabs x) +inf.0)))

(define flinfinite?
  (λ: ([x : Flonum])
    (fl= (flabs x) +inf.0)))

(define flnan?
  (λ: ([x : Flonum])
    (not (fl<= (flabs x) +inf.0))))

(define flinteger?
  (λ: ([x : Flonum])
    (fl= x (fltruncate x))))

(: flsubnormal-next* (Flonum -> Flonum))
(define (flsubnormal-next* x)
  (fl/ (fl+ (fl* x (flexpt 2.0 1022.0)) epsilon.0)
       (flexpt 2.0 1022.0)))

(: flsubnormal-prev* (Flonum -> Flonum))
(define (flsubnormal-prev* x)
  (fl/ (fl- (fl* x (flexpt 2.0 1022.0)) epsilon.0)
       (flexpt 2.0 1022.0)))

(: flnext* (Flonum -> Flonum))
(define (flnext* x)
  (cond [(x . fl< . 0.0)  (fl- 0.0 (flprev* (fl- 0.0 x)))]
        [(fl= x 0.0)  +min.0]
        [(fl= x +inf.0)  +inf.0]
        [else  (define next-x (fl+ x (fl* x (fl* 0.5 epsilon.0))))
               (cond [(fl= next-x x)  (fl+ x (fl* x epsilon.0))]
                     [else  next-x])]))

(: flprev* (Flonum -> Flonum))
(define (flprev* x)
  (cond [(x . fl< . 0.0)  (fl- 0.0 (flnext* (fl- 0.0 x)))]
        [(fl= x 0.0)  -min.0]
        [(fl= x +inf.0)  +max.0]
        [else  (define prev-x (fl- x (fl* x (fl* 0.5 epsilon.0))))
               (cond [(fl= prev-x x)  (fl- x (fl* x epsilon.0))]
                     [else  prev-x])]))

;; ===================================================================================================
;; Error measurement

(: flulp-error (Flonum Real -> Flonum))
(define (flulp-error x r)
  (define r.0 (fl r))
  (cond [(eqv? x r)  0.0]
        [(and (fl= x 0.0) (fl= r.0 0.0))  0.0]
        [(and (fl= x +inf.0) (fl= r.0 +inf.0))  0.0]
        [(and (fl= x -inf.0) (fl= r.0 -inf.0))  0.0]
        [(zero? r)  +inf.0]
        [(and (flrational? x) (flrational? r.0))
         (flabs (fl (/ (- (inexact->exact x) (inexact->exact r))
                       (inexact->exact (flmax +min.0 (flulp r.0))))))]
        [else  +inf.0]))

;; ===================================================================================================
;; More floating-point functions
(: flsgn (Flonum -> Flonum))
(define (flsgn x)
  (cond [(fl< x 0.0) -1.0]
        [(fl< 0.0 x)  1.0]
        [else  0.0]))

(: fleven? (Flonum -> Boolean))
(define (fleven? x)
  (let ([x  (flabs x)])
    (or (fl= x 0.0)
        (and (x . fl>= . 2.0)
             (let ([0.5x  (fl* 0.5 x)])
               (fl= (truncate 0.5x) 0.5x))))))

(define last-odd (fl- (flexpt 2.0 53.0) 1.0))

(: flodd? (Flonum -> Boolean))
(define (flodd? x)
  (let ([x  (flabs x)])
    (and (x . fl>= . 1.0) (x . fl<= . last-odd)
         (let ([0.5x  (fl* 0.5 (fl+ 1.0 x))])
           (fl= (truncate 0.5x) 0.5x)))))

(: flhypot (Flonum Flonum -> Flonum))
(define (flhypot x y)
  (define xa (flabs x))
  (define ya (flabs y))
  (let ([xa  (flmin xa ya)]
        [ya  (flmax xa ya)])
    (cond [(fl= xa 0.0)  ya]
          [else  (define u (fl/ xa ya))
                 (fl* ya (flsqrt (fl+ 1.0 (fl* u u))))])))

;; todo: overflow not likely; underflow likely
(: fllog/base (Flonum Flonum -> Flonum))
(define (fllog/base b x)
  (fl/ (fllog x) (fllog b)))

(: flprobability? (case-> (Flonum -> Boolean)
                          (Flonum Any -> Boolean)))
(define (flprobability? p [log? #f])
  (cond [log?  (and (p . fl>= . -inf.0) (p . fl<= . 0.0))]
        [else  (and (p . fl>= . 0.0) (p . fl<= . 1.0))]))
(: flsinpix (Flonum -> Flonum))
;; Computes sin(pi*x) accurately; i.e. error <= 2 ulps but almost always <= 1 ulp
(define (flsinpix x)
  (cond [(fl= x 0.0)  x]
        [(and (x . fl> . -inf.0) (x . fl< . +inf.0))
         (let*-values
             ([(x s)  (if (x . fl< . 0.0) (values (- x) -1.0) (values x 1.0))]
              [(x)    (fl- x (fl* 2.0 (fltruncate (fl* 0.5 x))))]
              [(x s)  (if (x . fl> . 1.0) (values (fl- x 1.0) (fl* s -1.0)) (values x s))]
              [(x)    (if (x . fl> . 0.5) (fl- 1.0 x) x)])
           (fl* s (flsin (fl* pi x))))]
        [else  +nan.0]))

(: flcospix (Flonum -> Flonum))
;; Computes cos(pi*x) accurately; i.e. error <= 1 ulps
(define (flcospix x)
  (cond [(and (x . fl> . -inf.0) (x . fl< . +inf.0))
         (let*-values
             ([(x)  (flabs x)]
              [(x)  (fl- x (fl* 2.0 (fltruncate (fl* 0.5 x))))]
              [(x)  (if (x . fl> . 1.0) (fl- 2.0 x) x)]
              [(x s)  (if (x . fl> . 0.5) (values (fl- 1.0 x) -1.0) (values x 1.0))])
           (cond [(x . fl> . 0.25)  (fl* (fl* s -1.0) (flsin (fl* pi (fl- x 0.5))))]
                 [else  (fl* s (flcos (fl* pi x)))]))]
        [else  +nan.0]))

(: fltanpix (Flonum -> Flonum))
;; Computes tan(pi*x) accurately; i.e. error <= 2 ulps but almost always <= 1 ulp
(define (fltanpix x)
  (cond [(fl= x 0.0)  x]
        [(and (x . fl> . -inf.0) (x . fl< . +inf.0))
         (let*-values 
             ([(x s)  (if (x . fl< . 0.0) (values (- x) -1.0) (values x 1.0))]
              [(x)    (fl- x (fltruncate x))]
              [(x s)  (if (x . fl> . 0.5) (values (fl- 1.0 x) (fl* s -1.0)) (values x s))])
           (cond [(x . fl= . 0.5)  +nan.0]
                 [(x . fl> . 0.25)  (fl/ s (fltan (fl* pi (fl- 0.5 x))))]
                 [else  (fl* s (fltan (fl* pi x)))]))]
        [else  +nan.0]))

(: flcscpix (Flonum -> Flonum))
(define (flcscpix x)
  (cond [(and (not (zero? x)) (flinteger? x))  +nan.0]
        [else  (/ 1.0 (flsinpix x))]))

(: flsecpix (Flonum -> Flonum))
(define (flsecpix x)
  (cond [(and (x . fl> . 0.0) (flinteger? (fl- x 0.5)))  +nan.0]
        [(and (x . fl< . 0.0) (flinteger? (fl+ x 0.5)))  +nan.0]
        [else  (/ 1.0 (flcospix x))]))

(: flcotpix (Flonum -> Flonum))
;; Computes 1/tan(pi*x) accurately; i.e. error <= 2 ulps but almost always <= 1 ulp
(define (flcotpix x)
  (cond [(fl= x 0.0)  (fl/ 1.0 x)]
        [(and (x . fl> . -inf.0) (x . fl< . +inf.0))
         (let*-values 
             ([(x s)  (if (x . fl< . 0.0) (values (- x) -1.0) (values x 1.0))]
              [(x)    (fl- x (fltruncate x))]
              [(x s)  (if (x . fl> . 0.5) (values (fl- 1.0 x) (fl* s -1.0)) (values x s))])
           (cond [(x . fl= . 0.0)  +nan.0]
                 [(x . fl< . 0.25)  (fl/ s (fltan (fl* pi x)))]
                 [else  (fl* s (fltan (fl* pi (fl- 0.5 x))))]))]
        [else  +nan.0]))




;                                                                                                                                
;                                                                                                                                
;                                                                                                                                
;       ;;;  ;;;                                                                     ;;;                   ;;;                   
;      ;       ;                                                                       ;                  ;                      
;      ;       ;                                                                       ;                  ;                      
;    ;;;;;;    ;        ;;;    ; ;;;;   ;     ;  ;;;;;;            ; ;;;      ;;;      ;      ;     ;   ;;;;;;  ;     ;  ; ;;;;  
;      ;       ;       ;   ;   ;;   ;;  ;     ;  ;  ;  ;           ;;   ;    ;   ;     ;       ;   ;;     ;     ;     ;  ;;   ;; 
;      ;       ;      ;     ;  ;     ;  ;     ;  ;  ;  ;           ;     ;  ;     ;    ;       ;   ;      ;     ;     ;  ;     ; 
;      ;       ;      ;     ;  ;     ;  ;     ;  ;  ;  ;    ;;;;   ;     ;  ;     ;    ;       ;   ;      ;     ;     ;  ;     ; 
;      ;       ;      ;     ;  ;     ;  ;     ;  ;  ;  ;           ;     ;  ;     ;    ;        ; ;;      ;     ;     ;  ;     ; 
;      ;       ;      ;     ;  ;     ;  ;     ;  ;  ;  ;           ;     ;  ;     ;    ;        ; ;       ;     ;     ;  ;     ; 
;      ;       ;       ;   ;   ;     ;  ;;   ;;  ;  ;  ;           ;;   ;    ;   ;     ;         ;;       ;     ;;   ;;  ;     ; 
;      ;        ;;;     ;;;    ;     ;   ;;;; ;  ;  ;  ;           ; ;;;      ;;;       ;;;      ;;       ;      ;;;; ;  ;     ; 
;                                                                  ;                             ;                               
;                                                                  ;                             ;                               
;                                                                  ;                           ;;                                
;                                                                                                                                


(define-for-syntax (syntax-list-reverse stx-lst)
  (datum->syntax stx-lst (reverse (syntax->list stx-lst)) stx-lst))

(define-syntax (horner-iter stx)
  (syntax-case stx ()
    [(_ y z ())  (syntax/loc stx y)]
    [(_ y z (c0 c ...))
     (syntax/loc stx
       (horner-iter (fl+ (fl* y z) c0) z (c ...)))]))

(define-syntax (make-flpolyfun stx)
  (syntax-case stx ()
    [(_ (c0 c ...))
     (with-syntax ([(c0 c ...)  (syntax-list-reverse #'(c0 c ...))])
       (syntax/loc stx
         (λ: ([z : Float])
           (horner-iter c0 z (c ...)))))]))

(define-syntax (make-even-flpolyfun stx)
  (syntax-case stx ()
    [(_ (c0:expr c ...))
     (syntax/loc stx
       (λ: ([z : Float])
         ((make-flpolyfun (c0 c ...)) (fl* z z))))]))

(define-syntax (make-odd-flpolyfun stx)
  (syntax-case stx ()
    [(_ (c0 c ...))
     (syntax/loc stx
       (λ: ([z : Float])
         (fl+ c0 (fl* z ((make-polyfun (c ...)) (fl* z z))))))]))

(define-syntax (make-quotient-flpolyfun stx)
  (syntax-case stx ()
    [(_ (a ...) (b ...))
     (with-syntax ([(a-rev ...)  (syntax-list-reverse #'(a ...))]
                   [(b-rev ...)  (syntax-list-reverse #'(b ...))])
       (syntax/loc stx
         (λ: ([z : Float])
           (cond [((flabs z) . fl<= . 1.0)
                  (fl/ ((make-flpolyfun (a ...)) z)
                       ((make-flpolyfun (b ...)) z))]
                 [else
                  (let ([z  (fl/ 1.0 z)])
                    (fl/ ((make-flpolyfun (a-rev ...)) z)
                         ((make-flpolyfun (b-rev ...)) z)))]))))]))



;                                                                                            
;                                                                                            
;                                                                                            
;       ;;;  ;;;                                                                             
;      ;       ;                                                                             
;      ;       ;                                                                             
;    ;;;;;;    ;        ;;;    ; ;;;;   ;     ;  ;;;;;;              ;;;    ;;   ;;  ; ;;;   
;      ;       ;       ;   ;   ;;   ;;  ;     ;  ;  ;  ;            ;   ;    ;   ;   ;;   ;  
;      ;       ;      ;     ;  ;     ;  ;     ;  ;  ;  ;           ;     ;    ; ;    ;     ; 
;      ;       ;      ;     ;  ;     ;  ;     ;  ;  ;  ;    ;;;;   ;     ;     ;     ;     ; 
;      ;       ;      ;     ;  ;     ;  ;     ;  ;  ;  ;           ;;;;;;;     ;     ;     ; 
;      ;       ;      ;     ;  ;     ;  ;     ;  ;  ;  ;           ;          ; ;    ;     ; 
;      ;       ;       ;   ;   ;     ;  ;;   ;;  ;  ;  ;            ;    ;   ;   ;   ;;   ;  
;      ;        ;;;     ;;;    ;     ;   ;;;; ;  ;  ;  ;             ;;;;   ;;   ;;  ; ;;;   
;                                                                                    ;       
;                                                                                    ;       
;                                                                                    ;       
;                                                                                            

(define expm1-poly-numer
  (make-flpolyfun
   (-0.28127670288085937e-1
     0.51278186299064534e0
    -0.6310029069350198e-1
     0.11638457975729296e-1
    -0.52143390687521003e-3
     0.21491399776965688e-4)))

(define expm1-poly-denom
  (make-flpolyfun
   ( 1.0
    -0.45442309511354755e0
     0.90850389570911714e-1
    -0.10088963629815502e-1
     0.63003407478692265e-3
    -0.17976570003654402e-4)))

(: flexpm1/poly (Float -> Float))
(define (flexpm1/poly x)
  ;; Define negative in terms of positive to avoid cancellation error
  (cond [(x . fl< . 0.0)  (define y (flexpm1/poly (- x)))
                          (fl/ (- y) (fl+ y 1.0))]
        [else  (fl+ (fl* x 0.10281276702880859e1)
                    (fl* x (fl/ (expm1-poly-numer x) (expm1-poly-denom x))))]))

;; Integer arguments for flexp2
(: flexp2s (U #f (Vectorof Nonnegative-Flonum)))
(define flexp2s #f)

(define (build-flexp2s)
  (: new-flexp2s (Vectorof Nonnegative-Flonum))
  (define new-flexp2s (build-vector (- 1024 -1074) (λ: ([n : Index]) (fl (expt 2 (- n 1074))))))
  (set! flexp2s new-flexp2s)
  new-flexp2s)


  (: flexpm1 (Float -> Float))
  ;; Computes exp(x)-1 in a way that is accurate for small x
  (define (flexpm1 x)
    (define ax (flabs x))
    (cond [(ax . fl>= . 0.5)  (fl- (flexp x) 1.0)]
          [(ax . fl> . (fl* 0.5 epsilon.0))  (flexpm1/poly x)]
          [else  x]))
  
  (: flgauss (Flonum -> Flonum))
  ;; Computes exp(-x^2) in a way that is accurate for large x
  (define (flgauss x)
    (let ([x  (flabs x)])
      (cond [(x . fl> . 28.0)  0.0]
            [(x . fl> . 1.0)
             ;; Split x into a flonum with 21 high-order fractional bits and a part with the rest
             ;; Sometime after p > 26.1, (exp (- (* p p))) outputs subnormals, so we don't go there
             (define p (flmin 26.0 (fl/ (fltruncate (fl* (flexpt 2.0 21.0) x)) (flexpt 2.0 21.0))))
             (define q (fl- x p))
             (fl* (fl* (flexp (- (fl* 2.0 (fl* p q))))
                       (flexp (- (fl* q q))))
                  (flexp (- (fl* p p))))]
            [else
             (flexp (- (fl* x x)))])))
  
  (: flexpsqr (Flonum -> Flonum))
  ;; Computes exp(x^2) in a way that is accurate for large x
  (define (flexpsqr x)
    (let ([x  (flabs x)])
      (cond [(x . fl> . 27.0)  +inf.0]
            [(x . fl> . 1.0)
             (define p (fl/ (fltruncate (fl* (flexpt 2.0 21.0) x)) (flexpt 2.0 21.0)))
             (define q (fl- x p))
             (fl* (fl* (flexp (fl* 2.0 (fl* p q)))
                       (flexp (fl* q q)))
                  (flexp (fl* p p)))]
            [else
             (flexp (fl* x x))])))
  
  (: flexp1p (Flonum -> Flonum))
  ;; Computes exp(1+x) in a way that is accurate near powers of 2
  (define (flexp1p x)
    (cond [(x . fl< . -0.5)  (flexp (fl+ 1.0 x))]
          [else
           (define lg2x (flfloor (fl/ (fllog x) (fllog 2.0))))
           (define lg2x+1 (flfloor (fl/ (fllog (fl+ 1.0 x)) (fllog 2.0))))
           (cond [(fl= lg2x lg2x+1)  (flexp (fl+ 1.0 x))]
                 [else  (fl* (flexp x) (flexp 1.0))])]))
  
  (: flexp2 (Flonum -> Nonnegative-Flonum))
  ;; Computes 2^x
  (define (flexp2 x)
    (cond [(fl<= x -1075.0)  0.0]
          [(fl>= x 1024.0)  +inf.0]
          [(fl= x (flround x))
           (let* ([flexp2s  flexp2s]
                  [flexp2s  (if flexp2s flexp2s (build-flexp2s))])
             (vector-ref flexp2s (fl->exact-integer (fl+ x 1074.0))))]
          [else  (flexpt 2.0 x)]))
  
  (: flpow2near (-> Flonum Flonum))
  (define (flpow2near a)
    (flexp2 (flmax -1074.0 (flmin 1023.0 (flround (fl/ (fllog (flabs a)) (fllog 2.0)))))))



;                                                                                                                                                                             
;                                                                                                                                                                             
;                                                                                                                                                                             
;       ;;;  ;;;                                                   ;                                                           ;           ;        ;                         
;      ;       ;                                                   ;                                     ;                     ;           ;        ;                         
;      ;       ;                                                   ;                                     ;                     ;           ;        ;                         
;    ;;;;;;    ;        ;;;    ; ;;;;   ;     ;  ;;;;;;            ; ;;;      ; ;;;    ;;;    ; ;;;;   ;;;;;;              ;;; ;    ;;;    ;    ;   ;    ;     ;;;      ; ;;; 
;      ;       ;       ;   ;   ;;   ;;  ;     ;  ;  ;  ;           ;;   ;     ;;   ;  ;   ;   ;;   ;;    ;                ;   ;;   ;   ;   ;  ;;    ;  ;;     ;   ;     ;;   ;
;      ;       ;      ;     ;  ;     ;  ;     ;  ;  ;  ;           ;     ;    ;      ;     ;  ;     ;    ;               ;     ;  ;     ;  ; ;      ; ;      ;     ;    ;     
;      ;       ;      ;     ;  ;     ;  ;     ;  ;  ;  ;    ;;;;   ;     ;    ;      ;     ;  ;     ;    ;        ;;;;   ;     ;  ;     ;  ;;;      ;;;      ;     ;    ;     
;      ;       ;      ;     ;  ;     ;  ;     ;  ;  ;  ;           ;     ;    ;      ;;;;;;;  ;     ;    ;               ;     ;  ;;;;;;;  ;  ;     ;  ;     ;;;;;;;    ;     
;      ;       ;      ;     ;  ;     ;  ;     ;  ;  ;  ;           ;     ;    ;      ;        ;     ;    ;               ;     ;  ;        ;   ;    ;   ;    ;          ;     
;      ;       ;       ;   ;   ;     ;  ;;   ;;  ;  ;  ;           ;;   ;     ;       ;    ;  ;     ;    ;                ;   ;;   ;    ;  ;    ;   ;    ;    ;    ;    ;     
;      ;        ;;;     ;;;    ;     ;   ;;;; ;  ;  ;  ;           ; ;;;      ;        ;;;;   ;     ;     ;;;              ;;; ;    ;;;;   ;     ;  ;     ;    ;;;;     ;     
;                                                                                                                                                                             
;                                                                                                                                                                             
;                                                                                                                                                                             
;                                                                                                                                                                             

(: flbracketed-root* (-> (-> Flonum Flonum) Flonum Flonum Flonum Flonum Flonum))
(define (flbracketed-root* f a fa b fb)
  (let loop ([bisected? #t] [a a] [fa fa] [b b] [fb fb] [c a] [fc fa] [d 0.0] [n 0])
    (define min-abs-ab (min (abs a) (abs b)))
    (define ε (if (min-abs-ab . <= . +max-subnormal.0) +min.0 (* min-abs-ab epsilon.0)))
    (cond
      ;; If we got it right, return it
      [(= fb 0.0)  b]
      ;; If a and b are too close, return b
      [((abs (- a b)) . <= . ε)
       b]
      [(n . < . 5000)
       (let*-values
           ([(bisect? s)
             (cond
               ;; Weird rules for forcing bisection to make progress
               [(or (and bisected?       ((abs (- b c)) . < . (* 128.0 ε)))
                    (and (not bisected?) ((abs (- c d)) . < . (* 128.0 ε))))
                (values #t 0.0)]
               ;; Get an interpolated point
               [else
                (define fa-fb (- fa fb))
                (define fb-fc (- fb fc))
                (define fc-fa (- fc fa))
                (define da (* fa-fb (- fc-fa)))
                (define db (* fb-fc (- fa-fb)))
                (define dc (* fc-fa (- fb-fc)))
                (cond [(or (= da 0.0) (= db 0.0) (= dc 0.0))
                       ;; Secant method because quadratic method will fail
                       (values #f (- b (* fb (/ (- b a) (- fa-fb)))))]
                      [else
                       ;; Inverse quadratic interpolation method
                       (values #f (+ (/ (* a fb fc) da)
                                     (/ (* b fc fa) db)
                                     (/ (* c fa fb) dc)))])])]
            ;; Run tests to determine whether it's a bad point
            [(bisected? s)
             (cond
               [(or bisect?
                    (and (not (let ([s0  (/ (+ (* 3.0 a) b) 4.0)])
                                (if (<= s0 b) (<= s0 s b) (<= b s s0)))))
                    (and bisected?       ((abs (- s b)) . >= . (* 0.5 (abs (- b c)))))
                    (and (not bisected?) ((abs (- s b)) . >= . (* 0.5 (abs (- c d))))))
                ;; Bisect this time
                (values #t (* 0.5 (+ a b)))]
               [else
                (values #f s)])]
            [(d)  c]
            [(c fc)  (values b fb)]
            [(fs)  (f s)]
            ;; Replace the endpoint with the same sign as s
            [(a fa b fb)  (if ((* fa fs) . < . 0.0)
                              (values a fa s fs)
                              (values s fs b fb))]
            ;; Make sure b is closer
            [(a fa b fb)  (if ((abs fa) . < . (abs fb))
                              (values b fb a fa)
                              (values a fa b fb))])
         (loop bisected? a fa b fb c fc d (+ n 1)))]
      [else  b])))

(: flbracketed-root (-> (-> Flonum Flonum) Flonum Flonum Flonum))
;; Find a root between a and b if f(a) and f(b) have opposite signs
(define (flbracketed-root f a b)
  (define fa (f a))
  (define fb (f b))
  (cond [(= fa 0.0)  a]
        [(= fb 0.0)  b]
        [(or (flnan? a) (flnan? fa) (flnan? b) (flnan? fb))  +nan.0]
        ;; Check signs
        [((* fa fb) . >= . 0.0)
         +nan.0]
        [else
         (let*-values
             ([(a fa)  (cond [(= a -inf.0)  (values -max.0 (f -max.0))]
                             [(= a +inf.0)  (values +max.0 (f +max.0))]
                             [else  (values a fa)])]
              [(b fb)  (cond [(= b -inf.0)  (values -max.0 (f -max.0))]
                             [(= b +inf.0)  (values +max.0 (f +max.0))]
                             [else  (values b fb)])]
              ;; Make sure b is closer
              [(a fa b fb)  (if ((abs fa) . < . (abs fb))
                                (values b fb a fa)
                                (values a fa b fb))])
           (flbracketed-root* f a fa b fb))]))




;                                                                                                                       
;                                                                                                                       
;                                                                                                                       
;       ;;;  ;;;                                                                                                ;       
;      ;       ;                                                                                                ;       
;      ;       ;                                                                                                ;       
;    ;;;;;;    ;        ;;;    ; ;;;;   ;     ;  ;;;;;;             ;;;;;     ;;;      ;;;;     ; ;;;    ;;;    ; ;;;;  
;      ;       ;       ;   ;   ;;   ;;  ;     ;  ;  ;  ;           ;     ;   ;   ;    ;    ;    ;;   ;  ;   ;   ;;   ;; 
;      ;       ;      ;     ;  ;     ;  ;     ;  ;  ;  ;           ;        ;     ;        ;    ;      ;        ;     ; 
;      ;       ;      ;     ;  ;     ;  ;     ;  ;  ;  ;    ;;;;   ;;;;     ;     ;   ;;;;;;    ;      ;        ;     ; 
;      ;       ;      ;     ;  ;     ;  ;     ;  ;  ;  ;              ;;;;  ;;;;;;;  ;;    ;    ;      ;        ;     ; 
;      ;       ;      ;     ;  ;     ;  ;     ;  ;  ;  ;                 ;  ;        ;     ;    ;      ;        ;     ; 
;      ;       ;       ;   ;   ;     ;  ;;   ;;  ;  ;  ;           ;     ;   ;    ;  ;    ;;    ;       ;   ;   ;     ; 
;      ;        ;;;     ;;;    ;     ;   ;;;; ;  ;  ;  ;            ;;;;;     ;;;;    ;;;; ;    ;        ;;;    ;     ; 
;                                                                                                                       
;                                                                                                                       
;                                                                                                                       
;                                                                                                                       


(: find-least-flonum (case-> ((Flonum -> Any) Flonum -> (U Flonum #f))
                             ((Flonum -> Any) Flonum Flonum -> (U Flonum #f))))

(define find-least-flonum
  (case-lambda
    [(pred? x-start)
     (when (eqv? +nan.0 x-start)
       (raise-argument-error 'find-least-flonum "non-NaN Flonum" 1 pred? x-start))
     (let loop ([n-end  (flonum->ordinal x-start)] [step 1])
       (define x-end (ordinal->flonum n-end))
       (cond [(pred? x-end)  (find-least-flonum pred? x-start x-end)]
             [(fl= x-end +inf.0)  #f]
             [else  (loop (min +inf-ordinal (+ n-end step)) (* step 2))]))]
    [(pred? x-start x-end)
     (when (eqv? x-start +nan.0)
       (raise-argument-error 'find-least-flonum "non-NaN Flonum" 1 pred? x-start x-end))
     (when (eqv? x-end +nan.0)
       (raise-argument-error 'find-least-flonum "non-NaN Flonum" 2 pred? x-start x-end))
     (cond [(pred? x-start)  x-start]
           [(not (pred? x-end))  #f]
           [else
            (let loop ([n-start  (flonum->ordinal x-start)] [n-end  (flonum->ordinal x-end)])
              (cond [(= n-start n-end)  (define x (ordinal->flonum n-end))
                                        (if (pred? x) x #f)]
                    [else
                     (define n-mid (quotient (+ n-start n-end) 2))
                     (cond [(pred? (ordinal->flonum n-mid))
                            (loop n-start n-mid)]
                           [else
                            (loop (+ n-mid 1) n-end)])]))])]))

(: sub-or-prev (Flonum Flonum -> Flonum))
(define (sub-or-prev k i)
  (define prev-k (fl- k i))
  (if (fl= prev-k k) (flprev* k) prev-k))

(: add-or-next (Flonum Flonum -> Flonum))
(define (add-or-next k i)
  (define next-k (fl+ k i))
  (if (fl= next-k k) (flnext* k) next-k))

(: flmidpoint (Flonum Flonum -> Flonum))
(define (flmidpoint x y)
  (let ([x  (flmin x y)]
        [y  (flmax x y)])
    (cond [(fl= x -inf.0)  (cond [(fl= y +inf.0)  0.0]
                                 [(fl= y -inf.0)  -inf.0]
                                 [else  (+ (* 0.5 -max.0) (* 0.5 y))])]
          [(fl= y +inf.0)  (cond [(fl= x +inf.0)  +inf.0]
                                 [else  (+ (* 0.5 x) (* 0.5 +max.0))])]
          [else  (+ (* 0.5 x) (* 0.5 y))])))

(: flfind-least-integer (case-> ((Flonum -> Any) -> Flonum)
                                ((Flonum -> Any) Flonum -> Flonum)
                                ((Flonum -> Any) Flonum Flonum -> Flonum)
                                ((Flonum -> Any) Flonum Flonum Flonum -> Flonum)))
;; Finds the least integer k such that (pred? k) is #t, given optional bounds and an optional
;; initial estimate. If the predicate is not monotone in the bounds, the result of this function is
;; indeterminate, and depends in an unspecified way on the initial estimate.
;; Formally, to get a unique answer, one of the following cases must be true.
;;  1. Exists k, forall mn <= i < k, (pred? i) is #f /\ forall k <= j <= mx, (pred? j) is #t
;;  2. Forall k, (pred? k) is #f
;;  3. Forall k, (pred? k) is #t
;; where mn0 <= k <= mx0. For case #1, this function returns k. For case #2, it returns +nan.0. For
;; case #3, it returns mn0.
(define (flfind-least-integer pred? [mn0 -inf.0] [mx0 +inf.0] [k0 +nan.0])
  (let ([mn  (flceiling (flmin mn0 mx0))]
        [mx  (flfloor (flmax mn0 mx0))])
    ;; Make sure the initial estimate is in-bounds
    (define k (cond [(and (k0 . >= . mn) (k0 . <= . mx))  (flfloor k0)]
                    [else  (flfloor (flmidpoint mn mx))]))
    (define k? (pred? k))
    ;; Find an integer k-min <= k for which (pred? k-min) is #f; increment exponentially
    (define-values (k-min k-min?)
      (let: loop : (Values Flonum Any) ([k-min : Flonum  k] [k-min? : Any  k?] [i : Flonum  1.0])
        ;(printf "min: ~v~n" k-min)
        (cond [(k-min . fl<= . mn)  (cond [(fl= k-min mn)  (values k-min k-min?)]
                                          [else  (values mn (pred? mn))])]
              [k-min?  (define prev-k-min (sub-or-prev k-min i))
                       (loop prev-k-min (pred? prev-k-min) (* 2.0 (- k-min prev-k-min)))]
              [else  (values k-min #f)])))
    ;; Find an integer k-max >= k0 for which (pred? k-max) is #t; increment exponentially
    (define-values (k-max k-max?)
      (let: loop : (Values Flonum Any) ([k-max : Flonum  k] [k-max? : Any  k?] [i : Flonum  1.0])
        ;(printf "max: ~v~n" k-max)
        (cond [(k-max . fl>= . mx)  (cond [(fl= k-max mx)  (values k-max k-max?)]
                                          [else  (values mx (pred? mx))])]
              [k-max?  (values k-max #t)]
              [else  (define next-k-max (add-or-next k-max i))
                     (loop next-k-max (pred? next-k-max) (* 2.0 (- next-k-max k-max)))])))
    ;; Quickly check cases #2 and #3; if case #1, do a binary search
    (cond [(not k-max?)  +nan.0]
          [k-min?  mn]
          [else
           ;; Loop invariant: (pred? k-max) is #t and (pred? k-min) is #f
           (let loop ([k-min k-min] [k-max k-max])
             ;(printf "~v ~v~n" k-min k-max)
             (define k (flfloor (flmidpoint k-min k-max)))
             ;; Check whether k-min + 1 = k-max or (flnext k-min) = k-max
             (cond [(or (= k k-min) (= k k-max))  k-max]
                   [(pred? k)  (loop k-min k)]
                   [else  (loop k k-max)]))])))



;                                                                                                              
;                                                                                                              
;                                                                                                              
;       ;;;  ;;;                                                                                               
;      ;       ;                                                                                               
;      ;       ;                                                                                               
;    ;;;;;;    ;        ;;;    ; ;;;;   ;     ;  ;;;;;;              ;;;      ; ;;;    ; ;;;    ;;;      ; ;;; 
;      ;       ;       ;   ;   ;;   ;;  ;     ;  ;  ;  ;            ;   ;     ;;   ;   ;;   ;  ;   ;     ;;   ;
;      ;       ;      ;     ;  ;     ;  ;     ;  ;  ;  ;           ;     ;    ;        ;      ;     ;    ;     
;      ;       ;      ;     ;  ;     ;  ;     ;  ;  ;  ;    ;;;;   ;     ;    ;        ;      ;     ;    ;     
;      ;       ;      ;     ;  ;     ;  ;     ;  ;  ;  ;           ;;;;;;;    ;        ;      ;     ;    ;     
;      ;       ;      ;     ;  ;     ;  ;     ;  ;  ;  ;           ;          ;        ;      ;     ;    ;     
;      ;       ;       ;   ;   ;     ;  ;;   ;;  ;  ;  ;            ;    ;    ;        ;       ;   ;     ;     
;      ;        ;;;     ;;;    ;     ;   ;;;; ;  ;  ;  ;             ;;;;     ;        ;        ;;;      ;     
;                                                                                                              
;                                                                                                              
;                                                                                                              
;                                                                                                              


(define-syntax-rule (near-pow2 a)
  (flexpt 2.0 (flmax -1023.0 (flmin 1023.0 (flround (fl/ (fllog (flabs a)) (fllog 2.0)))))))

(define-syntax-rule (near-pow2/div a b)
  ;; Clamping both values makes this work properly when a or b is infinite or zero
  (let ([ea  (flmax -511.0 (flmin 511.0 (fl/ (fllog (flabs a)) (fllog 2.0))))]
        [eb  (flmax -511.0 (flmin 511.0 (fl/ (fllog (flabs b)) (fllog 2.0))))])
    (flexpt 2.0 (flround (fl* 0.5 (fl+ ea eb))))))

;(: flsplit (Flonum -> (Values Flonum Flonum)))
;; Splits a flonum into a two flonums `hi' and `lo' with 26 bits precision each, such that
;; |hi| >= |lo| and hi + lo = a. (The extra sign bit accounts for the missing bit.)
;; This function returns (values +nan.0 +nan.0) for |a| >= 1.3393857490036326e+300.
(define-syntax-rule (flsplit a-expr)
  (let ([a a-expr])
    (let* ([c   (fl* a (fl+ 1.0 (flexpt 2.0 27.0)))]
           [x2  (fl- c (fl- c a))])
      (values x2 (fl- a x2)))))

;; =================================================================================================
;; Fast monotone addition and subtraction

;(: fast-mono-fl+/error (Flonum Flonum -> (Values Flonum Flonum)))
;; Returns a+b and its rounding error
;; Assumes |a| >= |b|
(define-syntax-rule (fast-mono-fl+/error a-expr b-expr)
  (let ([a a-expr] [b b-expr])
    (let ([x2  (+ a b)])
      (values x2 (- b (- x2 a))))))

;(: fast-mono-fl-/error (Flonum Flonum -> (Values Flonum Flonum)))
;; Returns a+b and its rounding error
;; Assumes |a| >= |b|
(define-syntax-rule (fast-mono-fl-/error a-expr b-expr)
  (let ([a a-expr] [b b-expr])
    (let ([x2  (- a b)])
      (values x2 (- (- a x2) b)))))

;; =================================================================================================
;; Fast arithmetic that returns rounding error

;(: fast-fl+/error (Flonum Flonum -> (Values Flonum Flonum)))
;; Returns a+b and its rounding error
(define-syntax-rule (fast-fl+/error a-expr b-expr)
  (let ([a a-expr] [b b-expr])
    (let* ([x2  (fl+ a b)]
           [v   (fl- x2 a)])
      (values x2 (fl+ (fl- a (fl- x2 v)) (fl- b v))))))

;(: fast-fl-/error (Flonum Flonum -> (Values Flonum Flonum)))
;; Returns a-b and its rounding error
(define-syntax-rule (fast-fl-/error a-expr b-expr)
  (let ([a a-expr] [b b-expr])
    (let* ([x2  (fl- a b)]
           [v   (fl- x2 a)])
      (values x2 (fl- (fl- a (fl- x2 v)) (fl+ b v))))))

;(: fast-fl*/error (Flonum Flonum -> (Values Flonum Flonum)))
;; Returns a*b and its rounding error
(define-syntax-rule (fast-fl*/error a-expr b-expr)
  (let ([a a-expr] [b b-expr])
    (let*-values ([(x2)  (fl* a b)]
                  [(a2 a1)  (flsplit a)]
                  [(b2 b1)  (flsplit b)])
      (values x2 (- (fl- (fl- (fl- (fl- x2 (fl* a2 b2))
                                   (fl* a1 b2))
                              (fl* a2 b1))
                         (fl* a1 b1)))))))

;(: fast-flfma/error (Flonum Flonum Flonum -> (Values Flonum Flonum)))
;; Returns a*b+c and its rounding error
(define-syntax-rule (fast-flfma/error a-expr b-expr c-expr)
  (let*-values ([(y2 y1)  (fast-fl*/error a-expr b-expr)]
                [(h0 h1)  (fast-fl+/error c-expr y1)]
                [(h3 h2)  (fast-fl+/error h0 y2)])
    (values h3 (fl+ h2 h1))))

;(: fast-flfsa/error (Flonum Flonum Flonum -> (Values Flonum Flonum)))
;; Returns a*a+b and its rounding error
(define-syntax-rule (fast-flfsa/error a-expr b-expr)
  (let*-values ([(y2 y1)  (fast-flsqr/error a-expr)]
                [(h0 h1)  (fast-fl+/error b-expr y1)]
                [(h3 h2)  (fast-fl+/error h0 y2)])
    (values h3 (fl+ h2 h1))))

#;; If we had hardware fused multiply-add:
(define-syntax-rule (fast-fl*/error a-expr b-expr)
  (let ([a a-expr] [b b-expr])
    (let ([x2  (fl* a b)])
      (values x2 (flfma a b (- x2))))))

;(: fast-flsqr/error (Flonum -> (Values Flonum Flonum)))
;; Returns a*a and its rounding error
(define-syntax-rule (fast-flsqr/error a-expr)
  (let ([a a-expr])
    (let*-values ([(x2)  (fl* a a)]
                  [(a2 a1)  (flsplit a)])
      (values x2 (- (fl- (fl- (fl- x2 (fl* a2 a2))
                              (fl* 2.0 (fl* a2 a1)))
                         (fl* a1 a1)))))))

;(: fast-fl//error (Flonum Flonum -> (Values Flonum Flonum)))
;; Returns a/b and its rounding error
(define-syntax-rule (fast-fl//error a-expr b-expr)
  (let ([a a-expr] [b b-expr])
    (let*-values ([(x2)  (fl/ a b)]
                  [(w2 w1)  (fast-fl*/error x2 b)])
      (fast-mono-fl+/error x2 (fl/ (fl- (fl- a w2) w1) b)))))


(: fl+/error (Flonum Flonum -> (Values Flonum Flonum)))
(define (fl+/error a b)
  (let-values ([(x2 x1)  (fast-fl+/error a b)])
    (values x2 (if (flrational? x2) x1 0.0))))

(: fl-/error (Flonum Flonum -> (Values Flonum Flonum)))
(define (fl-/error a b)
  (let-values ([(x2 x1)  (fast-fl-/error a b)])
    (values x2 (if (flrational? x2) x1 0.0))))

(: fl*/error (Flonum Flonum -> (Values Flonum Flonum)))
(define (fl*/error a b)
  (let ([x2  (fl* a b)])
    (values x2 (if (and (flrational? x2) (not (flsubnormal? x2)))
                   (let*-values ([(da db)  (values (near-pow2 a) (near-pow2 b))]
                                 [(d)  (fl* da db)]
                                 [(d?)  (and (d . fl> . 0.0) (d . fl< . +inf.0))]
                                 [(a2 a1)  (flsplit (fl/ a da))]
                                 [(b2 b1)  (flsplit (fl/ b db))]
                                 [(x2)  (if d? (fl/ x2 d) (fl/ (fl/ x2 da) db))]
                                 [(x1)  (- (fl- (fl- (fl- (fl- x2 (fl* a2 b2))
                                                          (fl* a1 b2))
                                                     (fl* a2 b1))
                                                (fl* a1 b1)))])
                     (if d? (fl* x1 d) (fl* (fl* x1 da) db)))
                   0.0))))

(: flsqr/error (Flonum -> (Values Flonum Flonum)))
(define (flsqr/error a)
  (let ([x2  (fl* a a)])
    (values x2 (if (and (flrational? x2) (not (flsubnormal? x2)))
                   (let*-values ([(d)  (near-pow2 a)]
                                 [(d^2)  (fl* d d)]
                                 [(d^2?)  (and (d^2 . fl> . 0.0) (d^2 . fl< . +inf.0))]
                                 [(a2 a1)  (flsplit (fl/ a d))]
                                 [(x2)  (if d^2? (fl/ x2 d^2) (fl/ (fl/ x2 d) d))]
                                 [(x1)  (- (fl- (fl- (fl- x2 (fl* a2 a2))
                                                     (fl* 2.0 (fl* a1 a2)))
                                                (fl* a1 a1)))])
                     (if d^2? (fl* x1 d^2) (fl* (fl* x1 d) d)))
                   0.0))))

(: fl//error (Flonum Flonum -> (Values Flonum Flonum)))
(define (fl//error a b)
  (let ([x2  (fl/ a b)])
    (values x2 (if (and (flrational? x2) (flrational? b))
                   (let* ([d  (near-pow2/div a b)]
                          [a  (fl/ a d)]
                          [b  (fl/ b d)])
                     (let-values ([(w2 w1)  (fl*/error x2 b)])
                       (fl/ (fl- (fl- a w2) w1) b)))
                   0.0))))

(: flfma/error (-> Flonum Flonum Flonum (Values Flonum Flonum)))
(define (flfma/error a b c)
  (define-values (x2 x1) (fast-flfma/error a b c))
  (cond [(flrational? (+ x2 x1))  (values x2 x1)]
        [else
         (define n (near-pow2 (max (flsqrt (abs a)) (flsqrt (abs b)))))
         (define 1/n (/ 1.0 n))
         (define n^2 (* n n))
         (let-values ([(x2 x1)  (fast-flfma/error (* a 1/n) (* b 1/n) (* c 1/n 1/n))])
           (values (* n^2 x2) (* n^2 x1)))]))

(: flfsa/error (-> Flonum Flonum (Values Flonum Flonum)))
(define (flfsa/error a b)
  (define-values (x2 x1) (fast-flfsa/error a b))
  (cond [(flrational? (+ x2 x1))  (values x2 x1)]
        [else
         (define n (near-pow2 (flsqrt (abs a))))
         (define 1/n (/ 1.0 n))
         (define n^2 (* n n))
         (let-values ([(x2 x1)  (fast-flfsa/error (* a 1/n) (* b 1/n 1/n))])
           (values (* n^2 x2) (* n^2 x1)))]))




;                                                                                                              
;                                                                                                              
;                                                                                                              
;                                                                                       ;     ;;;              
;                                ;                                            ;         ;       ;              
;                                ;                                            ;                 ;              
;    ;;;;;   ;     ;  ; ;;;;   ;;;;;;     ;;;;   ;;   ;;           ;     ;  ;;;;;;    ;;;       ;       ;;;;;  
;   ;     ;   ;   ;;  ;;   ;;    ;       ;    ;   ;   ;            ;     ;    ;         ;       ;      ;     ; 
;   ;         ;   ;   ;     ;    ;            ;    ; ;             ;     ;    ;         ;       ;      ;       
;   ;;;;      ;   ;   ;     ;    ;       ;;;;;;     ;       ;;;;   ;     ;    ;         ;       ;      ;;;;    
;      ;;;;    ; ;;   ;     ;    ;      ;;    ;     ;              ;     ;    ;         ;       ;         ;;;; 
;         ;    ; ;    ;     ;    ;      ;     ;    ; ;             ;     ;    ;         ;       ;            ; 
;   ;     ;     ;;    ;     ;    ;      ;    ;;   ;   ;            ;;   ;;    ;         ;       ;      ;     ; 
;    ;;;;;      ;;    ;     ;     ;;;    ;;;; ;  ;;   ;;            ;;;; ;     ;;;   ;;;;;;;     ;;;    ;;;;;  
;               ;                                                                                              
;               ;                                                                                              
;             ;;                                                                                               
;                                                                                                              


(define-syntax-rule (define-inline-op name inline-op typed-op inline-pats ...)
  (define-syntax (name stx)
    (syntax-case stx ()
      [(_ . inline-pats)  (syntax/loc stx (inline-op . inline-pats))] ...
      [(_ . args)  (syntax/loc stx (typed-op . args))]
      [_  (syntax/loc stx typed-op)])))


(define-syntax-rule (ensure-index name n-expr)
  (let: ([n : Integer  n-expr])
    (if (index? n) n (raise-argument-error name "Index" n))))

(define-syntax-rule (ensure-flvector name xs-expr)
  (let: ([xs : FlVector  xs-expr])
    (if (flvector? xs) xs (raise-argument-error name "FlVector" xs))))

(define-syntax-rule (ensure-procedure name f-expr T)
  (let: ([f : T  f-expr])
    (if (procedure? f) f (raise-argument-error name "Procedure" f))))



(: raise-length-error (Symbol String Any Index -> Nothing))
(define (raise-length-error name type-name xs n)
  (raise-argument-error name (format "~a of length ~a" type-name n) xs))


(define-syntax (unsafe-flvector-fill! stx)
  (syntax-case stx ()
    [(_ xs n f-expr)
     (syntax/loc stx
       (let: loop : FlVector ([i : Nonnegative-Fixnum  0])
         (if (i . unsafe-fx< . n)
             (begin (unsafe-flvector-set! xs i (f-expr i))
                    (loop (unsafe-fx+ i 1)))
             xs)))]))

(define-syntax (inline-build-flvector stx)
  (syntax-case stx ()
    [(_ n-expr f-expr)
     (syntax/loc stx
       (let*: ([xs : FlVector  (make-flvector (ann n-expr Integer))]
               [n  : Index     (flvector-length xs)])
         (unsafe-flvector-fill! xs n (ann f-expr (Index -> Flonum)))))]))

(define-syntax (inline-flvector-map stx)
  (syntax-case stx ()
    [(_ f-expr xs-expr)
     (syntax/loc stx
       (let*: ([xs : FlVector  xs-expr]
               [n  : Index     (flvector-length xs)])
         (define-syntax-rule (new-f i)
           ((ann f-expr (Flonum -> Flonum)) (unsafe-flvector-ref xs i)))
         (define ys (make-flvector n))
         (unsafe-flvector-fill! ys n new-f)))]
    [(_ f-expr xs-expr xss-expr ...)
     (with-syntax ([(f)  (generate-temporaries #'(f-expr))]
                   [(xs xss ...)  (generate-temporaries #'(xs-expr xss-expr ...))]
                   [(n ns ...)    (generate-temporaries #'(xs-expr xss-expr ...))]
                   [(Flonums ...)  (build-list (length (syntax->list #'(xs-expr xss-expr ...)))
                                               (λ _ #'Flonum))])
       (syntax/loc stx
         (let*: ([xs : FlVector   xs-expr]
                 [n  : Index      (flvector-length xs)]
                 [xss : FlVector  xss-expr] ...)
           (define-syntax-rule (new-f i)
             ((ann f-expr (Flonums ... -> Flonum)) (unsafe-flvector-ref xs i)
                                                   (unsafe-flvector-ref xss i) ...))
           (define ys (make-flvector n))
           (unsafe-flvector-fill! ys n new-f))))]))



;                                                                          
;                                                                          
;                                                                          
;       ;;;  ;;;                                                           
;      ;       ;                                   ;                       
;      ;       ;                                   ;                       
;    ;;;;;;    ;      ;     ;    ;;;      ;;;    ;;;;;;     ;;;      ; ;;; 
;      ;       ;       ;   ;    ;   ;    ;   ;     ;       ;   ;     ;;   ;
;      ;       ;       ;   ;   ;     ;  ;          ;      ;     ;    ;     
;      ;       ;       ;   ;   ;     ;  ;          ;      ;     ;    ;     
;      ;       ;        ; ;    ;;;;;;;  ;          ;      ;     ;    ;     
;      ;       ;        ; ;    ;        ;          ;      ;     ;    ;     
;      ;       ;        ; ;     ;    ;   ;   ;     ;       ;   ;     ;     
;      ;        ;;;      ;       ;;;;     ;;;       ;;;     ;;;      ;     
;                                                                          
;                                                                          
;                                                                          
;; ===================================================================================================
;; flvector-copy!

(: unsafe-flvector-copy! (FlVector Integer FlVector Integer Integer -> Void))
(define (unsafe-flvector-copy! dest dest-start src src-start src-end)
  (let loop ([i dest-start] [j src-start])
    (when (j . unsafe-fx< . src-end)
      (unsafe-flvector-set! dest i (unsafe-flvector-ref src j))
      (loop (unsafe-fx+ i 1) (unsafe-fx+ j 1)))))

(: flvector-copy! (case-> (FlVector Integer FlVector -> Void)
                          (FlVector Integer FlVector Integer -> Void)
                          (FlVector Integer FlVector Integer Integer -> Void)))
(define flvector-copy!
  (case-lambda
    [(dest dest-start src)
     (flvector-copy! dest dest-start src 0 (flvector-length src))]
    [(dest dest-start src src-start)
     (flvector-copy! dest dest-start src src-start (flvector-length src))]
    [(dest dest-start src src-start src-end)
     (define dest-len (flvector-length dest))
     (define src-len (flvector-length src))
     (cond [(or (dest-start . < . 0) (dest-start . > . dest-len))
            (raise-argument-error 'flvector-copy! (format "Index <= ~e" dest-len) 1
                                  dest dest-start src src-start src-end)]
           [(or (src-start . < . 0) (src-start . > . src-len))
            (raise-argument-error 'flvector-copy! (format "Index <= ~e" src-len) 3
                                  dest dest-start src src-start src-end)]
           [(or (src-end . < . 0) (src-end . > . src-len))
            (raise-argument-error 'flvector-copy! (format "Index <= ~e" src-len) 4
                                  dest dest-start src src-start src-end)]
           [(src-end . < . src-start)
            (error 'flvector-copy! "ending index is smaller than starting index")]
           [((- dest-len dest-start) . < . (- src-end src-start))
            (error 'flvector-copy! "not enough room in target vector")]
           [else
            (unsafe-flvector-copy! dest dest-start src src-start src-end)])]))

;; ===================================================================================================
;; Conversion

(: list->flvector ((Listof Real) -> FlVector))
(define (list->flvector vs)
  (for/flvector: #:length (length vs) ([v  (in-list vs)])
    (fl v)))

(: flvector->list (FlVector -> (Listof Float)))
(define (flvector->list xs)
  (for/list: : (Listof Float) ([x  (in-flvector xs)]) x))

(: vector->flvector ((Vectorof Real) -> FlVector))
(define (vector->flvector vs)
  (for/flvector: #:length (vector-length vs) ([v  (in-vector vs)])
    (fl v)))

(: flvector->vector (FlVector -> (Vectorof Float)))
(define (flvector->vector xs)
  (for/vector: #:length (flvector-length xs) ([x  (in-flvector xs)]) : Flonum
    x))

;; ===================================================================================================
;; Pointwise operations

(define-syntax-rule (lift1 f)
  (λ: ([arr : FlVector])
    (inline-flvector-map f arr)))

(define-syntax-rule (lift2 f)
  (λ: ([arr0 : FlVector] [arr1 : FlVector])
    (inline-flvector-map f arr0 arr1)))

(: flvector-scale (FlVector Float -> FlVector))
(define (flvector-scale arr y) (inline-flvector-map (λ: ([x : Flonum]) (fl* x y)) arr))

(: flvector-sqr (FlVector -> FlVector))
(define flvector-sqr (lift1 (λ: ([x : Flonum]) (fl* x x))))

(: flvector-sqrt (FlVector -> FlVector))
(define flvector-sqrt (lift1 flsqrt))

(: flvector-abs (FlVector -> FlVector))
(define flvector-abs (lift1 flabs))

(: flvector+ (FlVector FlVector -> FlVector))
(define flvector+ (lift2 fl+))

(: flvector* (FlVector FlVector -> FlVector))
(define flvector* (lift2 fl*))

(: flvector- (case-> (FlVector -> FlVector)
                     (FlVector FlVector -> FlVector)))
(define flvector-
  (case-lambda:
    [([arr0 : FlVector])
     (inline-flvector-map (λ: ([x : Float]) (fl- 0.0 x)) arr0)]
    [([arr0 : FlVector] [arr1 : FlVector])
     (inline-flvector-map fl- arr0 arr1)]))

(: flvector/ (case-> (FlVector -> FlVector)
                     (FlVector FlVector -> FlVector)))
(define flvector/
  (case-lambda:
    [([arr0 : FlVector])
     (inline-flvector-map (λ: ([x : Float]) (fl/ 1.0 x)) arr0)]
    [([arr0 : FlVector] [arr1 : FlVector])
     (inline-flvector-map fl/ arr0 arr1)]))

(: flvector-min  (FlVector FlVector -> FlVector))
(define flvector-min (lift2 flmin))

(: flvector-max  (FlVector FlVector -> FlVector))
(define flvector-max (lift2 flmax))

;; ===================================================================================================
;; Summation

#|
Algorithm adapted from:

J R Shewchuk. Adaptive Precision Floating-Point Arithmetic and Fast Geometric Predicates.
Discrete & Computational Geometry, 1996, vol 18, pp 305--363.
|#

(: flvector-sum (FlVector -> Flonum))
;; Returns the sum of the elements in xs in a way that incurs rounding error only once
(define (flvector-sum xs)
  (define n (flvector-length xs))
  ;; Vector of remainders
  (define rs (make-flvector n))
  ;; Loop over `xs'
  (let i-loop ([#{i : Nonnegative-Fixnum} 0]
               ;; p = Number of valid remainders in `rs'
               [#{p : Nonnegative-Fixnum} 0])
    (cond
      [(i . fx< . n)
       ;; Add x consecutively to each remainder, storing the remainder of *those* additions in `rs'
       (let j-loop ([#{j : Nonnegative-Fixnum} 0]
                    ;; q = Number of remainders generated by this j-loop:
                    [#{q : Nonnegative-Fixnum} 0]
                    [x  (unsafe-flvector-ref xs i)])
         (cond
           [(j . fx< . p)
            (define r (unsafe-flvector-ref rs j))
            ;; Get the largest of x and r, or x if it's not rational
            (let-values ([(x r)  (if ((flabs x) . fl< . (flabs r)) (values r x) (values x r))])
              ;; Add with remainder
              (define z (fl+ x r))
              (define-values (hi lo)
                (cond [(flrational? z)  (values z (fl- r (fl- z x)))]
                      [else  (values x r)]))
              (cond [(fl= lo 0.0)
                     ;; No remainder: don't store (makes average case O(n*log(n)))
                     (j-loop (unsafe-fx+ j 1) q hi)]
                    [else
                     ;; Store the remainder, increment the counter
                     (unsafe-flvector-set! rs q lo)
                     (j-loop (unsafe-fx+ j 1) (unsafe-fx+ q 1) hi)]))]
           [else
            ;; Store the sum so far as the last remainder
            (unsafe-flvector-set! rs q x)
            (i-loop (fx+ i 1) (unsafe-fx+ q 1))]))]
      [else
       ;; Add all the remainders
       (let j-loop ([#{j : Nonnegative-Fixnum} 0] [acc  0.0])
         (cond [(j . fx< . p)  (j-loop (unsafe-fx+ j 1) (fl+ acc (unsafe-flvector-ref rs j)))]
               [else  acc]))])))

(: flvector-sums (FlVector -> FlVector))
;; Returns the partial sums of the elements in xs in a way that incurs rounding error only once
;; for each
;; This function works just like `flvector-sum', but keeps track of partial sums instead of
;; summing all the remainders at the end
(define (flvector-sums xs)
  (define n (flvector-length xs))
  (define rs (make-flvector n))
  (define ss (make-flvector n))
  (let i-loop ([#{i : Nonnegative-Fixnum} 0]
               [#{p : Nonnegative-Fixnum} 0])
    (cond
      [(i . fx< . n)
       (let j-loop ([#{j : Nonnegative-Fixnum} 0]
                    [#{q : Nonnegative-Fixnum} 0]
                    [x (unsafe-flvector-ref xs i)]
                    [s 0.0])
         (cond
           [(j . fx< . p)
            (define r (unsafe-flvector-ref rs j))
            (let-values ([(x r)  (if ((flabs x) . fl< . (flabs r)) (values r x) (values x r))])
              (define z (fl+ x r))
              (define-values (hi lo)
                (cond [(flrational? z)  (values z (fl- r (fl- z x)))]
                      [else  (values x r)]))
              (cond [(fl= lo 0.0)
                     (j-loop (unsafe-fx+ j 1) q hi s)]
                    [else
                     (unsafe-flvector-set! rs q lo)
                     (j-loop (unsafe-fx+ j 1) (unsafe-fx+ q 1) hi (fl+ s lo))]))]
           [else
            (unsafe-flvector-set! rs q x)
            (unsafe-flvector-set! ss i (fl+ s x))
            (i-loop (fx+ i 1) (unsafe-fx+ q 1))]))]
      [else  ss])))

(: flsum ((Listof Flonum) -> Flonum))
(define (flsum xs) (flvector-sum (list->flvector xs)))
                                  
