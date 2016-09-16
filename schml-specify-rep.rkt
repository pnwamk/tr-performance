#lang typed/racket
#|------------------------------------------------------------------------------+
|Pass: src/casts/specify-representation
+-------------------------------------------------------------------------------+
|Author: Andre Kuhlenshmidt (akuhlens@indiana.edu)                              |
+-------------------------------------------------------------------------------+
Description: This pass exposes the memory layout of aspects of the program.
After this pass language complexity decreases greatly! But all operations are
exposed as the effects that they truelly are.
+-------------------------------------------------------------------------------+
| Source Grammar : Cast6
| Target Grammar : Data0
+------------------------------------------------------------------------------|#
;; The define-pass syntax



;                                                                                                     
;                                                                                                     
;                                                                                                     
;   ;                 ;;;                                                            ;                
;   ;                   ;                                                            ;          ;     
;   ;                   ;                                                            ;          ;     
;   ; ;;;;     ;;;      ;      ; ;;;      ;;;      ; ;;;   ;;;;;              ; ;;;  ;    ;   ;;;;;;  
;   ;;   ;;   ;   ;     ;      ;;   ;    ;   ;     ;;   ; ;     ;             ;;   ; ;  ;;      ;     
;   ;     ;  ;     ;    ;      ;     ;  ;     ;    ;      ;                   ;      ; ;        ;     
;   ;     ;  ;     ;    ;      ;     ;  ;     ;    ;      ;;;;                ;      ;;;        ;     
;   ;     ;  ;;;;;;;    ;      ;     ;  ;;;;;;;    ;         ;;;;             ;      ;  ;       ;     
;   ;     ;  ;          ;      ;     ;  ;          ;            ;             ;      ;   ;      ;     
;   ;     ;   ;    ;    ;      ;;   ;    ;    ;    ;      ;     ;     ;;      ;      ;    ;     ;     
;   ;     ;    ;;;;      ;;;   ; ;;;      ;;;;     ;       ;;;;;      ;;      ;      ;     ;     ;;;  
;                              ;                                                                      
;                              ;                                                                      
;                              ;                                                                      
;                                                                                                     

(require/typed racket/base
	       [(srcloc->string src->str)
		(srcloc . -> . (U False String))])
(: srcloc->string (srcloc . -> . String))
(define (srcloc->string x) (or (src->str x) ""))

(: syntax->srcloc ((Syntaxof Any) . -> . srcloc))
(define (syntax->srcloc x)
  (srcloc (syntax-source x)
	  (syntax-line x)
          (syntax-column x)
	  (syntax-position x)
	  (syntax-span x)))

(: file->srcloc (String . -> . srcloc))
(define (file->srcloc n)
  (srcloc n #f #f #f #f))




#| In order to simulate the ability to pass the wrong
   number of arguments to a function I need a fold-right
   that takes the shorter of two lists
|#

(: fold-2-left
   (All (a b c)
	(-> (-> a b c c) c (Listof a) (Listof b) c)))
(define (fold-2-left p acc l0 l1)
  (if (or (null? l0) (null? l1))
      acc
      (fold-2-left p
		   (p (car l0) (car l1) acc)
		   (cdr l0)
		   (cdr l1))))


(: snoc (All (A B) (Listof A) B -> (Listof (U A B))))
(define (snoc l e)
  (match l
    [(cons a d) (cons a (snoc d e))]
    ['() (list e)]))


#| Some helpers for debuging |#

(: traces (Parameter (Listof Symbol)))
(define traces (make-parameter '()))

(: trace (-> (U Symbol (Listof Symbol)) Void))
(define (trace t)
  (let* ((t* (traces)))
    (if (symbol? t)
        (traces (cons t t*))
        (traces (append t t*)))))

(define-syntax-rule (trace? s ...)
  (let ([t*? (traces)])
    (or (memq s t*?) ...)))

(: current-log-port (Parameter Output-Port))
(define current-log-port (make-parameter (current-error-port)))

(define-syntax-rule (logf fmt a ...)
  (let ()
    (fprintf (current-log-port) fmt a ...)
    (flush-output (current-log-port))))


(define-syntax-rule (pass/log (o ...) (p in c ...))
  (let ([t? (trace? 'p 'All 'o ...)])
    (when t? (logf "~v input:\n~v\n\n" 'p in))
    (let ([out (p in c ...)])
      (when t? (logf "~v output:\n~v\n\n" 'p in))
      out)))


(define-syntax logging
  (syntax-rules ()
    [(logging n () f a ...) (logging n (All) f a ...)]
    [(logging n (o0 o* ...) f a ...)
     (let ([t? (trace? 'n 'o0 'o* ...)])
       (when t? (logf (format "~a: ~a\n\n" 'n f) a ...)))]))

(define-syntax-rule (log-body n (v ...) e ... b)
  (let ([t? (trace? 'n 'All)])
    (when t?
      (logf "~v input:\n" 'n)
      (logf "\t~v : ~v\n" 'v v) ...
      (logf "\n"))
    e ...
    (let ([out b])
      (when t?
        (logf "~v output:\n\t~v\n\n" 'n out)
        (flush-output (current-log-port)))
      out)))

(define-syntax-rule (tracef (s ...) fmt a ...)
  (when (trace? s ...)
    (logf fmt a ...)))

(define-syntax trace-define
  (syntax-rules (->)
    [(_ (f i ...) -> (r ...) e ... b)
     (begin
       (define n (box 0))
       (define (f i ...)
         (define t? (trace? 'All 'f))
         (set-box! n (+ (unbox n) 1))
         (when t?
           (logf "~a@~a:~a=~v\n" 'f (unbox n) 'i i) ...
           (logf "\n")
           (flush-output (current-log-port)))
         e ...
         (let-values ([(r ...) b])
           (set-box! n (- (unbox n) 1))
           (when t?
             (logf "~a@~a:~a=~v\n" 'f (unbox n) 'r r) ...
             (logf "\n")
             (flush-output (current-log-port)))
           (values r ...))))]
    [(_ (f i ...) e ... b)
     (trace-define (f i ...) -> (out) e ... b)]))

;; allows for conditional compilation
(define-for-syntax under-construction?
  (and (getenv "schmlUnderConstruction") #t))

(define-for-syntax syntax-id
  (syntax-rules ()
    [(_ x ...) (begin x ...)]))

(define-for-syntax syntax-void
  (syntax-rules ()
    [(_ x ...) (void)]))

;; only run this code if we are working on schml
(define-syntax if-in-construction
  (if under-construction?
      syntax-id
      syntax-void))

(struct exn:todo exn ())
(begin-for-syntax (struct exn:todo exn ()))

(define-syntax TODO
  (if under-construction?
      (syntax-rules ()
        [(_ x ...)
         (raise
          (exn:todo
           (format "TODO: ~a" '(x ...))
           (current-continuation-marks)))])
      (lambda (x)
        (define loc-string
          (srcloc->string
           (srcloc (syntax-source x) (syntax-line x) (syntax-column x)
                   (syntax-position x) (syntax-span x))))
        (raise-syntax-error
         'Unfinished-TODO
         (format "~a: ~a" loc-string (syntax->datum x))))))

;; Do syntax gives an imperative style syntax to monadic code
;; This particular implementation extends this were useful allowing
;; the user to use other binding an branching form while
;; maintaining the "do syntax" in the sytactic conclusions of the forms.
;; The common form:
#;(do (bind-operation : (Monad-name Impure-Type Pure-Type)
    ;; Monadic Statements
    (pattern : Pure-Type <- monadic-expression))
    ;; Or discarding the pure value
    (monadic-expression : Monadic-Type)
    ...
    monadic-expression)
;; TODO syntax case may allow for more parametricity over other
;; binding forms
(define-syntax do
  (syntax-rules (<- : doing
                 let let* let-values let*-values match-let match-let-values
                 match match*
                 begin if
                 )
    ;; let let* let-values let*-values match-let match-let-values
    ;; all work in do expression with the bodies of the let implicitly
    ;; acting as a do expression
    [(_ ann (let (b ...) e e* ...))
     (let (b ...) (do ann e e* ...))]
    [(_ bind (let* (b ...) e e* ...)) (let* (b ...) (do bind e e* ...))]
    [(_ bind (let-values (b ...) e e* ...))
     (let-values (b ...) (do bind e e* ...))]
    [(_ bind (let*-values (b ...) e e* ...))
     (let*-values (b ...) (do bind e e* ...))]
    [(_ bind (match-let (b ...) e e* ...))
     (match-let (b ...) (do bind e e* ...))]
    [(_ bind (match-let-values (b ...) e e* ...))
     (match-let-values (b ...) (do bind e e* ...))]
    ;; match and match* also work in do-expressions
    ;; the right hand side of each match clause is implicitly
    ;; a do expression
    [(_ ann (match  e [p0 s0 s0* ...] [p s s* ...] ...))
     (match  e  [p0 (do ann s0 s0* ...)] [p (do ann s s* ...)] ...)]
    [(_ ann (match* vs [p0 s0 s0* ...] [p s s* ...] ...))
     (match* vs [p0 (do ann s0 s0* ...)] [p (do ann s s* ...)] ...)]
    ;; Facilitate faster type-checking around ifs (maybe) and
    ;; allow for un-annotate do-syntax in if branches with the help
    ;; of the "Infer" rule below.
    [(_ ann (if t c a)) (if t (do ann c) (do ann a))]
    ;; Allow begin to escape to real effects
    ;; Useful for printing because the IO monad would be too much
    [(_ ann (begin s! ...) s s* ...) (begin s! ... (do ann s s* ...))]
    ;; "Infer" the type of unannotated do expressions
    ;; by copying the current bind-operation and type annotation.
    [(_ (bind : T) (doing (p : t <- rhs) s* ...))
     (do (bind : T) (p : t <- rhs) s* ...)]
    ;; Left hand side of each do statement is actually a pattern
    ;; TODO amk find a way to give this better error messages
    ;; like below but more abstract
    [(_ ann ((p ...) : a <- e0) s s* ...)
     (do ann (tmp : a <- e0) (match-let ([(p ...) tmp]) s s* ...))
     #|
     (bind (ann e0 (C m a))
     (lambda ((tmp : a)) : (C m b)
     (match tmp
       [(p ...) (do (bind : (C m b)) e e* ...)]
       [otherwise
        (error 'do "pattern ~a didn't match ~a" '(p ...) tmp)])))
     |#]
    ;; Hint the type of do expressions by annotating the return value
    [(_ (bind : T) e) (ann e : T)]
    ;; Normal definition of do but propogating types to help the
    ;; type checker.
    [(_ (bind : (C m b)) (v : a <- e0) s s* ...)
     (ann
      (bind (ann e0 (C m a))
       (lambda ([v : a])
         : (C m b)
         (do (bind : (C m b)) s s* ...)))
      (C m b))]
    ;; More concise syntax for throwing away the pure value.
    [(_ (bind : (C m b)) (e0 : T) s s* ...)
     (bind (ann e0 T) (lambda (_) (do (bind : (C m b)) s s* ...)))]))


#| The state monad |#
(define-type (State S A) (S . -> . (values A S)))

(define #:forall (M A) (run-state (ma : (State M A)) (s : M))
  : (values A M)
  (ma s))

(define #:forall (M A) (return-state (p : A))
  : (State M A)
  (lambda ((i : M)) (values p i)))

(define #:forall (M A B) (bind-state (pi : (State M A))
                                     (f : (-> A (State M B))))
  : (State M B)
  (lambda ((i : M))
    (let-values ([((p : A) (i : M)) (pi i)])
      ((f p) i))))

(define #:forall (M) (put-state (p : M))
  : (State M Null)
  (lambda ((s : M))
    (values '() p)))

(define #:forall (M) get-state : (State M M)
  (lambda ((i : M))
    (values i i)))


(define #:forall (M A B) (map-state [f : (A -> (State M B))] [l : (Listof A)])
  : (State M (Listof B))
  (letrec ([loop : ((Listof A) . -> . (State M (Listof B)))
            (lambda ([l : (Listof A)]) : (State M (Listof B))
             (if (null? l)
                 (return-state '())
                 (do (bind-state : (State M (Listof B)))
                     (a : B <- (f (car l)))
                     (d : (Listof B) <- (loop (cdr l)))
                     (return-state (cons a d)))))])
    (loop l)))

(define #:forall (M A B C)
  (map-state2 [f : (A B -> (State M C))] [l1 : (Listof A)] [l2 : (Listof B)])
  : (State M (Listof C))
  (letrec ([loop : ((Listof A) (Listof B) -> (State M (Listof C)))
            (lambda ([l1 : (Listof A)]
                     [l2 : (Listof B)])
              : (State M (Listof C))
              (cond
                [(null? l1)
                 (if (null? l2)
                     (return-state '())
                     (error 'map-state2 "second list longer"))]
                [(null? l2) (error 'map-state "first list longer")]
                [else
                 (do (bind-state : (State M (Listof C)))
                     (a : C <- (f (car l1) (car l2)))
                     (d : (Listof C) <- (loop (cdr l1) (cdr l2)))
                     (return-state (cons a d)))]))])
    (loop l1 l2)))


(: foldr-state (All (M A B) ((A B -> (State M B)) B (Listof A) -> (State M B))))
(define (foldr-state fn acc ls)
  (if (null? ls)
      (return-state (ann acc B))
      (do (bind-state : (State M B))
          (match-let ([(cons a d) ls])
            (acc : B <- (foldr-state fn acc d))
            (fn a acc)))))

(: lift-state (All (M A B C D)
               (case-> [(A -> B) (State M A) -> (State M B)]
                       [(A B -> C) (State M A) (State M B) -> (State M C)]
                       [(A B C -> D) (State M A) (State M B) (State M C) -> (State M D)])))
(define lift-state
  (case-lambda
    [(f ma)
     (do (bind-state : (State M B))
         (a : A <- ma)
         (return-state (f a)))]
    [(f ma mb)
     (do (bind-state : (State M C))
         (a : A <- ma)
         (b : B <- mb)
         (return-state (f a b)))]
    [(f ma mb mc)
     (do (bind-state : (State M D))
         (a : A <- ma)
         (b : B <- mb)
         (c : C <- mc)
         (return-state (f a b c)))]))



#| Utilities Not Provided by Racket |#

;; Binding While Branching!
(define-syntax-rule (lif (t p) c a)
  (let ((t p)) (if t c a)))

(define-syntax ex-cond
  (syntax-rules (else => let let-values match-let)
    [(_ (else e* ... e))
     (begin e* ... e)]
    [(_ (let (b ...) c c* ...))
     (let (b ...) (ex-cond c c* ...))]
    [(_ (let-values (b ...) c c* ...))
     (let (b ...) (ex-cond c c* ...))]
    [(_ (match-let (b ...) c c* ...))
     (let (b ...) (ex-cond c c* ...))]
    [(_ (p => e) c c* ...)
     (lif (t p) (e t) (ex-cond c c* ...))]
    [(_ (p e* ... e) c c* ...)
     (lif (t p) (begin e* ... e) (ex-cond c c* ...))]))

;; Cast to Boolean
(define (true? [x : Any]) : Boolean
  (if x #t #f))

(: to-symbol (Any -> Symbol))
(define (to-symbol a)
  (cond
    [(string? a) (string->symbol a)]
    [(symbol? a) a]
    [else (to-symbol (format "~a" a))]))


;                                                                                            
;                                                                                            
;                                                                                            
;                                                                           ;                
;                                                                           ;          ;     
;                                                                           ;          ;     
;     ;;;      ; ;;;    ; ;;;    ;;;      ; ;;;   ;;;;;              ; ;;;  ;    ;   ;;;;;;  
;    ;   ;     ;;   ;   ;;   ;  ;   ;     ;;   ; ;     ;             ;;   ; ;  ;;      ;     
;   ;     ;    ;        ;      ;     ;    ;      ;                   ;      ; ;        ;     
;   ;     ;    ;        ;      ;     ;    ;      ;;;;                ;      ;;;        ;     
;   ;;;;;;;    ;        ;      ;     ;    ;         ;;;;             ;      ;  ;       ;     
;   ;          ;        ;      ;     ;    ;            ;             ;      ;   ;      ;     
;    ;    ;    ;        ;       ;   ;     ;      ;     ;     ;;      ;      ;    ;     ;     
;     ;;;;     ;        ;        ;;;      ;       ;;;;;      ;;      ;      ;     ;     ;;;  
;                                                                                            
;                                                                                            
;                                                                                            
;                                                                                            

;; Exceptions Thrown should all be subtypes of exn:schml
(struct exn:schml exn ())

;; Expception thrown in a specific pass 
(struct exn:schml:pass exn:schml ())

;; This is a generic error handler that is usefull for
;; quick testing it should not be used for actuall errors
;; once the code is complete.

(define-syntax-rule (raise-pass-exn who fmt args ...)
  (raise 
   (exn:schml:pass 
    (format "Error in ~a: ~a"
	    who
	    (format fmt args ...))
    (current-continuation-marks))))

#| Errors thrown in the read pass |#
(struct exn:schml:read exn:schml ())

(define file-name-fmt
  "Error in read: unable to extract file name from the path ~a")

(define-syntax-rule (raise-file-name-exn p)
  (raise (exn:schml:read
	  (format file-name-fmt (path->string p))
	  (current-continuation-marks))))


;                                                                                                                                                           
;                                                                                                                                                           
;                                                                                                                                                           
;                                  ;;;     ;                                                     ;                                         ;                
;                                 ;        ;                                           ;         ;                                         ;          ;     
;                                 ;                                                    ;                                                   ;          ;     
;     ;;;      ;;;    ; ;;;;    ;;;;;;   ;;;       ;;; ;  ;     ;    ; ;;;    ;;;;   ;;;;;;    ;;;       ;;;    ; ;;;;              ; ;;;  ;    ;   ;;;;;;  
;    ;   ;    ;   ;   ;;   ;;     ;        ;      ;   ;;  ;     ;    ;;   ;  ;    ;    ;         ;      ;   ;   ;;   ;;             ;;   ; ;  ;;      ;     
;   ;        ;     ;  ;     ;     ;        ;     ;     ;  ;     ;    ;            ;    ;         ;     ;     ;  ;     ;             ;      ; ;        ;     
;   ;        ;     ;  ;     ;     ;        ;     ;     ;  ;     ;    ;       ;;;;;;    ;         ;     ;     ;  ;     ;             ;      ;;;        ;     
;   ;        ;     ;  ;     ;     ;        ;     ;     ;  ;     ;    ;      ;;    ;    ;         ;     ;     ;  ;     ;             ;      ;  ;       ;     
;   ;        ;     ;  ;     ;     ;        ;     ;     ;  ;     ;    ;      ;     ;    ;         ;     ;     ;  ;     ;             ;      ;   ;      ;     
;    ;   ;    ;   ;   ;     ;     ;        ;      ;   ;;  ;;   ;;    ;      ;    ;;    ;         ;      ;   ;   ;     ;     ;;      ;      ;    ;     ;     
;     ;;;      ;;;    ;     ;     ;     ;;;;;;;    ;;; ;   ;;;; ;    ;       ;;;; ;     ;;;   ;;;;;;;    ;;;    ;     ;     ;;      ;      ;     ;     ;;;  
;                                                      ;                                                                                                    
;                                                 ;   ;;                                                                                                    
;                                                  ;;;;                                                                                                     
;                                                                                                                                                           

;; How blame is tracked
(define-type Blame-Semantics (U 'Lazy-D))
(define blame-semantics : (Parameterof Blame-Semantics)
  (make-parameter 'Lazy-D))

;; How casts are represented
(define-type Cast-Representation (U 'Type-Based 'Coercions))
(define cast-representation : (Parameterof Cast-Representation)
  (make-parameter 'Coercions))

;; Optimizations options
(: dynamic-operations? (Parameterof (U Boolean 'inline)))
(define dynamic-operations? (make-parameter #t))

;; Default places for everything, but there is no default source
(define c-path : (Parameterof (Option Path))
  (make-parameter #f))
(define s-path : (Parameterof (Option Path))
  (make-parameter #f))
(define output-path : (Parameterof (Option Path))
  (make-parameter #f))
(define init-heap-kilobytes : (Parameterof Natural)
  (make-parameter (expt 1024 2)))

;; Interaction with the c compiler
(define c-flags : (Parameterof (Listof String))
  (make-parameter '()))
;; where is the runtime to be used located
(define runtime-path : (Parameterof (Option Path)) (make-parameter #f))


(struct Config
  ([source-path : Path]
   [blame-semantics : Blame-Semantics]
   [exec-path : Path]
   [c-path : Path]
   [keep-c : Boolean]
   [c-flags : (Listof String)]
   [asm-path : (Option Path)]
   [cast-rep : Cast-Representation]
   [mem-limit : Natural]
   [runtime-path : (Option Path)])
  #:transparent)



;                                                                                                                                                                    
;                                                                                                                                                                    
;                                                                                                                                                                    
;                        ;                                                                                                                          ;                
;                        ;                                                                               ;                                          ;          ;     
;                                                                                                        ;                                          ;          ;     
;   ;     ;  ; ;;;;    ;;;       ;;; ;  ;     ;    ;;;               ;;;      ;;;    ;     ;  ; ;;;;   ;;;;;;     ;;;      ; ;;;             ; ;;;  ;    ;   ;;;;;;  
;   ;     ;  ;;   ;;     ;      ;   ;;  ;     ;   ;   ;             ;   ;    ;   ;   ;     ;  ;;   ;;    ;       ;   ;     ;;   ;            ;;   ; ;  ;;      ;     
;   ;     ;  ;     ;     ;     ;     ;  ;     ;  ;     ;           ;        ;     ;  ;     ;  ;     ;    ;      ;     ;    ;                 ;      ; ;        ;     
;   ;     ;  ;     ;     ;     ;     ;  ;     ;  ;     ;    ;;;;   ;        ;     ;  ;     ;  ;     ;    ;      ;     ;    ;                 ;      ;;;        ;     
;   ;     ;  ;     ;     ;     ;     ;  ;     ;  ;;;;;;;           ;        ;     ;  ;     ;  ;     ;    ;      ;;;;;;;    ;                 ;      ;  ;       ;     
;   ;     ;  ;     ;     ;     ;     ;  ;     ;  ;                 ;        ;     ;  ;     ;  ;     ;    ;      ;          ;                 ;      ;   ;      ;     
;   ;;   ;;  ;     ;     ;      ;   ;;  ;;   ;;   ;    ;            ;   ;    ;   ;   ;;   ;;  ;     ;    ;       ;    ;    ;         ;;      ;      ;    ;     ;     
;    ;;;; ;  ;     ;  ;;;;;;;    ;;; ;   ;;;; ;    ;;;;              ;;;      ;;;     ;;;; ;  ;     ;     ;;;     ;;;;     ;         ;;      ;      ;     ;     ;;;  
;                                    ;                                                                                                                               
;                                    ;                                                                                                                               
;                                    ;                                                                                                                               
;                                                                                                                                                                    



(struct Unique-Counter ([next : Natural])
  #:mutable)

(: make-unique-counter (Natural -> Unique-Counter))
(define (make-unique-counter x)
  (Unique-Counter x))

(: unique-counter-next! (Unique-Counter -> Natural))
(define (unique-counter-next! u)
  (define tmp (Unique-Counter-next u))
  (set-Unique-Counter-next! u (add1 tmp))
  tmp)


;                                                                                                                                                                                                        
;                                                                                                                                                                                                        
;                                                                                                                                                                                                        
;                        ;                                            ;           ;                                ;         ;;;     ;                                                  ;                
;                        ;                                            ;           ;                      ;         ;        ;        ;                                                  ;          ;     
;                                                                                 ;                      ;                  ;                                                           ;          ;     
;   ;     ;  ; ;;;;    ;;;       ;;; ;  ;     ;    ;;;              ;;;       ;;; ;    ;;;    ; ;;;;   ;;;;;;    ;;;      ;;;;;;   ;;;       ;;;      ; ;;;   ;;;;;              ; ;;;  ;    ;   ;;;;;;  
;   ;     ;  ;;   ;;     ;      ;   ;;  ;     ;   ;   ;               ;      ;   ;;   ;   ;   ;;   ;;    ;         ;        ;        ;      ;   ;     ;;   ; ;     ;             ;;   ; ;  ;;      ;     
;   ;     ;  ;     ;     ;     ;     ;  ;     ;  ;     ;              ;     ;     ;  ;     ;  ;     ;    ;         ;        ;        ;     ;     ;    ;      ;                   ;      ; ;        ;     
;   ;     ;  ;     ;     ;     ;     ;  ;     ;  ;     ;    ;;;;      ;     ;     ;  ;     ;  ;     ;    ;         ;        ;        ;     ;     ;    ;      ;;;;                ;      ;;;        ;     
;   ;     ;  ;     ;     ;     ;     ;  ;     ;  ;;;;;;;              ;     ;     ;  ;;;;;;;  ;     ;    ;         ;        ;        ;     ;;;;;;;    ;         ;;;;             ;      ;  ;       ;     
;   ;     ;  ;     ;     ;     ;     ;  ;     ;  ;                    ;     ;     ;  ;        ;     ;    ;         ;        ;        ;     ;          ;            ;             ;      ;   ;      ;     
;   ;;   ;;  ;     ;     ;      ;   ;;  ;;   ;;   ;    ;              ;      ;   ;;   ;    ;  ;     ;    ;         ;        ;        ;      ;    ;    ;      ;     ;     ;;      ;      ;    ;     ;     
;    ;;;; ;  ;     ;  ;;;;;;;    ;;; ;   ;;;; ;    ;;;;            ;;;;;;;    ;;; ;    ;;;;   ;     ;     ;;;   ;;;;;;;     ;     ;;;;;;;    ;;;;     ;       ;;;;;      ;;      ;      ;     ;     ;;;  
;                                    ;                                                                                                                                                                   
;                                    ;                                                                                                                                                                   
;                                    ;                                                                                                                                                                   
;                                                                                                                                                                                                        


(struct Uid ([prefix : String] [suffix : Natural]) #:transparent)

(define-type Uid* (Listof Uid))

(define FIRST-UID-SUFFIX 0)

(: uid->string (-> Uid String))
(define (uid->string u)
  ;; Rubout all non c identifier characters
  (: help (Char -> Char))
  (define (help c)
    (let ([n (char->integer c)])
      ;;        A-Z          a-z          0-9
      (if (or (<= 65 n 90) (<= 97 n 122) (<= 48 n 57))
          c
          #\_)))
  (string-append
   "u"
   (number->string (Uid-suffix u))
   "_"
   (list->string (map help (string->list (Uid-prefix u))))))

;; Are two uid equal?
(: uid=? (-> Uid Uid Boolean))
(define (uid=? [u : Uid] [v : Uid])
  (or (= (Uid-suffix u) (Uid-suffix v))))

(: make-next-uid! : Unique-Counter -> (String -> Uid))
(define ((make-next-uid! uc) s)
  (Uid s (unique-counter-next! uc)))

;; If you are in the state monad you can purely allocate and increment
(define-type Nat Natural)
(: uid-state (String -> (State Nat Uid)))
(define (uid-state (name : String))
  (lambda ((s : Natural))
    (values (Uid name s) (add1 s))))

;; If you are in state passing style you
;; could use this to allocate and increment
(: next-uid (-> String Natural (values Uid Natural)))
(define (next-uid prefix suffix) next-uid
  (values (Uid prefix suffix) (add1 suffix)))

;; A simple macro for helpign with state passing style
;; I am trying to move away from this so that code can
;; be less verbose
(define-syntax let-uid*
  (syntax-rules ()
    [(_ (wrong ...) others ...)
     (raise-syntax-error 'let-uid "next must always be an identifier")]
    [(_ next () body ...)(let () body ...)]
    [(_ next ([name0 prefix0] [name* prefix*] ...) body ...)
     (let-values ([(name0 next) (next-uid prefix0 next)])
       (let-uid* next ([name* prefix*] ...)
		 body ...))]))


;                                                                                   
;                                                                                   
;                                                                                   
;       ;;;                                                        ;                
;      ;                                                           ;          ;     
;      ;                                                           ;          ;     
;    ;;;;;;    ;;;      ; ;;;  ;;;;;;    ;;;;;              ; ;;;  ;    ;   ;;;;;;  
;      ;      ;   ;     ;;   ; ;  ;  ;  ;     ;             ;;   ; ;  ;;      ;     
;      ;     ;     ;    ;      ;  ;  ;  ;                   ;      ; ;        ;     
;      ;     ;     ;    ;      ;  ;  ;  ;;;;                ;      ;;;        ;     
;      ;     ;     ;    ;      ;  ;  ;     ;;;;             ;      ;  ;       ;     
;      ;     ;     ;    ;      ;  ;  ;        ;             ;      ;   ;      ;     
;      ;      ;   ;     ;      ;  ;  ;  ;     ;     ;;      ;      ;    ;     ;     
;      ;       ;;;      ;      ;  ;  ;   ;;;;;      ;;      ;      ;     ;     ;;;  
;                                                                                   
;                                                                                   
;                                                                                   
;                                                                                   


#|
All language "Forms" are just polymorphic racket structs.
These are used to define valid ASTs which are passed between
passes of the compiler. There are many forms because we try
to switch forms whenever there is any change in the meaning
of the form.

The macro generates a function for each name in the list plus
an predicate to identify values of this struct.
So (name field1 field2) would create the following definitions.
name? - predicate
name  - constructor
name-field1 - accessor for field1
name-field2 - accessor for field2
And a type constructor "name" expecting the types of field1 and field2 
|#

(define-syntax (define-forms stx)
  (syntax-case stx ()
    [(_ (name* field** ...) ...)
     (let ([f** (syntax->list #'((field** ...) ...))])
       (with-syntax ([((type** ...) ...) (map generate-temporaries f**)])
         #'(begin
             (struct (type** ...) name* ([field** : type**] ...) #:transparent)
             ...)))]))

(define-forms
  ;; Top level wrapper for combining compiler
  ;; state, meta-information, and the program AST
  (Prog annotation expression)
  ;; Annotations that may be added to other AST nodes
  (Ann value data)
  ;; Function abstraction
  (Lambda formals body)
  ;; Function application 
  (App operator operands)
  ;; Variable node
  (Var id)
  ;; Conditionals
  (If test then else)
  ;; Type ascription
  (Ascribe expression type label)
  ;; Primitive operators application 
  (Op operator operands)
  ;; recursive binding
  (Letrec bindings body)
  ;; non recursive binding
  (Let bindings body)
  ;; sequence operator
  (Begin effects value)
  ;; Perform a No Operation
  (No-Op)
  ;; Effect operations
  ;; Monotonic effects
  (Mbox value)
  (Munbox box)
  (Mbox-set! box value)
  (Mvector value constructor)
  (Mvector-set! vector offset value)
  (Mvector-ref vector offset)
  ;; Guarded effects
  (Gbox value)
  (Gunbox box)
  (Gbox-set! box value)
  (Gvector len init-val)
  (Gvector-set! vector offset value)
  (Gvector-ref vector offset)
  ;;
  (Create-tuple values)
  (Tuple-proj tuple index)
  (Coerce-Tuple cast value coercion)
  (Cast-Tuple cast value t1 t2 lbl)
  ;; various imediates markers
  (Quote literal)    ;; immediate data in general
  ;; Node that references a piece of code identified by the UID value
  (Code-Label value)
  (Tag bits)         ;; an tag for an imediate value
  (Type type)        ;; an atomic type
  ;; Effectfull expressions
  ;; typed bindings annotations
  (Fml identifier type)
  (Bnd identifier type expression)
  ;; Different casts
  (Cast expression instruction)
  ;; TODO Interpreted-Cast
  (Interpreted-Cast expression instruction)
  (Fn-Caster expression)
  ;;Type Operations
  (Type-Dyn-Huh exp)
  (Type-Tag expression)
  (Type-Fn-arity expression)
  (Type-Fn-arg expression index)
  (Type-Fn-return expression)
  (Type-Fn-Huh type)
  (Type-GVect-Huh type)
  (Type-GRef-Huh type)
  (Type-GRef-Of expression)
  (Type-GVect-Of expression)
  (Type-Tuple-Huh type)
  (Type-Tuple-num type)
  (Type-Tuple-item type index)
  ;; closure Representation
  (App-Closure code data exprs)
  (Closure-Data code caster variables)
  (Closure-code var)
  (Closure-ref this var)
  (Closure-caster this)
  (Let-Static* type-bindings crcn-bindings body)
  (Static-Id id)
  (LetP bindings body)
  (LetC bindings body);; Can create cyclic immutable data
  (Procedure this params code caster bound-vars body)
  ;; represents a set of moves to initialize variables before
  (Code variables body)
  ;; Dyn operations
  (Dyn-tag expression)
  (Dyn-immediate expression)
  (Dyn-type expression)
  (Dyn-value expression)
  (Dyn-make expression type)
  (Dyn-Fn-App expr expr* type* label)
  (Dyn-GRef-Ref expr label)
  (Dyn-GRef-Set! expr1 expr2 type label)
  (Dyn-GVector-Ref expr index label)
  (Dyn-GVector-Set! expr1 index expr2 type label)
  ;; Observational Operations
  (Blame expression)
  (Observe expression type)
  ;; Lambda subforms
  (Castable caster body)
  (Bound closure variables body)
  (Free caster variables body)
  (GlobDecs vars body) ;; declaration of global variables
  ;; Static Global Binding
  (Labels bindings body)
  (App-Code rand rators)
  (App-Fn rand rators)
  (App/Fn-Proxy-Huh rand rators)
  (App-Fn-or-Proxy cast rand rators)
  ;; Benchmarking tools language forms
  ;; low cost repetition
  (Repeat var start end body)
  ;; TODO figue out an appropriate comment about all forms here
  (Halt)
  (Success)
  (Assign lhs rhs)
  ;; Declares Local Variables
  (Locals names body)
  (Return value)
  (Relop primitive expression1 expression2)
  ;; Uil Memory Ops
  (Malloc expression)
  ;; Uil IO Primitives todo add C Calls and replace these
  (Printf format expressions)
  (Print expression)
  (BinOp primitive expression1 expression2)
  ;; Guarded references IL Representation
  (Unguarded-Box init)
  (Unguarded-Box-Ref box)
  (Unguarded-Box-Set! box value)
  (Unguarded-Vect size value)
  (Unguarded-Vect-Ref vect index)
  (Unguarded-Vect-Set! vect index value)
  (Guarded-Proxy expression representation)
  (Guarded-Proxy-Ref guarded)
  (Guarded-Proxy-Source guarded)
  (Guarded-Proxy-Target guarded)
  (Guarded-Proxy-Blames guarded)
  (Guarded-Proxy-Coercion guarded)
  (Guarded-Proxy-Huh expression)
  #|
  (GRep-proxied? expression)
  (UGbox expression)
  (UGbox-set! expression1 expression2)
  (UGbox-ref expression)
  (UGvect expression1 expression2)
  (UGvect-set! expression1 expression2 expression3)
  (UGvect-ref expression1 expression2)
  (Gproxy for-exp from-exp to-exp blames-exp)
  (Gproxy-for expression)
  (Gproxy-from expression)
  (Gproxy-to expression)
  (Gproxy-blames expression)
  |#
  )

(define NO-OP (No-Op))


(define-type Blame-Label String)
(define blame-label? string?)


#| Types throughout the languages |#

;; Schml types
(define-forms
  (Unit)
  (Int)
  (Bool)
  (Dyn)
  (Fn arity fmls ret)
  (MRef  arg)
  (MVect arg)
  (GRef  arg)
  (GVect arg)
  (STuple num items))

;; TODO I am unsure of if these are being used
;; find out and act appropriately
#;
(define-forms
  (String-Ptr)
  (Any-Value)
  (Any-Type)
  (Void-Type)
  (Bottom-Type))

;;Constants for the types
(define UNIT-TYPE (Unit))
(define INT-TYPE (Int))
(define BOOL-TYPE (Bool))
(define DYN-TYPE (Dyn))
(define REF-DYN-TYPE (GRef DYN-TYPE))

;; define type id = t and id* = (c* t) ...
(define-syntax-rule (define-type+ id ([id* c*] ...) t)
  (begin (define-type id t)
	 (define-type id* (c* id)) ...))

#|
(define ANY-TYPE (Any-Type))
(define STRING-PTR (String-Ptr))
(define ANY-VALUE (Any-Value))
(define BOTTOM-TYPE (Bottom-Type))
(define VOID-TYPE (Void-Type))
|#
(define INTxINT-TYPE (list INT-TYPE INT-TYPE))
(define INTxINT->BOOL-TYPE (Fn 2 INTxINT-TYPE BOOL-TYPE))
(define INTxINT->INT-TYPE (Fn 2 INTxINT-TYPE INT-TYPE))
(define ->UNIT-TYPE (Fn 0 '() UNIT-TYPE))
(define ->INT-TYPE (Fn 0 '() INT-TYPE))

;; Are two types consistent at the top of the types?
(: shallow-consistent? (Any Any -> Boolean))
(define (shallow-consistent? t g)
  ;; Typed racket made me do it
  ;; This uber modular structure speeds up type checking
  (define (both-int? t g) : Boolean (and (Int? t)  (Int? g)))
  (define (both-bool? t g): Boolean (and (Bool? t) (Bool? g)))
  (define (both-fn? t g)  : Boolean
    (and (Fn? t)
         (Fn? g)
         (equal? (Fn-arity t)
                 (Fn-arity g))))
  (define (both-tuple? t g)  : Boolean
    (and (STuple? t)
         (STuple? g)
         (equal? (STuple-num t)
                 (STuple-num g))))
  (define (ref-shallow-consistent? t g) : Boolean
    (or (and (GRef? t) (GRef? g))
        (and (GVect? t) (GVect? g))
        (and (MRef? t) (MRef? t))
        (and (MVect? t) (MVect? t))))
  (or (Dyn? t)
      (Dyn? g)
      (both-int? t g)
      (both-bool? t g)
      (both-fn? t g)
      (both-tuple? t g)
      (ref-shallow-consistent? t g)))


(: completely-static-type? (-> Schml-Type Boolean))
;; Is the type t devoid of dyn?
(define (completely-static-type? t)
  ;; Typed Racket made me do it
  ;; This uber modular structure speeds up type checking
  (define (fn-completely-static? [t : Schml-Type]): Boolean
    (and (Fn? t)
         (andmap completely-static-type? (Fn-fmls t))
         (completely-static-type? (Fn-ret t))))
  (define (tuple-completely-static? [t : Schml-Type]): Boolean
    (and (STuple? t)
         (andmap completely-static-type? (STuple-items t))))
  (define (ref-completely-static? [t : Schml-Type])
    (or (and (GRef? t) (completely-static-type? (GRef-arg t)))
        (and (MRef? t) (completely-static-type? (MRef-arg t)))
        (and (GVect? t) (completely-static-type? (GVect-arg t)))
        (and (MVect? t) (completely-static-type? (MVect-arg t)))))
  (or (Int? t)
      (Bool? t)
      (fn-completely-static? t)
      (tuple-completely-static? t)
      (ref-completely-static? t)))







#|-----------------------------------------------------------------------------+
| Types shared by the Schml language family
+-----------------------------------------------------------------------------|#

(define-type Schml-Primitive (U Schml-Prim Schml-Prim!))

#;(: schml-primitive? (-> Any Boolean : Schml-Primitive))
#;
(define (schml-primitive? x)
  (or (schml-prim? x) (schml-prim!? x)))

(define-predicate schml-primitive? Schml-Primitive)

(define-type Schml-Prim
  (U IntxInt->Int-Primitive
     IntxInt->Bool-Primitive
     ->Int-Primitive))

(define-predicate schml-prim? Schml-Prim)

#;(: schml-prim? (Any -> Boolean : Schml-Prim))
#;
(define (schml-prim? x)
  (or (IntxInt->Int-primitive? x)
      (IntxInt->Bool-primitive? x)))

(define-type Schml-Prim!
  (U Timer-Primitive))

(define-predicate schml-prim!? Schml-Prim!)
#;(: schml-prim!? (Any -> Boolean : Schml-Prim!))
#;
(define (schml-prim!? x)
  (or (timer-primitive? x)))

(define-type IntxInt->Int-Primitive (U '* '+ '-
                                        'binary-and 'binary-or 'binary-xor
                                        '%/ '%>> '%<<))

(define-type IxI->I-Prim IntxInt->Int-Primitive)

(define-predicate IntxInt->Int-primitive? IntxInt->Int-Primitive)

(define-type ->Int-Primitive (U 'read-int))
(define-type ->I-Prim ->Int-Primitive)

(define-predicate ->Int-primitive? ->Int-Primitive)


#;(: IntxInt->Int-primitive? (-> Any Boolean : IntxInt->Int-Primitive))
#;
(define (IntxInt->Int-primitive? x)
  
  #;(memq x '(* + - binary-and binary-or binary-xor %/ %>> %<<))
  )


(define-type IntxInt->Bool-Primitive (U '< '<= '= '> '>=))
(define-type IxI->B-Prim IntxInt->Bool-Primitive)
(define-predicate IntxInt->Bool-primitive? IntxInt->Bool-Primitive)

#;(: IntxInt->Bool-primitive? (Any -> Boolean : IntxInt->Bool-Primitive))
#;
(define (IntxInt->Bool-primitive? x)
  (memq x '(< <= = > >=))
  #;                     
  (or (eq? '< x)
      (eq? '<= x)
      (eq? '= x)
      (eq? '> x)
      (eq? '>= x)))

#|
(define-type IntxNon0->Int-Primitives '/)
(define-type Ix!0->I IntxNon0->Int-Primitives)
(define-predicate IntxNon0->Int-Prim? IntxNon0->Int-Primitives)

(define-type IntxNibble->Int-Primitives (U '<< '>>))
(define-type IxN->I IntxNibble->Int-Primitives)
(define-predicate IntxNibble->Int-Prim? IntxNibble->Int-Primitives)
|#

(define-type Timer-Primitive (U 'timer-start 'timer-stop 'timer-report))

(: timer-primitive? (Any -> Boolean : Timer-Primitive))
(define (timer-primitive? x)
  (or (eq? 'timer-start  x)
      (eq? 'timer-stop   x)
      (eq? 'timer-report x)))

#| Literals of the schml languages
   Only Integers and Booleans in the schml language are first
   class literal constants
|#

(define-type Schml-Literal
  (U Integer Boolean Null))

#;(: platform-integer? (Any -> Boolean : Integer))
#;
(define (platform-integer? x)
  (fixnum? x))

(: schml-literal? (Any -> Boolean : Schml-Literal))
(define (schml-literal? x)
  (or (exact-integer? x)
      (boolean? x)
      (null? x)))

(: schml-literal->type (Schml-Literal -> (U Bool Int Unit)))
(define (schml-literal->type x)
  (cond
    [(boolean? x) BOOL-TYPE]
    [(integer? x) INT-TYPE]
    [(null? x)    UNIT-TYPE]
    [else (error 'language/schml-literal->type "~a" x)]))

;; Types in the schml languages
(define-type  Base-Type (U Int Bool Unit))

(: base-type? (Any -> Boolean : Base-Type))
(define (base-type? x)
  (or (Int? x)
      (Bool? x)
      (Unit? x)))

(define-type+ Schml-Type ([Schml-Type* Listof]
			  [Schml-Type? Option])
  (U Dyn
     Base-Type
     Schml-Fn-Type
     Schml-Ref-Type
     Schml-Tuple-Type))

(define-type Schml-Fn-Type
  (Fn Index Schml-Type* Schml-Type))

(define-type Schml-Tuple-Type
  (STuple Index Schml-Type*))

(define-type Schml-Ref-Type
  (U (GRef  Schml-Type)
     (GVect Schml-Type)
     (MRef  Schml-Type)
     (MVect Schml-Type)))

(define-type Atomic-Schml-Type (U Unit Int Bool Dyn))

(: schml-type? (Any -> Boolean : Schml-Type))
(define (schml-type? x)
  (or (Dyn? x)
      (base-type? x)
      (schml-fn? x)
      (schml-ref? x)
      (schml-tuple? x)))
      

(define-predicate schml-type*? Schml-Type*)
#;(: schml-type*? (Any -> Boolean : Schml-Type*))
#;
(define (schml-type*? x)
  (or (null? x)
      (and (pair? x)
           (schml-type? (car x))
           (schml-type*? (cdr x)))))

(define-predicate schml-fn? Schml-Fn-Type)
(define-predicate schml-tuple? Schml-Tuple-Type)
#;(: schml-fn? (Any -> Boolean : Schml-Fn-Type))
#;(define (schml-fn? x)
   (and (Fn? x)
    (index? (Fn-arity x))
    (schml-type*? (Fn-fmls x))
    (schml-type? (Fn-ret x))))


(define-predicate schml-ref? Schml-Ref-Type)
#;(: schml-ref? (Any -> Boolean : Schml-Ref-Type))

#;
(define (schml-ref? x)
  (or (and (GRef? x)  (schml-type? (GRef-arg x)))
      (and (GVect? x) (schml-type? (GVect-arg x)))
      (and (MRef? x)  (schml-type? (MRef-arg x)))
      (and (MVect? x) (schml-type? (MVect-arg x)))))

(define-type+ Schml-Fml ([Schml-Fml* Listof])
  (Fml Uid Schml-Type))

(define-type ConsistentT (Schml-Type Schml-Type -> Boolean))
(: consistent? ConsistentT)
(define (consistent? t g)
  ;; Typed racket made me structure the code this way.
  ;; TODO change the names to be both-unit? ...
  (: both-unit? ConsistentT)
  (define (both-unit? t g) (and (Unit? t) (Unit? g)))
  (: both-bool? ConsistentT)
  (define (both-bool? t g) (and (Bool? t) (Bool? g)))
  (: both-int? ConsistentT)
  (define (both-int? t g) (and (Int? t) (Int? g)))
  (: consistent-fns? ConsistentT)
  (define (consistent-fns? t g)
    (and (Fn? t) (Fn? g)
         (= (Fn-arity t) (Fn-arity g))
         (andmap consistent? (Fn-fmls t) (Fn-fmls g))
         (consistent? (Fn-ret t) (Fn-ret g))))
  (: consistent-tuples? ConsistentT)
  (define (consistent-tuples? t g)
    (and (STuple? t) (STuple? g)
         (= (STuple-num t) (STuple-num g))
         (andmap consistent? (STuple-items t) (STuple-items g))))
  (: consistent-grefs? ConsistentT)
  (define (consistent-grefs? t g)
    (and (GRef? t) (GRef? g)
         (consistent? (GRef-arg t) (GRef-arg g))))
  (: consistent-gvects? ConsistentT)
  (define (consistent-gvects? t g)
    (and (GVect? t) (GVect? g)
         (consistent? (GVect-arg t) (GVect-arg g))))
  (or (Dyn? t)
      (Dyn? g)
      (both-unit? t g)
      (both-bool? t g)
      (both-int? t g)
      (consistent-fns? t g)
      (consistent-tuples? t g)
      (consistent-grefs? t g)
      (consistent-gvects? t g)))

#|
 Join :: type X type -> type
 This is the join of the least precise latice
     ⊑ latice example:
      Int --> Int
         /   \
        /     \
       /       \        Joins ↑
Dyn --> Int Int --> Dyn
       \       /        Meets ↓
        \     /
         \   /
      Dyn --> Dyn
           |
          Dyn
|#

(: join (Schml-Type Schml-Type . -> . Schml-Type))
(define (join t g)
  (cond
    [(Dyn? t) g] [(Dyn? g) t]
    [(and (Unit? t) (Unit? g)) UNIT-TYPE]
    [(and (Int? t) (Int? g)) INT-TYPE]
    [(and (Bool? t) (Bool? g)) BOOL-TYPE]
    [(and (Fn? t) (Fn? g) (= (Fn-arity t) (Fn-arity g)))
     (Fn (Fn-arity t)
         (map join (Fn-fmls t) (Fn-fmls g))
         (join (Fn-ret t) (Fn-ret g)))]
    [(and (STuple? t) (STuple? g) (= (STuple-num t) (STuple-num g)))
     (STuple (STuple-num t)
         (map join (STuple-items t) (STuple-items g)))]
    [(and (GRef? t) (GRef? g))
     (GRef (join (GRef-arg t) (GRef-arg g)))]
    [(and (GVect? t) (GVect? g))
     (join (GVect-arg t) (GVect-arg g))]
    [else (error 'join "Types are not consistent")]))


(define-forms
  (Coercion coercion)
  (Twosome type1 type2 lbl)
  ;; TODO Come up with a better name for this
  (Quote-Coercion const)
  (Compose-Coercions fst snd)
  ;; I am swithing to using the Cast and Interpreted Cast for the following
  ;; Forms
  ;(Coerce coercion expression) 
  ;(Interpreted-Coerce coercion expression)
  ;; Identity Cast
  ;; "Calculated No Op Cast"
  (Identity)
  (Id-Coercion-Huh E)
  (Id-Coercion)
  ;; Projection Coercion
  ;; "Project from dynamic at type blaming label if it fails"
  ;; G?ˡ in most papers
  ;; T?ˡ for this compiler
  (Project type label)
  ;; Injection Coercion
  ;; "Inject into the dynamic type at type"
  (Inject type)
  ;; Sequence Coercion
  ;; "Perform the first Coercion and then Another"
  (Sequence fst snd)
  ;; Fail Coercion
  ;; "Fail with the label"
  (Failed label)
  ;; Function Coercion
  ;; "Proxy a function call with args coercions and return coercion"
  ;; I am switching over to using the Fn form for this
  #;(Proxy-Fn arity args return)
  (Fn-Coercion-Arity c)
  (Fn-Coercion args return)
  (Fn-Coercion-Arg coercion index)
  (Fn-Coercion-Return coercion)
  ;;
  (CTuple num items)
  (Tuple-Coercion items)
  (Tuple-Coercion-Huh c)
  (Tuple-Coercion-Num c)
  (Tuple-Coercion-Item c indx)
  (Make-Tuple-Coercion make-uid t1 t2 lbl)
  (Compose-Tuple-Coercion Uid c1 c2)
  (Mediating-Coercion-Huh? c)
  ;; Guarded Reference Coercion
  ;; "Proxy a Guarded Reference's Reads and writes"
  (Ref read write)
  (Ref-Coercion read write)
  (Ref-Coercion-Read expression)
  (Ref-Coercion-Write ref)
  (Fn-Proxy arity coercion closure)
  (Fn-Proxy-Coercion expression)
  (Fn-Proxy-Closure expression)
  (Fn-Proxy-Huh expression)
  (Hybrid-Proxy apply closure coercion)
  (Hybrid-Proxy-Huh clos)
  (Hybrid-Proxy-Closure hybrid)
  (Hybrid-Proxy-Coercion hybrid)
  ;; Coercion Manipulation Stuff
  (Sequence-Coercion-Huh crcn)
  (Sequence-Coercion fst snd)
  (Sequence-Coercion-Fst seq)
  (Sequence-Coercion-Snd seq)
  (Project-Coercion type label)
  (Project-Coercion-Huh crcn)
  (Project-Coercion-Type prj)
  (Project-Coercion-Label prj)
  (Inject-Coercion type)
  (Inject-Coercion-Huh crnc)
  (Inject-Coercion-Type inj)
  (Failed-Coercion label)
  (Failed-Coercion-Huh crcn)
  (Failed-Coercion-Label fld)
  (Ref-Coercion-Huh crcn)
  (Fn-Coercion-Huh crcn)
  (Make-Coercion t1 t2 lbl)
  (Make-Fn-Coercion make-uid t1 t2 lbl)
  (Compose-Fn-Coercion comp-uid c1 c2))

(define-type Cast-Fml* (Listof Cast-Fml))
(define-type Cast-Fml (Fml Uid Schml-Type))

(define-type Cast-Literal (U Schml-Literal Blame-Label))

(define-type Src srcloc)

(define-type Tag-Symbol (U 'Int 'Bool 'Unit 'Fn 'Atomic 'Boxed 'GRef 'GVect 'STuple))

(define-type Schml-Coercion
  (Rec C (U Identity
            (Project Schml-Type Blame-Label)
            (Inject Schml-Type)
            (Sequence C C)
            (Failed Blame-Label)
            (Fn Index (Listof C) C)
            (Ref C C)
            (CTuple Index (Listof C)))))

(define IDENTITY : Identity (Identity))

(define-type Schml-Coercion* (Listof Schml-Coercion))

(define-type Data-Literal (U Integer String))

#|------------------------------------------------------------------------------
  Compact Types and Coercions are a compile time hash-consing of types
  They are introduced by hoist types in Language Cast-or-Coerce3.1
------------------------------------------------------------------------------|#

;; Represents the shallow tree structure of types where all subtrees
;; of the type are either and atomic type or a identifier for a type.
(define-type Compact-Type
  (U (Fn Index (Listof Prim-Type) Prim-Type)
     (STuple Index (Listof Prim-Type))
     (GRef Prim-Type) (MRef Prim-Type)
     (GVect Prim-Type) (MVect Prim-Type)))

;; Represent the shallow tree structure of coercions where all
;; subtrees of the type are either atomic types, the identity coercion
;; or coercion identifiers.
(define-type Compact-Coercion
  (U (Project Prim-Type Blame-Label)
     (Inject Prim-Type)
     (Sequence Immediate-Coercion Immediate-Coercion)
     (Failed Blame-Label)
     (Fn Index (Listof Immediate-Coercion) Immediate-Coercion)
     (CTuple Index (Listof Immediate-Coercion))
     (Ref Immediate-Coercion Immediate-Coercion)))

;; TODO (andre) a more descriptive name for this would be
;; Immediate-Type
(define-type Prim-Type (U Atomic-Schml-Type (Static-Id Uid)))

;; A type representing coercions that have already been
;; allocated at runntime or are small enought to fit into
;; a register at runtime. 
;; TODO (andre) since types are completely static consider changing
;; the type representation so that types are allocated as
;; untagged values. Doing so would simplify type case and
;; allow cheaper allocation of fails and injects at runtime.
;; (NOTE) This should be done after implementation of the non
;; N^2 implementation of guarded reference coercions because
;; that may require injects to carry blame labels thus reducing
;; the impact of this optimization.
(define-type Immediate-Coercion (U Identity (Static-Id Uid)))
 
(define-type Coercion/Prim-Type
  (Rec C (U Identity
            (Failed Blame-Label)
            (Project Prim-Type Blame-Label)
            (Inject Prim-Type)
            (Sequence C C)
            (Fn Index (Listof C) C)
            (Ref C C)
            (CTuple Index (Listof C)))))

(define-type Coercion/Prim-Type* (Listof Coercion/Prim-Type))

#;(define-type (Map-Expr E1 E2)
  (case->
   [(Type Schml-Type) -> (Type Schml-Type)]
   [(Quote Schml-Literal) -> (Quote Schml-Literal)]
   [(Quote Cast-Literal) -> (Quote Cast-Literal)]
   [(Quote-Coercion Schml-Coercion) -> (Quote-Coercion Schml-Coercion)]
   [(Quote-Coercion Immediate-Coercion) -> (Quote-Coercion Immediate-Coercion)]
   [(Code-Label Uid) -> (Code-Label Uid)]
   [(Var Uid) -> (Var Uid)]
   [(Static-Id Uid) -> (Static-Id Uid)]
   [No-Op -> No-Op]
   [Halt -> Halt]
   [Success -> Success] 
   [(Lambda (Listof Uid) E1) -> (Lambda (Listof Uid) E2)]
   [(Lambda (Listof (Fml Uid Schml-Type)) E1) ->
    (Lambda (Listof (Fml Uid Schml-Type)) E2)]
   [(App E1 (Listof E1)) -> (App E2 (Listof E2))]
   [(App-Code E1 (Listof E1)) -> (App-Code E2 (Listof E2))]
   [(App-Fn E1 (Listof E1)) -> (App-Fn E2 (Listof E2))]
   [(App-Fn-or-Proxy Uid E1 (Listof E1)) -> (App-Fn-or-Proxy Uid E2 (Listof E2))]
   [(App-Closure E1 E1 (Listof E1)) -> (App-Closure E2 E2 (Listof E2))]
   [(If E1 E1 E1) -> (If E2 E2 E2)]
   [(Observe E1 Schml-Type) -> (Observe E2 Schml-Type)]
   [(Blame E1) -> (Blame E2)]
   [(Repeat Uid E1 E1 E1) -> (Repeat Uid E2 E2 E2)]
   [(Op Schml-Prim (Listof E1)) -> (Op Schml-Prim (Listof E2))]
   [(Letrec (Listof (Pair Uid E1)) E1) -> (Letrec (Listof (Pair Uid E2)) E2)]
   [(Letrec (Listof (Bnd Uid Schml-Type E1)) E1) -> (Letrec (Listof (Bnd Uid Schml-Type E2)) E2)]
   [(Let (Listof (Pair Uid E1)) E1) -> (Let (Listof (Pair Uid E2)) E2)]
   [(Let (Listof (Bnd Uid Schml-Type E1)) E1) -> (Let (Listof (Bnd Uid Schml-Type E2)) E2)]
   [(Labels (Listof (Pair Uid (Code Uid* E1))) E1) ->
    (Labels (Listof (Pair Uid (Code Uid* E2))) E2)]
   [(Begin (Listof E1) E1) -> (Begin (Listof E2) E2)]
   [(Gbox E1) -> (Gbox E2)]
   [(Gunbox E1) -> (Gunbox E2)]
   [(Gbox-set! E1 E1) -> (Gbox-set! E2 E2)]
   [(Gvector E1 E1) -> (Gvector E2 E2)]
   [(Gvector-set! E1 E1 E1) -> (Gvector-set! E2 E2 E2)]
   [(Gvector-ref E1 E1) -> (Gvector-ref E2 E2)]
   [(Cast E1 (Twosome Schml-Type Schml-Type Blame-Label)) ->
    (Cast E2 (Twosome Schml-Type Schml-Type Blame-Label))]
   [(Cast E1 (Coercion Schml-Coercion)) ->
    (Cast E2 (Coercion Schml-Coercion))]
   [(Interpreted-Cast E1 (Twosome E1 E1 E1)) -> (Interpreted-Cast E2 (Twosome E2 E2 E2))]
   [(Interpreted-Cast E1 (Coercion E1)) -> (Interpreted-Cast E2 (Coercion E2))]
   [(Fn-Caster E1) -> (Fn-Caster E2)]
   [(Type-Dyn-Huh E1) -> (Type-Dyn-Huh E2)]
   [(Type-Tag E1) -> (Type-Tag E2)] 
   [(Type-Fn-arity E1) -> (Type-Fn-arity E2)]
   [(Type-Fn-arg E1 E1) -> (Type-Fn-arg E2 E2)]
   [(Type-Fn-return E1) -> (Type-Fn-return E2)]
   [(Type-Fn-Huh E1) -> (Type-Fn-Huh E2)]
   [(Type-GVect-Huh E1) -> (Type-GVect-Huh E2)]
   [(Type-GRef-Huh E1) -> (Type-GRef-Huh E2)]
   [(Type-GRef-Of E1) -> (Type-GRef-Of E2)]
   [(Type-GVect-Of E1) -> (Type-GRef-Of E2)]
   #;[(Let-Static* (Listof (Pair Uid Compact-Type))
        (Listof (Pair Uid Compact-Coercion)) E1)
      -> (Let-Static* (Listof (Pair Uid Compact-Type))
           (Listof (Pair Uid Compact-Coercion)) E2)]
   [(Dyn-tag E1) -> (Dyn-tag E2)]
   [(Dyn-immediate E1) -> (Dyn-immediate E2)]
   [(Dyn-type E1) -> (Dyn-type E2)]
   [(Dyn-value E1) -> (Dyn-value E2)]
   [(Fn-Proxy (List Index Uid) E1 E1) ->
    (Fn-Proxy (List Index Uid) E2 E2)]
   [(Fn-Proxy-Huh E1) ->
    (Fn-Proxy-Huh E2)]
   [(Fn-Proxy-Closure E1) ->
    (Fn-Proxy-Closure E2)]
   [(Fn-Proxy-Coercion E1) ->
    (Fn-Proxy-Coercion E2)]
   [(Compose-Coercions E1 E1) -> (Compose-Coercions E2 E2)]
   [(Compose-Fn-Coercion Uid E1 E1) ->
    (Compose-Fn-Coercion Uid E2 E2)]
   [(Fn-Coercion-Arity E1) -> (Fn-Coercion-Arity E2)]
   [(Fn-Coercion (Listof E1) E1) -> (Fn-Coercion (Listof E2) E2)]
   [(Fn-Coercion-Arg E1 E1) -> (Fn-Coercion-Arg E2 E2)]
   [(Fn-Coercion-Return E1) -> (Fn-Coercion-Return E2)]
   [(Ref-Coercion E1 E1) -> (Ref-Coercion E2 E2)]
   [(Ref-Coercion-Read E1) -> (Ref-Coercion-Read E2)]
   [(Ref-Coercion-Write E1) -> (Ref-Coercion-Write E2)]
   [(Hybrid-Proxy Uid E1 E1) -> (Hybrid-Proxy Uid E1 E2)]
   [(Hybrid-Proxy-Huh E1) ->(Hybrid-Proxy-Huh E2)] 
   [(Hybrid-Proxy-Closure E1) -> (Hybrid-Proxy-Closure E2)] 
   [(Hybrid-Proxy-Coercion E1) -> (Hybrid-Proxy-Coercion E2)]
   [(Sequence-Coercion E1 E1) -> (Sequence-Coercion E2 E2)]
   [(Sequence-Coercion-Huh E1) -> (Sequence-Coercion-Huh E2)]
   [(Sequence-Coercion-Fst E1) -> (Sequence-Coercion-Fst E2)]
   [(Sequence-Coercion-Snd E1) -> (Sequence-Coercion-Snd E2)]
   [(Project-Coercion E1 E1) -> (Project-Coercion E2 E2)]
   [(Project-Coercion-Huh E1) ->   (Project-Coercion-Huh E2)]
   [(Project-Coercion-Type E1) -> (Project-Coercion-Type E2)]
   [(Project-Coercion-Label E1) -> (Project-Coercion-Label E2)]
   [(Inject-Coercion E1) -> (Inject-Coercion E2)]
   [(Inject-Coercion-Huh E1) -> (Inject-Coercion-Huh E2)]
   [(Inject-Coercion-Type E1) -> (Inject-Coercion-Type E2)]
   [(Failed-Coercion E1) ->   (Failed-Coercion E2)]
   [(Failed-Coercion-Huh E1) -> (Failed-Coercion-Huh E2)]
   [(Failed-Coercion-Label E1) -> (Failed-Coercion-Label E2)]
   [(Ref-Coercion-Huh E1) -> (Ref-Coercion-Huh E2)]
   [(Fn-Coercion-Huh E1) -> (Fn-Coercion-Huh E2)]
   [(Make-Coercion E1 E1 E1) -> (Make-Coercion E2 E2 E2)]
   [(Make-Fn-Coercion Uid E1 E1 E1) -> (Make-Fn-Coercion Uid E2 E2 E2)]
   [(Compose-Fn-Coercion Uid E1 E1) -> (Compose-Fn-Coercion Uid E2 E2)]
   [(Id-Coercion-Huh E1) -> (Id-Coercion-Huh E2)]
   [Id-Coercion -> Id-Coercion]   
   [(Tag Tag-Symbol) -> (Tag Tag-Symbol)]))

;; TODO submit a patch to racket so that this isn't necisarry
;; adhoc polymorphism encoded by case lambda across all


;(: map-expr (All (A B) (A -> B) -> (Map-Expr A B)))
#;(define ((map-expr f) e)
  (match e
    [(and c (or (Type _) (Quote _) (Quote-Coercion _)
                (Code-Label _) (Var _) (Static-Id _)
                (Tag _)))
     c]
    [(and c (or (No-Op) (Halt) (Success))) c]
    ;; Don't use compound forms anymore
    [(Lambda i* e) (Lambda i* (f e))]
    [(App e e*) (App (f e) (map f e*))]
    [(App-Code e e*) (App-Code (f e) (map f e*))]
    [(App-Fn e e*) (App-Fn (f e) (map f e*))]
    [(App-Fn-or-Proxy u e e*) (App-Fn-or-Proxy u (f e) (map f e*))]
    [(Fn-Proxy i e1 e2)
     (Fn-Proxy i (f e1) (f e2))]
    [(Fn-Proxy-Huh e) 
     (Fn-Proxy-Huh (f e))]
    [(Fn-Proxy-Closure e)
     (Fn-Proxy-Closure (f e))]
    [(Fn-Proxy-Coercion e)
     (Fn-Proxy-Coercion (f e))]
    [(If e1 e2 e3) (If (f e1) (f e2) (f e3))]
    [(Op p e*) (Op p (map f e*))]
    [(Letrec b* e) (Letrec (map (map-bnd f) b*) (f e))]
    [(Let b* e) (Let (map (map-bnd f) b*) (f e))]
    [(Labels b* e) (Labels (map (map-bnd-code f) b*) (f e))]
    [(Begin e* e) (Begin (map f e*) (f e))]
    [(Gbox e) (Gbox (f e))]
    [(Gunbox e) (Gunbox (f e))]
    [(Gbox-set! e1 e2) (Gbox-set! (f e1) (f e2))]
    [(Gvector e1 e2) (Gvector (f e1) (f e1))]
    [(Gvector-set! e1 e2 e3) (Gvector-set! (f e1) (f e2) (f e3))]
    [(Gvector-ref e1 e2) (Gvector-ref (f e1) (f e2))]
    [(Cast e i) (Cast (f e) i)]
    [(Interpreted-Cast e1 (Twosome e2 e3 e4))
     (Interpreted-Cast (f e1) (Twosome (f e2) (f e3) (f e4)))]
    [(Interpreted-Cast e1 (Coercion e2))
     (Interpreted-Cast (f e1) (Coercion (f e2)))]
    [(Compose-Coercions e1 e2) (Compose-Coercions (f e1) (f e2))]
    [(Compose-Fn-Coercion u c1 c2)
     (Compose-Fn-Coercion u (f c1) (f c2))]
    [(Id-Coercion-Huh e) (Id-Coercion-Huh (f e))]
    [(and id (Id-Coercion)) id]
    [(Fn-Caster e) (Fn-Caster (f e))]
    [(Type-Dyn-Huh e) (Type-Dyn-Huh (f e))]
    [(Type-Tag e) (Type-Tag (f e))] 
    [(Type-Fn-arity e) (Type-Fn-arity (f e))]
    [(Type-Fn-arg e1 e2) (Type-Fn-arg (f e1) (f e2))]
    [(Type-Fn-return e) (Type-Fn-return (f e))]
    [(Type-Fn-Huh e) (Type-Fn-Huh (f e))]
    [(Type-GVect-Huh e) (Type-GVect-Huh (f e))]
    [(Type-GRef-Huh e) (Type-GRef-Huh (f e))]
    [(Type-GRef-Of e) (Type-GRef-Of (f e))]
    [(Type-GVect-Of e) (Type-GRef-Of (f e))]
    [(App-Closure e1 e2 e*) (App-Closure (f e1) (f e2) (map f e*))]
    [(Let-Static* bt bc e) (Let-Static* bt bc (f e))]
    [(Dyn-tag e) (Dyn-tag (f e))]
    [(Dyn-immediate e) (Dyn-immediate (f e))]
    [(Dyn-type e) (Dyn-type (f e))]
    [(Dyn-value e) (Dyn-value (f e))]
    [other (error 'forms/map-expr "match failed: ~a" other)]))

(define-type (Map-Bnd E1 E2)
  (case->
   [(Bnd Uid Schml-Type E1) -> (Bnd Uid Schml-Type E2)]
   [(Pair Uid E1) -> (Pair Uid E2)]))

(: map-bnd (All (A B) (A -> B) -> (Map-Bnd A B)))
(define ((map-bnd f) b)
  (match b
    [(Bnd i t e) (Bnd i t (f e))]
    [(cons i e) (cons i (f e))]))


;                                                                                                                                
;                                                                                                                                
;                                                                                                                                
;                        ;                 ;                 ;                                                  ;                
;                        ;                 ;       ;         ;                                                  ;          ;     
;                                                  ;                                                            ;          ;     
;   ; ;;;      ; ;;;   ;;;     ;;;;;;    ;;;     ;;;;;;    ;;;     ;     ;    ;;;     ;;;;;              ; ;;;  ;    ;   ;;;;;;  
;   ;;   ;     ;;   ;    ;     ;  ;  ;     ;       ;         ;      ;   ;    ;   ;   ;     ;             ;;   ; ;  ;;      ;     
;   ;     ;    ;         ;     ;  ;  ;     ;       ;         ;      ;   ;   ;     ;  ;                   ;      ; ;        ;     
;   ;     ;    ;         ;     ;  ;  ;     ;       ;         ;      ;   ;   ;     ;  ;;;;                ;      ;;;        ;     
;   ;     ;    ;         ;     ;  ;  ;     ;       ;         ;       ; ;    ;;;;;;;     ;;;;             ;      ;  ;       ;     
;   ;     ;    ;         ;     ;  ;  ;     ;       ;         ;       ; ;    ;              ;             ;      ;   ;      ;     
;   ;;   ;     ;         ;     ;  ;  ;     ;       ;         ;       ; ;     ;    ;  ;     ;     ;;      ;      ;    ;     ;     
;   ; ;;;      ;      ;;;;;;;  ;  ;  ;  ;;;;;;;     ;;;   ;;;;;;;     ;       ;;;;    ;;;;;      ;;      ;      ;     ;     ;;;  
;   ;                                                                                                                            
;   ;                                                                                                                            
;   ;                                                                                                                            
;                                                                                                                                


(: schml-primitive->type
   (-> Schml-Primitive (Fn Index (Listof (U Int Bool)) (U Int Bool Unit))))
(define (schml-primitive->type p)
  (cond
   [(IntxInt->Bool-primitive? p) INTxINT->BOOL-TYPE]
   [(IntxInt->Int-primitive? p)  INTxINT->INT-TYPE]
   [(->Int-primitive? p) ->INT-TYPE]
   [(timer-primitive? p)         ->UNIT-TYPE]))




#|-----------------------------------------------------------------------------
We are going to UIL
-----------------------------------------------------------------------------|#

(define-type UIL-Prim  (U Schml-Prim Array-Prim))
(define-type UIL-Prim! (U Schml-Prim! Array-Prim! Print-Prim! Bottom-Prim))
(define-predicate uil-prim-effect? UIL-Prim!)
(define-predicate uil-prim-value? UIL-Prim)

(define-type UIL-Expr-Prim (U Array-Prim IxI->I-Prim ->I-Prim))

(define-type Array-Prim (U 'Alloc 'Array-ref))
(define-type Array-Prim! 'Array-set!)
(define-type Print-Prim! (U 'Printf 'Print))
(define-type Bottom-Prim (U 'Exit))

(define-type (UIL-Op E) (Op UIL-Prim (Listof E)))
(define-type (UIL-Op! E) (Op UIL-Prim! (Listof E)))


(define-type Data0-Lang
  (Prog (List String Natural Schml-Type)
        (GlobDecs Uid* D0-Expr)))

;(define-type D0-Bnd-Code* (Listof D0-Bnd-Code))
;(define-type D0-Bnd-Code (Pairof Uid D0-Code))
;(define-type D0-Code (Code Uid* D0-Expr))
;
;(define-type D0-Expr
;  (Rec E (U (Labels D0-Bnd-Code* E)
;            (Let D0-Bnd* E)
;	    (App-Code E (Listof E))
;            (UIL-Op! E)
;            (UIL-Op E)
;	    (If E E E)
;	    (Begin D0-Expr* E)
;            (Repeat Uid E E E)
;	    (Var Uid)
;	    (Code-Label Uid)
;	    (Quote D0-Literal)
;            (Assign Uid E)
;            Halt
;            Success)))
;
;(define-type D0-Expr* (Listof D0-Expr))
;(define-type D0-Bnd* (Listof D0-Bnd))
;(define-type D0-Bnd  (Pairof Uid D0-Expr))
;(define-type D0-Literal Data-Literal)


;                                                                                                                                                                             
;                                                                                                                                                                             
;                                                                                                                                                                             
;                                                                                                                                   ;;;;                     ;                
;                                ;                                                                                                 ;;   ;                    ;          ;     
;                                ;                                                                                                 ;                         ;          ;     
;     ;;;      ;;;;    ;;;;;   ;;;;;;              ;;;      ; ;;;             ;;;      ;;;      ;;;      ; ;;;    ;;;      ;;;    ;                   ; ;;;  ;    ;   ;;;;;;  
;    ;   ;    ;    ;  ;     ;    ;                ;   ;     ;;   ;           ;   ;    ;   ;    ;   ;     ;;   ;  ;   ;    ;   ;   ; ;;;;              ;;   ; ;  ;;      ;     
;   ;              ;  ;          ;               ;     ;    ;               ;        ;     ;  ;     ;    ;      ;        ;     ;  ;;   ;;             ;      ; ;        ;     
;   ;         ;;;;;;  ;;;;       ;        ;;;;   ;     ;    ;        ;;;;   ;        ;     ;  ;     ;    ;      ;        ;     ;  ;     ;             ;      ;;;        ;     
;   ;        ;;    ;     ;;;;    ;               ;     ;    ;               ;        ;     ;  ;;;;;;;    ;      ;        ;;;;;;;  ;     ;             ;      ;  ;       ;     
;   ;        ;     ;        ;    ;               ;     ;    ;               ;        ;     ;  ;          ;      ;        ;        ;     ;             ;      ;   ;      ;     
;    ;   ;   ;    ;;  ;     ;    ;                ;   ;     ;                ;   ;    ;   ;    ;    ;    ;       ;   ;    ;    ;   ;   ;;     ;;      ;      ;    ;     ;     
;     ;;;     ;;;; ;   ;;;;;      ;;;              ;;;      ;                 ;;;      ;;;      ;;;;     ;        ;;;      ;;;;     ;;;;      ;;      ;      ;     ;     ;;;  
;                                                                                                                                                                             
;                                                                                                                                                                             
;                                                                                                                                                                             
;                                                                                                                                                                             



#|-----------------------------------------------------------------------------+
| Language/Cast3 created by interpret-casts                                    |
+-----------------------------------------------------------------------------|#



(define-type Cast-or-Coerce6-Lang
  (Prog (List String Natural Schml-Type)
        (Let-Static* CoC6-Bnd-Type* CoC6-Bnd-Crcn* CoC6-Expr)))

(define-type CoC6-Expr
  (Rec E (U
          ;; Closure-Operations
          (LetP CoC6-Bnd-Procedure* (LetC CoC6-Bnd-Closure* E))
          (LetP CoC6-Bnd-Procedure* E)
          (Closure-code E)
          (Closure-caster E)
          (Closure-ref Uid Uid)
          (App-Closure E E (Listof E))
          ;; Code Labels
          (Code-Label Uid)
          (Labels CoC6-Bnd-Code* E)
          (App-Code E (Listof E))
          ;; Functions as an interface
          (Lambda Uid* (Castable (Option Uid) E))
          (Fn-Caster E)
          (App-Fn E (Listof E))
          ;; Our Lovely Function Proxy Representation
          (App-Fn-or-Proxy Uid E (Listof E))
          (Hybrid-Proxy Uid E E)
          (Hybrid-Proxy-Huh E)
          (Hybrid-Proxy-Closure E)
          (Hybrid-Proxy-Coercion E)
          (Fn-Proxy Index E E)
          (Fn-Proxy-Huh E)
          (Fn-Proxy-Closure E)
          (Fn-Proxy-Coercion E)
          ;; Coercions
          (Quote-Coercion Immediate-Coercion)
          ;(Compose-Coercions E E)
          (Id-Coercion-Huh E)
          (Fn-Coercion-Huh E)
          (Make-Fn-Coercion Uid E E E)
          (Compose-Fn-Coercion Uid E E)
          (Fn-Coercion (Listof E) E)
          (Fn-Coercion-Arity E)
          (Fn-Coercion-Arg E E)
          (Fn-Coercion-Return E)
          (Ref-Coercion E E)
          (Ref-Coercion-Huh E)
          (Ref-Coercion-Read E)
          (Ref-Coercion-Write E)
          (Sequence-Coercion E E)
          (Sequence-Coercion-Huh E)
          (Sequence-Coercion-Fst E)
          (Sequence-Coercion-Snd E)
          (Project-Coercion E E)
          (Project-Coercion-Huh E)
          (Project-Coercion-Type E)
          (Project-Coercion-Label E)
          (Inject-Coercion E)
          (Inject-Coercion-Type E)
          (Inject-Coercion-Huh E)
          (Failed-Coercion E)
          (Failed-Coercion-Huh E)
          (Failed-Coercion-Label E)
          ;;Type operations
          (Type Prim-Type)
          (Type-Dyn-Huh E)
          (Type-Fn-Huh E)
          (Type-Fn-arity E)
          (Type-Fn-arg E E)
          (Type-Fn-return E)
          (Type-GRef-Huh E)
          (Type-GRef-Of  E)
          (Type-GVect-Huh E)
          (Type-GVect-Of E)
          ;; Tags are exposed before specify This is bad
          ;; TODO fix this after the deadline
          (Type-Tag E)
          (Tag Tag-Symbol)
          ;;(Type-Ctr-Case E Type-Ctr-Case-Clause* E)
          ;;(Dyn-Case E Type-Ctr-Clause* E)
          ;; Dynamic as a value
          (Dyn-tag E)
          (Dyn-immediate E)
          (Dyn-type E)
          (Dyn-value E)
          (Dyn-make E E)
          ;; binding 
	  (Let CoC6-Bnd-Data* E)
          (Var Uid)
          ;; Controll Flow
          (If E E E)
          (Begin CoC6-Expr* E)
          (Repeat Uid E E E)
          ;;Primitives
          (Op Schml-Primitive (Listof E))
          (Quote Cast-Literal)
          ;; Casts with different ways of getting the same semantics
	  ;;(Cast E (Twosome Schml-Type Schml-Type Blame-Label))
          ;;(Cast E (Coercion Schml-Coercion))
          ;;(Interpreted-Cast E (Twosome E E E))
          ;;(Interpreted-Cast E (Coercion E))
          ;; Observations
          (Blame E)
          (Observe E Schml-Type)
          ;; Unguarded-Representation
          (Unguarded-Box E)
          (Unguarded-Box-Ref E)
          (Unguarded-Box-Set! E E)
          (Unguarded-Vect E E)
          (Unguarded-Vect-Ref E E)
          (Unguarded-Vect-Set! E E E)
          (Guarded-Proxy-Huh E)
          (Guarded-Proxy E (Twosome E E E))
          (Guarded-Proxy E (Coercion E))
          (Guarded-Proxy-Ref E)
          (Guarded-Proxy-Source E)
          (Guarded-Proxy-Target E)
          (Guarded-Proxy-Blames E)
          (Guarded-Proxy-Coercion E)
          ;;
          (Create-tuple (Listof E))
          (Tuple-proj E Index)
          (Tuple-Coercion-Huh E)
          (Tuple-Coercion-Num E)
          (Tuple-Coercion-Item E Index)
          (Coerce-Tuple Uid E E)
          (Cast-Tuple Uid E E E E)
          (Type-Tuple-Huh E)
          (Type-Tuple-num E)
          (Type-Tuple-item E Index)
          (Make-Tuple-Coercion Uid E E E)
          (Compose-Tuple-Coercion Uid E E)
          (Mediating-Coercion-Huh? E))))



(define-type CoC6-Expr* (Listof CoC6-Expr))
(define-type CoC6-Code (Code Uid* CoC6-Expr))
(define-type CoC6-Bnd-Code (Pairof Uid CoC6-Code))
(define-type CoC6-Bnd-Code* (Listof CoC6-Bnd-Code))
(define-type CoC6-Bnd-Data  (Pairof Uid CoC6-Expr))
(define-type CoC6-Bnd-Data* (Listof CoC6-Bnd-Data))

(define-type CoC6-Procedure
  (Procedure Uid Uid* Uid (Option Uid) Uid* CoC6-Expr))
(define-type CoC6-Closure
  (Closure-Data CoC6-Expr (Option CoC6-Expr) CoC6-Expr*))
(define-type CoC6-Bnd-Procedure (Pairof Uid CoC6-Procedure))
(define-type CoC6-Bnd-Procedure* (Listof CoC6-Bnd-Procedure))
(define-type CoC6-Bnd-Closure (Pairof Uid CoC6-Closure))
(define-type CoC6-Bnd-Closure* (Listof CoC6-Bnd-Closure))
(define-type CoC6-Bnd-Type  (Pairof Uid Compact-Type))
(define-type CoC6-Bnd-Type* (Listof CoC6-Bnd-Type))
(define-type CoC6-Bnd-Crcn  (Pairof Uid Compact-Coercion))
(define-type CoC6-Bnd-Crcn* (Listof CoC6-Bnd-Crcn))



;                                                                                   
;                                                                                   
;                                                                                   
;         ;                               ;;;                      ;                
;         ;             ;                ;   ;                     ;          ;     
;         ;             ;               ;     ;                    ;          ;     
;     ;;; ;    ;;;;   ;;;;;;     ;;;;   ;     ;             ; ;;;  ;    ;   ;;;;;;  
;    ;   ;;   ;    ;    ;       ;    ;  ;  ;; ;             ;;   ; ;  ;;      ;     
;   ;     ;        ;    ;            ;  ;  ;; ;             ;      ; ;        ;     
;   ;     ;   ;;;;;;    ;       ;;;;;;  ;     ;             ;      ;;;        ;     
;   ;     ;  ;;    ;    ;      ;;    ;  ;     ;             ;      ;  ;       ;     
;   ;     ;  ;     ;    ;      ;     ;  ;     ;             ;      ;   ;      ;     
;    ;   ;;  ;    ;;    ;      ;    ;;   ;   ;      ;;      ;      ;    ;     ;     
;     ;;; ;   ;;;; ;     ;;;    ;;;; ;    ;;;       ;;      ;      ;     ;     ;;;  
;                                                                                   
;                                                                                   
;                                                                                   
;                                                                                   


(define-type D0-Bnd-Code* (Listof D0-Bnd-Code))
(define-type D0-Bnd-Code (Pairof Uid D0-Code))
(define-type D0-Code (Code Uid* D0-Expr))

(define-type D0-Expr
  (Rec E (U (Labels D0-Bnd-Code* E)
            (Let D0-Bnd* E)
	    (App-Code E (Listof E))
            (UIL-Op! E)
            (UIL-Op E)
	    (If E E E)
	    (Begin D0-Expr* E)
            (Repeat Uid E E E)
	    (Var Uid)
	    (Code-Label Uid)
	    (Quote D0-Literal)
            (Assign Uid E)
            Halt
            Success)))

(define-type D0-Expr* (Listof D0-Expr))
(define-type D0-Bnd* (Listof D0-Bnd))
(define-type D0-Bnd  (Pairof Uid D0-Expr))
(define-type D0-Literal Data-Literal)



;                                                                                                                                                                                                                 
;                                                                                                                                                                                                                 
;                                                                                                                                                                                                                 
;         ;                                                                                                                                            ;                                         ;                
;         ;             ;                                                                                                  ;                 ;         ;                                         ;          ;     
;         ;             ;                                                                                                  ;                 ;                                                   ;          ;     
;     ;;; ;    ;;;;   ;;;;;;     ;;;;              ; ;;;    ;;;    ; ;;;      ; ;;;    ;;;     ;;;;;     ;;;    ; ;;;;   ;;;;;;     ;;;;   ;;;;;;    ;;;       ;;;    ; ;;;;              ; ;;;  ;    ;   ;;;;;;  
;    ;   ;;   ;    ;    ;       ;    ;             ;;   ;  ;   ;   ;;   ;     ;;   ;  ;   ;   ;     ;   ;   ;   ;;   ;;    ;       ;    ;    ;         ;      ;   ;   ;;   ;;             ;;   ; ;  ;;      ;     
;   ;     ;        ;    ;            ;             ;      ;     ;  ;     ;    ;      ;     ;  ;        ;     ;  ;     ;    ;            ;    ;         ;     ;     ;  ;     ;             ;      ; ;        ;     
;   ;     ;   ;;;;;;    ;       ;;;;;;    ;;;;     ;      ;     ;  ;     ;    ;      ;     ;  ;;;;     ;     ;  ;     ;    ;       ;;;;;;    ;         ;     ;     ;  ;     ;             ;      ;;;        ;     
;   ;     ;  ;;    ;    ;      ;;    ;             ;      ;;;;;;;  ;     ;    ;      ;;;;;;;     ;;;;  ;;;;;;;  ;     ;    ;      ;;    ;    ;         ;     ;     ;  ;     ;             ;      ;  ;       ;     
;   ;     ;  ;     ;    ;      ;     ;             ;      ;        ;     ;    ;      ;              ;  ;        ;     ;    ;      ;     ;    ;         ;     ;     ;  ;     ;             ;      ;   ;      ;     
;    ;   ;;  ;    ;;    ;      ;    ;;             ;       ;    ;  ;;   ;     ;       ;    ;  ;     ;   ;    ;  ;     ;    ;      ;    ;;    ;         ;      ;   ;   ;     ;     ;;      ;      ;    ;     ;     
;     ;;; ;   ;;;; ;     ;;;    ;;;; ;             ;        ;;;;   ; ;;;      ;        ;;;;    ;;;;;     ;;;;   ;     ;     ;;;    ;;;; ;     ;;;   ;;;;;;;    ;;;    ;     ;     ;;      ;      ;     ;     ;;;  
;                                                                  ;                                                                                                                                              
;                                                                  ;                                                                                                                                              
;                                                                  ;                                                                                                                                              
;                                                                                                                                                                                                                 

;; The Representation of functional types is an array
(define l:FN-ARITY-INDEX 0)
(define l:FN-RETURN-INDEX 1)
(define l:FN-FMLS-OFFSET 2)

;; The representation of tuple types is an array
(define l:TUPLE-NUM-INDEX 0)
(define l:TUPLE-ITEMS-OFFSET 1)

;; The representation of tagged structure types
;; My thought is that types can be allocated statically
;; so there doesn't really need to be much though put
;; it may even be worth not tagging them and just laying
;; the types explicitly;
(define l:TYPE-TAG-MASK #b111)
(define l:TYPE-FN-TAG #b000)
(define l:TYPE-GREF-TAG #b001)
(define l:TYPE-GVECT-TAG #b010)
(define l:TYPE-TUPLE-TAG #b011)
;; Hypothetical extensions to type tags
;; Though more organization could le
;;(define TYPE-GVECT-TAG #b010)
;;(define TYPE-MREF-TAG #b011)
;;(define TYPE-MVECT-TAG #b100)
;;(define TYPE-IARRAY-TAG #b101)
;;(define TYPE-MU-TAG #b110)

(define l:TYPE-ATOMIC-TAG #b111) ;; This should be TYPE-IMDT-TAG
;; Immediate types are tagged with #b111
(define l:TYPE-DYN-RT-VALUE #b0111)
(define l:TYPE-INT-RT-VALUE #b1111)
(define l:TYPE-BOOL-RT-VALUE #b10111)
(define l:TYPE-UNIT-RT-VALUE #b11111)

;; The representation of Dynamic Immediates
(define l:DYN-TAG-MASK  #b111)
(define l:DYN-IMDT-SHIFT 3)
(define l:DYN-BOXED-TAG #b000)
(define l:DYN-INT-TAG   #b001)
(define l:DYN-UNIT-TAG  #b010)
(define l:DYN-BOOL-TAG  #b111)

;; Boxed Dynamics are just a cons cell
(define l:DYN-BOX-SIZE 2)
(define l:DYN-VALUE-INDEX 0)
(define l:DYN-TYPE-INDEX 1)

;; Immediates
(define l:FALSE-IMDT #b000)
(define l:TRUE-IMDT #b001)
(define l:UNIT-IMDT #b000)
;; Unreachable Value
(define l:UNDEF-IMDT 0)

;; Guarded Representation
(define l:GREP-TAG-MASK #b111)
(define l:UGBOX-SIZE 1)
(define l:UGBOX-VALUE-INDEX 0)
(define l:UGBOX-TAG #b000)
(define l:GPROXY-TAG  #b001)
(define l:GPROXY/COERCION-SIZE 2)
(define l:GPROXY/TWOSOME-SIZE  4)
(define l:GPROXY-FOR-INDEX 0)
(define l:GPROXY-COERCION-INDEX 1)
(define l:GPROXY-FROM-INDEX 1)
(define l:GPROXY-TO-INDEX 2)
(define l:GPROXY-BLAMES-INDEX 3)
(define l:UGVECT-SIZE #f)
(define l:UGVECT-TAG #b000)
(define l:UGVECT-SIZE-INDEX 0)
(define l:UGVECT-OFFSET 1)

(define l:TUPLE-TAG #b000)

;; GREF Type Representation
(define l:TYPE-GREF-SIZE  1)
(define l:GREF-TO-INDEX 0)

;; GVECT Type Representation
(define l:TYPE-GVECT-SIZE  1)
(define l:GVECT-TO-INDEX 0)

;; Closure representation
(define l:CLOS-CODE-INDEX 0)
(define l:CLOS-CSTR-INDEX 1)
(define l:CLOS-FVAR-OFFSET 2)

;; Function Proxy Representation
(define l:HYBRID-PROXY-CRCN-SIZE 3)
(define l:HYBRID-PROXY-CODE-INDEX 0)
(define l:HYBRID-PROXY-CLOS-INDEX 1)
(define l:HYBRID-PROXY-CRCN-INDEX 2)

;; Shifting for secondary tags
(define l:SECOND-TAG-SHIFT 3)




;                                                                                                                                                                                                                                            
;                                                                                                                                                                                                                                            
;                                                                                                                                                                                                                                            
;                                          ;         ;;;                                                                                                                          ;                                         ;                
;                                          ;        ;                                                                                                 ;                 ;         ;                                         ;          ;     
;                                                   ;                                                                                                 ;                 ;                                                   ;          ;     
;    ;;;;;   ; ;;;      ;;;      ;;;     ;;;      ;;;;;;  ;     ;             ; ;;;    ;;;    ; ;;;      ; ;;;    ;;;     ;;;;;     ;;;    ; ;;;;   ;;;;;;     ;;;;   ;;;;;;    ;;;       ;;;    ; ;;;;              ; ;;;  ;    ;   ;;;;;;  
;   ;     ;  ;;   ;    ;   ;    ;   ;      ;        ;      ;   ;;             ;;   ;  ;   ;   ;;   ;     ;;   ;  ;   ;   ;     ;   ;   ;   ;;   ;;    ;       ;    ;    ;         ;      ;   ;   ;;   ;;             ;;   ; ;  ;;      ;     
;   ;        ;     ;  ;     ;  ;           ;        ;      ;   ;              ;      ;     ;  ;     ;    ;      ;     ;  ;        ;     ;  ;     ;    ;            ;    ;         ;     ;     ;  ;     ;             ;      ; ;        ;     
;   ;;;;     ;     ;  ;     ;  ;           ;        ;      ;   ;     ;;;;     ;      ;     ;  ;     ;    ;      ;     ;  ;;;;     ;     ;  ;     ;    ;       ;;;;;;    ;         ;     ;     ;  ;     ;             ;      ;;;        ;     
;      ;;;;  ;     ;  ;;;;;;;  ;           ;        ;       ; ;;              ;      ;;;;;;;  ;     ;    ;      ;;;;;;;     ;;;;  ;;;;;;;  ;     ;    ;      ;;    ;    ;         ;     ;     ;  ;     ;             ;      ;  ;       ;     
;         ;  ;     ;  ;        ;           ;        ;       ; ;               ;      ;        ;     ;    ;      ;              ;  ;        ;     ;    ;      ;     ;    ;         ;     ;     ;  ;     ;             ;      ;   ;      ;     
;   ;     ;  ;;   ;    ;    ;   ;   ;      ;        ;        ;;               ;       ;    ;  ;;   ;     ;       ;    ;  ;     ;   ;    ;  ;     ;    ;      ;    ;;    ;         ;      ;   ;   ;     ;     ;;      ;      ;    ;     ;     
;    ;;;;;   ; ;;;      ;;;;     ;;;    ;;;;;;;     ;        ;;               ;        ;;;;   ; ;;;      ;        ;;;;    ;;;;;     ;;;;   ;     ;     ;;;    ;;;; ;     ;;;   ;;;;;;;    ;;;    ;     ;     ;;      ;      ;     ;     ;;;  
;            ;                                               ;                                ;                                                                                                                                              
;            ;                                               ;                                ;                                                                                                                                              
;            ;                                             ;;                                 ;                                                                                                                                              
;                                                                                                                                                                                                                                            





;; Only allocate each of these once
(define FN-ARITY-INDEX        (Quote l:FN-ARITY-INDEX))
(define FN-RETURN-INDEX       (Quote l:FN-RETURN-INDEX))
(define FN-FMLS-OFFSET        (Quote l:FN-FMLS-OFFSET))

(define TYPE-TAG-MASK         (Quote l:TYPE-TAG-MASK))
(define TYPE-FN-TAG           (Quote l:TYPE-FN-TAG))
(define TYPE-ATOMIC-TAG       (Quote l:TYPE-ATOMIC-TAG))
(define TYPE-DYN-RT-VALUE     (Quote l:TYPE-DYN-RT-VALUE))
(define TYPE-INT-RT-VALUE     (Quote l:TYPE-INT-RT-VALUE))
(define TYPE-BOOL-RT-VALUE    (Quote l:TYPE-BOOL-RT-VALUE))
(define TYPE-UNIT-RT-VALUE    (Quote l:TYPE-UNIT-RT-VALUE))
(define TYPE-GREF-SIZE        (Quote l:TYPE-GREF-SIZE))
(define TYPE-GREF-TAG         (Quote l:TYPE-GREF-TAG))
(define TYPE-GVECT-SIZE       (Quote l:TYPE-GVECT-SIZE))
(define TYPE-GVECT-TAG        (Quote l:TYPE-GVECT-TAG))
(define TYPE-TUPLE-TAG        (Quote l:TYPE-TUPLE-TAG))
(define DYN-TAG-MASK          (Quote l:DYN-TAG-MASK))
(define DYN-BOXED-TAG         (Quote l:DYN-BOXED-TAG))
(define DYN-INT-TAG           (Quote l:DYN-INT-TAG))
(define DYN-BOOL-TAG          (Quote l:DYN-BOOL-TAG))
(define DYN-UNIT-TAG          (Quote l:DYN-UNIT-TAG))
(define DYN-IMDT-SHIFT        (Quote l:DYN-IMDT-SHIFT))
(define DYN-BOX-SIZE          (Quote l:DYN-BOX-SIZE))
(define DYN-VALUE-INDEX       (Quote l:DYN-VALUE-INDEX))
(define DYN-TYPE-INDEX        (Quote l:DYN-TYPE-INDEX))
(define FALSE-IMDT            (Quote l:FALSE-IMDT))
(define TRUE-IMDT             (Quote l:TRUE-IMDT))
(define UNDEF-IMDT            (Quote l:UNDEF-IMDT))
(define UNIT-IMDT             (Quote l:UNIT-IMDT))
(define GREP-TAG-MASK         (Quote l:GREP-TAG-MASK))
(define UGBOX-TAG             (Quote l:UGBOX-TAG))
(define UGBOX-SIZE            (Quote l:UGBOX-SIZE))
(define UGBOX-VALUE-INDEX     (Quote l:UGBOX-VALUE-INDEX))
(define UGVECT-SIZE-INDEX     (Quote l:UGVECT-SIZE-INDEX))
(define UGVECT-OFFSET         (Quote l:UGVECT-OFFSET))
(define GPROXY-TAG            (Quote l:GPROXY-TAG))
(define GPROXY/TWOSOME-SIZE   (Quote l:GPROXY/TWOSOME-SIZE))
(define GPROXY/COERCION-SIZE  (Quote l:GPROXY/COERCION-SIZE))
(define GPROXY-COERCION-INDEX (Quote l:GPROXY-COERCION-INDEX))
(define GPROXY-FOR-INDEX      (Quote l:GPROXY-FOR-INDEX))
(define GPROXY-FROM-INDEX     (Quote l:GPROXY-FROM-INDEX))
(define GPROXY-TO-INDEX       (Quote l:GPROXY-TO-INDEX))
(define GPROXY-BLAMES-INDEX   (Quote l:GPROXY-BLAMES-INDEX))
(define CLOS-CODE-INDEX       (Quote l:CLOS-CODE-INDEX))
(define CLOS-CSTR-INDEX       (Quote l:CLOS-CSTR-INDEX))
(define CLOS-FVAR-OFFSET      (Quote l:CLOS-FVAR-OFFSET))
(define GREF-TO-INDEX         (Quote l:GREF-TO-INDEX))
(define GVECT-TO-INDEX        (Quote l:GVECT-TO-INDEX))
(define TUPLE-NUM-INDEX       (Quote l:TUPLE-NUM-INDEX))
(define TUPLE-ITEMS-OFFSET    (Quote l:TUPLE-ITEMS-OFFSET))

(define l:PROJECT-COERCION-TAG #b000)
(define PROJECT-COERCION-TAG (Quote l:PROJECT-COERCION-TAG))
(define PROJECT-COERCION-TYPE-INDEX (Quote 0))
(define PROJECT-COERCION-LABEL-INDEX (Quote 1))
(define l:INJECT-COERCION-TAG #b001)
(define INJECT-COERCION-TAG (Quote l:INJECT-COERCION-TAG))
(define INJECT-COERCION-TYPE-INDEX (Quote 0))
(define l:SEQUENCE-COERCION-TAG #b010)
(define SEQUENCE-COERCION-TAG (Quote l:SEQUENCE-COERCION-TAG))
(define SEQUENCE-COERCION-FST-INDEX (Quote 0))
(define SEQUENCE-COERCION-SND-INDEX (Quote 1))
(define COERCION-TAG-MASK (Quote #b111)) ;; the same for primary and secondary tags
(define IDENTITY-COERCION-TAG (Quote #b011))
(define IDENTITY-COERCION-IMDT IDENTITY-COERCION-TAG)
;; (define l:FN-COERCION-TAG #b100)
(define l:MEDIATING-COERCION-TAG #b100)
(define MEDIATING-COERCION-TAG (Quote l:MEDIATING-COERCION-TAG))
(define l:SECOND-FN-COERCION-TAG #b001)
(define SECOND-FN-COERCION-TAG (Quote l:SECOND-FN-COERCION-TAG))
(define l:SECOND-TUPLE-COERCION-TAG #b010)
(define SECOND-TUPLE-COERCION-TAG (Quote l:SECOND-TUPLE-COERCION-TAG))

(define l:FN-TAG-MASK #b111)
(define FN-TAG-MASK (Quote l:FN-TAG-MASK))
(define l:CLOSURE-VALUE-MASK -8) ;; signed long compliment of fn tag mask
(define CLOSURE-VALUE-MASK (Quote l:CLOSURE-VALUE-MASK))
(define l:FN-PROXY-TAG #b001)
(define FN-PROXY-TAG (Quote l:FN-PROXY-TAG))
(define l:FN-PROXY-CRCN-INDEX 1)
(define l:FN-PROXY-CLOS-INDEX 0)
(define FN-PROXY-CRCN-INDEX (Quote l:FN-PROXY-CRCN-INDEX))
(define FN-PROXY-CLOS-INDEX (Quote l:FN-PROXY-CLOS-INDEX))
(define l:HYBRID-PROXY-TAG #b001)
(define HYBRID-PROXY-TAG (Quote l:HYBRID-PROXY-TAG))
(define HYBRID-PROXY-CRCN-INDEX (Quote l:HYBRID-PROXY-CRCN-INDEX))
(define HYBRID-PROXY-CLOS-INDEX (Quote l:HYBRID-PROXY-CLOS-INDEX))
;; (define l:REF-COERCION-TAG #b101)
(define l:SECOND-REF-COERCION-TAG #b000)
(define SECOND-REF-COERCION-TAG (Quote l:SECOND-REF-COERCION-TAG))
(define REF-COERCION-TAG-INDEX (Quote 0))
(define REF-COERCION-READ-INDEX (Quote 1))
(define REF-COERCION-WRITE-INDEX (Quote 2))
(define l:FAILED-COERCION-TAG #b110)
(define FAILED-COERCION-TAG (Quote l:FAILED-COERCION-TAG))
(define FAILED-COERCION-LABEL-INDEX (Quote 0))

(define SECOND-TAG-SHIFT (Quote l:SECOND-TAG-SHIFT))


(: specify-representation (Cast-or-Coerce6-Lang -> Data0-Lang))
(trace-define (specify-representation prgm)
  (match-let ([(Prog (list name next type) (Let-Static* bndt* bnd-crcn* exp)) prgm])
    (let* ([next       : (Boxof Nat) (box next)]
           [bnd-code*  : (Boxof D0-Bnd-Code*) (box '())]
           [exp        : D0-Expr (sr-expr next bnd-code* (hash) empty-index-map exp)]
           [init-type* : D0-Expr* (map (sr-bndt next) bndt*)]
           [type-id*   : Uid*     (map (inst car Uid Any) bndt*)]
           [init-crcn* : D0-Expr* (map (sr-bnd-coercion next) bnd-crcn*)]
           [crcn-id*   : Uid*     (map (inst car Uid Any) bnd-crcn*)]
           [next       : Nat (unbox next)]
           [bnd-code*  : D0-Bnd-Code* (unbox bnd-code*)])
      (Prog (list name next type)
       (GlobDecs (append type-id* crcn-id*)
        (Labels bnd-code*
         (Begin (append init-type* init-crcn*) exp)))))))

;; Env must be maintained as a mapping from uids to how to access those
;; values. This is important because uid references to variable inside a
;; closure must turn into memory loads.

(define-type IndexMap (Uid Uid -> Nat))

(: sr-expr ((Boxof Nat) (Boxof D0-Bnd-Code*) Env IndexMap CoC6-Expr -> D0-Expr))
(define (sr-expr next new-code env cenv exp)
  ;; This is the only piece of code that should touch the unique counter
  (: next-uid! (String -> Uid))
  (define (next-uid! x)
    (let ([n (unbox next)])
      (set-box! next (add1 n))
      (Uid x n)))
  
  (: add-new-code! (D0-Bnd-Code -> Void))
  (define (add-new-code! b)
    (set-box! new-code (cons b (unbox new-code))))

  (: mk-fn-coercion-code-label? (Boxof (Option (Code-Label Uid))))
  (define mk-fn-coercion-code-label? (box #f))

  (: comp-fn-coercion-code-label? (Boxof (Option (Code-Label Uid))))
  (define comp-fn-coercion-code-label? (box #f))
  
  (: coerce-tuple-code-label? (Boxof (Option (Code-Label Uid))))
  (define coerce-tuple-code-label? (box #f))

  (: cast-tuple-code-label? (Boxof (Option (Code-Label Uid))))
  (define cast-tuple-code-label? (box #f))

  (: mk-tuple-coercion-code-label? (Boxof (Option (Code-Label Uid))))
  (define mk-tuple-coercion-code-label? (box #f))

  (: comp-tuple-coercion-code-label? (Boxof (Option (Code-Label Uid))))
  (define comp-tuple-coercion-code-label? (box #f))
  

  (: sr-alloc (String Fixnum (Listof (Pair String D0-Expr)) -> D0-Expr))
  (define sr-alloc (sr-alloc/next next))

  
  ;; The way that boxed immediate work currently bothers me.
  ;; Since we have access to unboxed static ints should we just
  ;; abandon the unboxed dyn integers another a mixture of static
  ;; allocation and and constant lifting could be used to make all
  (: sr-dyn-make ((CoC6-Expr -> D0-Expr) D0-Expr CoC6-Expr -> D0-Expr))
  (define (sr-dyn-make sr-expr e1 e2)
    (cond
      [(Type? e2)
       (match e2
         [(Type (Int))
          (Op '+ (list (Op '%<< (list e1 DYN-IMDT-SHIFT))
                       DYN-INT-TAG))]
         [(Type (Bool))
          (Op '+ (list (Op '%<< (list e1 DYN-IMDT-SHIFT))
                       DYN-BOOL-TAG))]
         [(Type (Unit))
          (Op '+ (list (Op '%<< (list e1 DYN-IMDT-SHIFT))
                       DYN-UNIT-TAG))]
         [else (sr-alloc "dynamic_boxed" #b000
                         `(("value" . ,e1)
                           ("type" . ,(sr-expr e2))))])]
      [else
       (let* ([val    (next-uid! "value")]
              [type   (next-uid! "type")]
              [tag    (next-uid! "tag")]
              [imm    (next-uid!  "imm")]
              [val-var (Var val)]
              [type-var (Var type)]
              [tag-var (Var tag)]
              [imm-var (Var imm)])
         (Let `((,val . ,e1)
                (,type . ,(sr-expr e2)))
              (Let `((,tag . ,(Op 'binary-and `(,type-var ,TYPE-TAG-MASK))))
                   (If (Op '= `(,tag-var ,TYPE-ATOMIC-TAG))
                       (Let `((,imm . ,(Op '%<< (list val-var DYN-IMDT-SHIFT))))
                            (If (Op '= `(,type-var ,TYPE-INT-RT-VALUE))
                                (Op 'binary-or `(,imm-var ,DYN-INT-TAG))
                                (If (Op '= `(,type-var ,TYPE-BOOL-RT-VALUE))
                                    (Op 'binary-or `(,imm-var ,DYN-BOOL-TAG))
                                    (Op 'binary-or `(,imm-var ,DYN-UNIT-TAG)))))
                       (sr-alloc "dynamic_boxed" #b000
                                 `(("" . ,val-var)
                                   ("" . ,type-var)))))))]))

  (: get-mk-fn-crcn! (Uid -> (Code-Label Uid)))
  (define (get-mk-fn-crcn! mk-crcn)
    (: make-code! (Uid -> (Code-Label Uid)))
    (define (make-code! mk-crcn)
      (define mk-fn-u (next-uid! "make-fn-coercion"))
      (define t1-u    (next-uid! "fn-type1"))
      (define t2-u    (next-uid! "fn-type2"))
      (define l-u     (next-uid! "label"))
      (define i-u     (next-uid! "index"))
      (define a-u     (next-uid! "fn-type-arity"))
      (define t1r-u   (next-uid! "fn-type1-return"))
      (define t2r-u   (next-uid! "fn-type2-return"))
      (define t1a-u   (next-uid! "fn-type1-argument"))
      (define t2a-u   (next-uid! "fn-type2-argument"))
      (define c1-u    (next-uid! "resulting_coercion"))
      (define c2-u    (next-uid! "resulting_coercion"))
      (define cr-u    (next-uid! "return-coercion"))
      (define ca-u    (next-uid! "argument-coercion"))
      (define st-u    (next-uid! "second-tagged"))
      (define t1      (Var t1-u))
      (define t2      (Var t2-u))
      (define l       (Var l-u))
      (define c1      (Var c1-u))
      (define c2      (Var c2-u))
      (define i       (Var i-u))
      (define a       (Var a-u))
      (define st      (Var st-u))
      (define mk-fn   (Code-Label mk-fn-u))
      (define mk-c    (Code-Label mk-crcn))
      ;; This code is carfully crafted so that the allocation occurs after
      ;; all of the coercion have been made this ensures that there isn't the
      ;; possibility of collecting while there is unitialized data in the heap.
      (define mk-fn-c : D0-Code
        (Code `(,t1-u ,t2-u ,l-u ,i-u ,a-u)
              (If (Op '= `(,i ,a))
                  (Let `((,t1r-u . ,(sr-tagged-array-ref t1 TYPE-FN-TAG FN-RETURN-INDEX))
                         (,t2r-u . ,(sr-tagged-array-ref t2 TYPE-FN-TAG FN-RETURN-INDEX)))
                       (Let `((,cr-u . ,(App-Code mk-c `(,(Var t1r-u) ,(Var t2r-u) ,l))))
                            (Let `((,c1-u . ,(Op 'Alloc (list (sr-plus a (Quote 2)))))
                                   (,st-u . ,(Op '+ (list (Op '%<< (list a SECOND-TAG-SHIFT))
                                                              SECOND-FN-COERCION-TAG))))
                                 (Begin
                                   `(,(sr-array-set! c1 FN-ARITY-INDEX st)
                                     ,(sr-array-set! c1 FN-RETURN-INDEX (Var cr-u)))
                                   (sr-tag-value c1 MEDIATING-COERCION-TAG)))))
                  (Let `((,t1a-u . ,(sr-tagged-array-ref t1 TYPE-FN-TAG (sr-plus FN-FMLS-OFFSET i)))
                         (,t2a-u . ,(sr-tagged-array-ref t2 TYPE-FN-TAG (sr-plus FN-FMLS-OFFSET i))))
                       (Let `((,ca-u . ,(App-Code mk-c `(,(Var t2a-u) ,(Var t1a-u) ,l))))
                            (Let `((,c2-u . ,(App-Code mk-fn `(,t1 ,t2 ,l ,(sr-plus (Quote 1) i) ,a))))
                                 (Begin
                                   `(,(sr-tagged-array-set! c2 MEDIATING-COERCION-TAG (sr-plus FN-FMLS-OFFSET i) (Var ca-u)))
                                   c2)))))))
      (add-new-code! (cons mk-fn-u mk-fn-c))
      (set-box! mk-fn-coercion-code-label? mk-fn)
      mk-fn)
    (let ([cl? (unbox mk-fn-coercion-code-label?)])
      (or cl? (make-code! mk-crcn))))

  (: get-comp-fn-crcn! (Uid -> (Code-Label Uid)))
  (define (get-comp-fn-crcn! comp-crcn)
    (: make-code! (Uid -> (Code-Label Uid)))
    (define (make-code! mk-crcn)
      (define comp-fn-u (next-uid! "compose-fn-coercion"))
      (define c1-u      (next-uid! "fn-coercion1"))
      (define c2-u      (next-uid! "fn-coercion2"))
      (define c3-u      (next-uid! "result-coercion"))
      (define c4-u      (next-uid! "result-coercion"))
      (define i-u       (next-uid! "index"))
      (define a-u       (next-uid! "fn-coercion-arity"))
      (define c1r-u     (next-uid! "fn-coercion1-return"))
      (define c2r-u     (next-uid! "fn-coercion2-return"))
      (define c1a-u     (next-uid! "fn-coercion1-argument"))
      (define c2a-u     (next-uid! "fn-coercion2-argument"))
      (define cr-u      (next-uid! "return-coercion"))
      (define ca-u      (next-uid! "argument-coercion"))
      (define id?1-u    (next-uid! "is_identity"))
      (define id?2-u    (next-uid! "is_still_identity"))
      (define st-u      (next-uid! "secondary-tagged"))
      (define c1        (Var c1-u))
      (define c2        (Var c2-u))
      (define c3        (Var c3-u))
      (define c4        (Var c4-u))
      (define cr        (Var cr-u))
      (define ca        (Var ca-u))
      (define i         (Var i-u))
      (define a         (Var a-u))
      (define id?1      (Var id?1-u))
      (define id?2      (Var id?2-u))
      (define st        (Var st-u))
      (define comp-fn   (Code-Label comp-fn-u))
      (define comp-c    (Code-Label comp-crcn))
      ;; This code is carfully crafted so that the allocation occurs after
      ;; all of the coercion have been made this ensures that there isn't the
      ;; possibility of collecting while there is unitialized data in the heap.
      (define comp-fn-c : D0-Code
        (Code `(,c1-u ,c2-u ,i-u ,a-u ,id?1-u)
              (If (Op '= `(,i ,a))
                  (Let `((,c1r-u . ,(sr-tagged-array-ref c1 MEDIATING-COERCION-TAG FN-RETURN-INDEX))
                         (,c2r-u . ,(sr-tagged-array-ref c2 MEDIATING-COERCION-TAG FN-RETURN-INDEX)))
                       (Let `((,cr-u . ,(App-Code comp-c `(,(Var c1r-u) ,(Var c2r-u)))))
                            (If (If id?1
                                    (sr-check-tag=? cr COERCION-TAG-MASK IDENTITY-COERCION-TAG)
                                    FALSE-IMDT)
                                IDENTITY-COERCION-IMDT
                                (Let `((,c3-u . ,(Op 'Alloc (list (sr-plus a (Quote 2)))))
                                       (,st-u . ,(Op '+ (list (Op '%<< (list a SECOND-TAG-SHIFT))
                                                              SECOND-FN-COERCION-TAG))))
                                     (Begin
                                       ;; TODO: come up with a test case that fails if the arity is not set
                                       `(,(sr-array-set! c3 FN-ARITY-INDEX st)
                                         ,(sr-array-set! c3 FN-RETURN-INDEX cr))
                                       (sr-tag-value c3 MEDIATING-COERCION-TAG))))))
                  (Let `((,c1a-u . ,(sr-tagged-array-ref c1 MEDIATING-COERCION-TAG (sr-plus FN-FMLS-OFFSET i)))
                         (,c2a-u . ,(sr-tagged-array-ref c2 MEDIATING-COERCION-TAG (sr-plus FN-FMLS-OFFSET i))))
                       (Let `((,ca-u . ,(App-Code comp-c `(,(Var c2a-u) ,(Var c1a-u)))))
                            (Let `((,id?2-u . ,(If id?1
                                                   (sr-check-tag=? ca COERCION-TAG-MASK IDENTITY-COERCION-TAG)
                                                   FALSE-IMDT)))
                                 (Let `((,c4-u . ,(App-Code comp-fn `(,c1 ,c2 ,(sr-plus (Quote 1) i) ,a ,id?2))))
                                      (If (sr-check-tag=? c4 COERCION-TAG-MASK IDENTITY-COERCION-TAG)
                                          IDENTITY-COERCION-IMDT
                                          (Begin
                                            `(,(sr-tagged-array-set! c4 MEDIATING-COERCION-TAG (sr-plus FN-FMLS-OFFSET i) ca))
                                            c4)))))))))
      (add-new-code! (cons comp-fn-u comp-fn-c))
      (set-box! comp-fn-coercion-code-label? comp-fn)
      comp-fn)
    (let ([cl? (unbox comp-fn-coercion-code-label?)])
      (or cl? (make-code! comp-crcn))))

  (: get-coerce-tuple! (Uid -> (Code-Label Uid)))
  (define (get-coerce-tuple! cast)
    (: make-code! (Uid -> (Code-Label Uid)))
    (define (make-code! cast)
      (define coerce-tuple-u (next-uid! "coerce-tuple"))
      (define v-u            (next-uid! "tuple-val"))
      (define c-u            (next-uid! "tuple-coercion"))
      (define i-u            (next-uid! "index"))
      (define a-u            (next-uid! "tuple-type-num"))
      (define va-u           (next-uid! "tuple-val-item"))
      (define ca-u           (next-uid! "tuple-coercion-item"))
      (define v1-u           (next-uid! "resulting_tuple"))
      (define v2-u           (next-uid! "resulting_tuple"))
      (define cva-u          (next-uid! "item"))
      (define v              (Var v-u))
      (define c              (Var c-u))
      (define v1             (Var v1-u))
      (define v2             (Var v2-u))
      (define i              (Var i-u))
      (define a              (Var a-u))
      (define coerce-tuple   (Code-Label coerce-tuple-u))
      (define mk-c           (Code-Label cast))
      (define coerce-tuple-c : D0-Code
        (Code `(,v-u ,c-u ,i-u ,a-u)
              (If (Op '= `(,i ,a))
                  (Let `((,v1-u . ,(Op 'Alloc (list a))))
                       v1)
                  (Let `((,va-u . ,(Op 'Array-ref (list v i)))
                         (,ca-u . ,(sr-tagged-array-ref c MEDIATING-COERCION-TAG (sr-plus TUPLE-ITEMS-OFFSET i))))
                       (Let `((,cva-u . ,(App-Code mk-c `(,(Var va-u) ,(Var ca-u)))))
                            (Let `((,v2-u . ,(App-Code coerce-tuple `(,v ,c ,(sr-plus (Quote 1) i) ,a))))
                                 (Begin
                                   `(,(Op 'Array-set! (list v2 i (Var cva-u))))
                                   v2)))))))
      (add-new-code! (cons coerce-tuple-u coerce-tuple-c))
      (set-box! coerce-tuple-code-label? coerce-tuple)
      coerce-tuple)
    (let ([cl? (unbox coerce-tuple-code-label?)])
      (or cl? (make-code! cast))))

  (: get-cast-tuple! (Uid -> (Code-Label Uid)))
  (define (get-cast-tuple! cast)
    (: make-code! (Uid -> (Code-Label Uid)))
    (define (make-code! cast)
      (define cast-u     (next-uid! "cast"))
      (define v-u        (next-uid! "val"))
      (define t1-u       (next-uid! "tuple-type1"))
      (define t2-u       (next-uid! "tuple-type2"))
      (define l-u        (next-uid! "label"))
      (define i-u        (next-uid! "index"))
      (define a-u        (next-uid! "tuple-type-num"))
      (define t1a-u      (next-uid! "tuple-type1-item"))
      (define t2a-u      (next-uid! "tuple-type2-item"))
      (define c1-u       (next-uid! "resulting_val"))
      (define c2-u       (next-uid! "resulting_val"))
      (define ca-u       (next-uid! "item-type"))
      (define va-u       (next-uid! "item-val"))
      (define v          (Var v-u))
      (define t1         (Var t1-u))
      (define t2         (Var t2-u))
      (define l          (Var l-u))
      (define c1         (Var c1-u))
      (define c2         (Var c2-u))
      (define va         (Var va-u))
      (define i          (Var i-u))
      (define a          (Var a-u))
      (define cast-tuple (Code-Label cast-u))
      (define mk-c       (Code-Label cast))
      (define cast-tuple-c : D0-Code
        (Code `(,v-u ,t1-u ,t2-u ,l-u ,i-u ,a-u)
              (If (Op '= `(,i ,a))
                  (Let `((,c1-u . ,(Op 'Alloc (list a))))
                       c1)
                  (Let `((,va-u . ,(Op 'Array-ref (list v i)))
                         (,t1a-u . ,(sr-tagged-array-ref t1 TYPE-TUPLE-TAG (sr-plus TUPLE-ITEMS-OFFSET i)))
                         (,t2a-u . ,(sr-tagged-array-ref t2 TYPE-TUPLE-TAG (sr-plus TUPLE-ITEMS-OFFSET i))))
                       (Let `((,ca-u . ,(App-Code mk-c `(,va ,(Var t1a-u) ,(Var t2a-u) ,l))))
                            (Let `((,c2-u . ,(App-Code cast-tuple `(,v ,t1 ,t2 ,l ,(sr-plus (Quote 1) i) ,a))))
                                 (Begin
                                   `(,(Op 'Array-set! (list c2 i (Var ca-u))))
                                   c2)))))))
      (add-new-code! (cons cast-u cast-tuple-c))
      (set-box! cast-tuple-code-label? cast-tuple)
      cast-tuple)
    (let ([cl? (unbox cast-tuple-code-label?)])
      (or cl? (make-code! cast))))

  (: get-mk-tuple-crcn! (Uid -> (Code-Label Uid)))
  (define (get-mk-tuple-crcn! mk-crcn)
    (: make-code! (Uid -> (Code-Label Uid)))
    (define (make-code! mk-crcn)
      (define mk-tuple-u (next-uid! "make-tuple-coercion"))
      (define t1-u       (next-uid! "tuple-type1"))
      (define t2-u       (next-uid! "tuple-type2"))
      (define l-u        (next-uid! "label"))
      (define i-u        (next-uid! "index"))
      (define a-u        (next-uid! "tuple-type-num"))
      (define t1a-u      (next-uid! "tuple-type1-item"))
      (define t2a-u      (next-uid! "tuple-type2-item"))
      (define c1-u       (next-uid! "resulting_coercion"))
      (define c2-u       (next-uid! "resulting_coercion"))
      (define ca-u       (next-uid! "item-coercion"))
      (define st-u       (next-uid! "second-tagged"))
      (define t1         (Var t1-u))
      (define t2         (Var t2-u))
      (define l          (Var l-u))
      (define c1         (Var c1-u))
      (define c2         (Var c2-u))
      (define i          (Var i-u))
      (define a          (Var a-u))
      (define st         (Var st-u))
      (define mk-tuple   (Code-Label mk-tuple-u))
      (define mk-c       (Code-Label mk-crcn))
      (define mk-tuple-c : D0-Code
        (Code `(,t1-u ,t2-u ,l-u ,i-u ,a-u)
              (If (Op '= `(,i ,a))
                  (Let `((,c1-u . ,(Op 'Alloc (list (sr-plus a (Quote 1)))))
                         (,st-u . ,(Op '+ (list (Op '%<< (list a SECOND-TAG-SHIFT))
                                                SECOND-TUPLE-COERCION-TAG))))
                       (Begin
                         `(,(sr-array-set! c1 TUPLE-NUM-INDEX st))
                         (sr-tag-value c1 MEDIATING-COERCION-TAG)))
                  (Let `((,t1a-u . ,(sr-tagged-array-ref t1 TYPE-TUPLE-TAG (sr-plus TUPLE-ITEMS-OFFSET i)))
                         (,t2a-u . ,(sr-tagged-array-ref t2 TYPE-TUPLE-TAG (sr-plus TUPLE-ITEMS-OFFSET i))))
                       (Let `((,ca-u . ,(App-Code mk-c `(,(Var t1a-u) ,(Var t2a-u) ,l))))
                            (Let `((,c2-u . ,(App-Code mk-tuple `(,t1 ,t2 ,l ,(sr-plus (Quote 1) i) ,a))))
                                 (Begin
                                   `(,(sr-tagged-array-set! c2 MEDIATING-COERCION-TAG (sr-plus TUPLE-ITEMS-OFFSET i) (Var ca-u)))
                                   c2)))))))
      (add-new-code! (cons mk-tuple-u mk-tuple-c))
      (set-box! mk-tuple-coercion-code-label? mk-tuple)
      mk-tuple)
    (let ([cl? (unbox mk-tuple-coercion-code-label?)])
      (or cl? (make-code! mk-crcn))))

  (: get-comp-tuple-crcn! (Uid -> (Code-Label Uid)))
  (define (get-comp-tuple-crcn! comp-crcn)
    (: make-code! (Uid -> (Code-Label Uid)))
    (define (make-code! mk-crcn)
      (define comp-tuple-u (next-uid! "compose-tuple-coercion"))
      (define c1-u      (next-uid! "tuple-coercion1"))
      (define c2-u      (next-uid! "tuple-coercion2"))
      (define c3-u      (next-uid! "result-coercion"))
      (define c4-u      (next-uid! "result-coercion"))
      (define i-u       (next-uid! "index"))
      (define a-u       (next-uid! "tuple-coercion-num"))
      (define c1a-u     (next-uid! "tuple-coercion1-argument"))
      (define c2a-u     (next-uid! "tuple-coercion2-argument"))
      (define cr-u      (next-uid! "return-coercion"))
      (define ca-u      (next-uid! "argument-coercion"))
      (define id?1-u    (next-uid! "is_identity"))
      (define id?2-u    (next-uid! "is_still_identity"))
      (define st-u      (next-uid! "second-tagged"))
      (define c1        (Var c1-u))
      (define c2        (Var c2-u))
      (define c3        (Var c3-u))
      (define c4        (Var c4-u))
      (define cr        (Var cr-u))
      (define ca        (Var ca-u))
      (define i         (Var i-u))
      (define a         (Var a-u))
      (define id?1      (Var id?1-u))
      (define id?2      (Var id?2-u))
      (define st        (Var st-u))
      (define comp-tuple   (Code-Label comp-tuple-u))
      (define comp-c    (Code-Label comp-crcn))
      (define comp-tuple-c : D0-Code
        (Code `(,c1-u ,c2-u ,i-u ,a-u ,id?1-u)
              (If (Op '= `(,i ,a))
                  (Let `((,c3-u . ,(Op 'Alloc (list (sr-plus a (Quote 1)))))
                         (,st-u . ,(Op '+ (list (Op '%<< (list a SECOND-TAG-SHIFT))
                                                SECOND-TUPLE-COERCION-TAG))))
                       (Begin
                         `(,(sr-array-set! c3 TUPLE-NUM-INDEX st))
                         (sr-tag-value c3 MEDIATING-COERCION-TAG)))
                  (Let `((,c1a-u . ,(sr-tagged-array-ref c1 MEDIATING-COERCION-TAG (sr-plus TUPLE-ITEMS-OFFSET i)))
                         (,c2a-u . ,(sr-tagged-array-ref c2 MEDIATING-COERCION-TAG (sr-plus TUPLE-ITEMS-OFFSET i))))
                       (Let `((,ca-u . ,(App-Code comp-c `(,(Var c1a-u) ,(Var c2a-u)))))
                            (Let `((,id?2-u . ,(If id?1
                                                   (sr-check-tag=? ca COERCION-TAG-MASK IDENTITY-COERCION-TAG)
                                                   FALSE-IMDT)))
                                 (Let `((,c4-u . ,(App-Code comp-tuple `(,c1 ,c2 ,(sr-plus (Quote 1) i) ,a ,id?2))))
                                      (If (sr-check-tag=? c4 COERCION-TAG-MASK IDENTITY-COERCION-TAG)
                                          IDENTITY-COERCION-IMDT
                                          (Begin
                                            `(,(sr-tagged-array-set! c4 MEDIATING-COERCION-TAG (sr-plus TUPLE-ITEMS-OFFSET i) ca))
                                            c4)))))))))
      (add-new-code! (cons comp-tuple-u comp-tuple-c))
      (set-box! comp-tuple-coercion-code-label? comp-tuple)
      comp-tuple)
    (let ([cl? (unbox comp-tuple-coercion-code-label?)])
      (or cl? (make-code! comp-crcn))))


  (: recur-curry-env (Env IndexMap -> (CoC6-Expr -> D0-Expr)))
  (define ((recur-curry-env env cenv) exp)
    (recur/env exp env cenv))

  

  
  (: recur/env (CoC6-Expr Env IndexMap -> D0-Expr))
  (define (recur/env exp env cenv)
    (: recur* (CoC6-Expr* -> D0-Expr*))
    (define (recur* e*) (map recur e*))
    (: recur (CoC6-Expr -> D0-Expr))
    (define (recur e)
      (error 'foo))
    (recur exp))


  
  (recur/env exp env cenv))


;; Allocate without forgetting to lift evaluating subterms first
;; this prevents evaluating terms which may cause more allocation
;; will initializing the values of an allocation
;; it essentially produces expression of the form:
;; (let ((t* e*) ...) (let ((tmp (alloc ...))) (begin (set tmp i t*) ... (binary-or tmp tag))))
;; though it does eliminate any form that it can based on it's input
(: sr-alloc/next ((Boxof Nat) ->
                  (String Fixnum (Listof (Pair String D0-Expr)) ->
                          D0-Expr)))
(define ((sr-alloc/next next) name tag slots)
  (: next-uid! (String -> Uid))
  (define (next-uid! x)
    (let ([n (unbox next)])
      (set-box! next (add1 n))
      (Uid x n)))
  ;; As long as this is used to initialize all the data I have
  ;; a faily stong guarentee that no other allocation could possibly occur.
  (: sr-alloc-init ((Var Uid) -> (Index (Var Uid) -> D0-Expr)))
  (define ((sr-alloc-init mem) offset value)
    (Op 'Array-set! (list mem (Quote offset) value)))
  ;; Take a list of variables and expressions paired with their names
  ;; make variables that are bound to the expressions and the bindings
  (: get-bnd/var ((Listof (Pair String D0-Expr)) -> (Values D0-Bnd* (Listof (Var Uid)))))
  (define (get-bnd/var b*)
    (if (null? b*)
        (values '() '())
        (let*-values ([(a  d)  (values (car b*) (cdr b*))]
                      [(b* v*) (get-bnd/var d)]
                      [(n  e)  (values (car a) (cdr a))])
          (if (Var? e)
              (values b* (cons e v*))
              (let* ([u (next-uid! n)])
                (values `((,u . ,e) . ,b*) `(,(Var u) . ,v*)))))))
  (define result
    (let ([size (length slots)])
      (if (= size 0)
          (error 'specify-representation "Empty objects can not be allocated")
          (let*-values ([(bnd* var*) (get-bnd/var slots)]
                        [(ind*)      (range 0 size)]
                        [(alloc-id)  (next-uid! name)]
                        [(alloc-var) (Var alloc-id)]
                        [(alloc-bnd) `((,alloc-id . ,(Op 'Alloc `(,(Quote size)))))]
                        [(set*)       (map (sr-alloc-init alloc-var) ind* var*)]
                        [(tag-return) (if (= tag 0)
                                          alloc-var
                                          (Op 'binary-or (list alloc-var (Quote tag))))]
                        [(alloc-set-return) (Let alloc-bnd (Begin set* tag-return))])
            (if (null? bnd*)
                alloc-set-return
                (Let bnd* alloc-set-return))))))
  (logging sr-bnd (Vomit) "~a ~a ~a ==> ~a" name tag slots result)
  result)

(: sr-prim-type (Prim-Type -> D0-Expr))
(define (sr-prim-type t)
  (match t
    ;; TODO Var is a little wastful perhaps this should be
    ;; A Label node of some sort?
    [(Int)  TYPE-INT-RT-VALUE]
    [(Bool) TYPE-BOOL-RT-VALUE]
    [(Dyn)  TYPE-DYN-RT-VALUE]
    [(Unit) TYPE-UNIT-RT-VALUE]
    [(Static-Id u) (Var u)]
    [other (error 'specify-representation/primitive-type "unmatched ~a" other)]))

(: sr-bndt ((Boxof Nat) -> (CoC6-Bnd-Type -> D0-Expr)))
(define ((sr-bndt next) bnd)
  (define sr-alloc (sr-alloc/next next))
  (: sr-type (Compact-Type -> D0-Expr))
  (define (sr-type t)
    (match t
      [(GRef t)
       (sr-alloc "GRefT" l:TYPE-GREF-TAG
                 `(("type" . ,(sr-prim-type t))))]
      [(GVect t)
       (sr-alloc "GVect_Type" l:TYPE-GVECT-TAG
                 `(("type" . ,(sr-prim-type t))))]      
      [(Fn a f* r)
       (sr-alloc "Fun_Type" l:TYPE-FN-TAG
                 `(("arity" . ,(Quote a))
                   ("return" . ,(sr-prim-type r)) .
                   ,(map (lambda ([t : Prim-Type])
                           (cons "argument" (sr-prim-type t)))
                         f*)))]
      [(STuple n a*)
       (sr-alloc "Tuple_Type" l:TYPE-TUPLE-TAG
                 `(("num" . ,(Quote n))
                   .
                   ,(map (lambda ([t : Prim-Type])
                           (cons "argument" (sr-prim-type t)))
                         a*)))]
      [other (error 'specify-representation/type "unmatched ~a" other)]))
  (match-let ([(cons u t) bnd])
    (Assign u (sr-type t))))

(: sr-immediate-coercion (Immediate-Coercion -> D0-Expr))
(define (sr-immediate-coercion c)
  (match c
    [(Identity) IDENTITY-COERCION-IMDT]
    [(Static-Id id) (Var id)]
    [else (error 'sr-immediate-coercion "unhandled case in match")]))

(: sr-bnd-coercion ((Boxof Nat) -> (CoC6-Bnd-Crcn -> D0-Expr)))
(define (sr-bnd-coercion next)
  (: next-uid! (String -> Uid))
  (define (next-uid! x)
    (let ([n (unbox next)])
      (set-box! next (add1 n))
      (Uid x n)))
  
  (define sr-alloc (sr-alloc/next next))
  (: sr-coercion (Compact-Coercion -> D0-Expr))
  (define (sr-coercion t)
    (match t
      [(Identity) IDENTITY-COERCION-IMDT]
      [(Project t l)
       ;; TODO Make it possible to turn off type hoisting
       (define t^ (sr-prim-type t))
       (sr-alloc "project_coercion" l:PROJECT-COERCION-TAG
                 `(("type" . ,t^) ("label" . ,(Quote l))))]
      [(Inject (app sr-prim-type t))
       (sr-alloc "inject-coercion" l:INJECT-COERCION-TAG
                 `(("type" . ,t)))]
      [(Sequence (app sr-immediate-coercion f)
                 (app sr-immediate-coercion s))
       (sr-alloc "sequence_coecion" l:SEQUENCE-COERCION-TAG
                 `(("first" . ,f) (,"second" . ,s)))]
      [(Fn l a* (app sr-immediate-coercion r))
       (define len : Index (length a*))
       (unless (= l len)
         (error 'sr-coercion "length mismatch"))
       (define st-u      (next-uid! "second-tagged"))
       (Let `((,st-u . ,(Op '+ (list (Op '%<< (list (Quote l) SECOND-TAG-SHIFT))
                                     SECOND-FN-COERCION-TAG))))
            (sr-alloc "fn_coercion" l:MEDIATING-COERCION-TAG
                 `(("arity"  . ,(Var st-u))
                   ("return" . ,r) .
                   ,(map (lambda ([a : Immediate-Coercion])
                           (cons "argument" (sr-immediate-coercion a)))
                         a*))))]
      [(Ref (app sr-immediate-coercion r) (app sr-immediate-coercion w))
       (define st-u    (next-uid! "second-tagged"))
       (Let `((,st-u . ,(Op '+ (list (Op '%<< (list (Quote 0) SECOND-TAG-SHIFT))
                                     SECOND-REF-COERCION-TAG))))
            (sr-alloc "ref-coercion" l:MEDIATING-COERCION-TAG
                      `(("tag" . ,(Var st-u))
                        ("read-coercion" . ,r)
                        ("write-coercion" . ,w))))]
      [(CTuple l a*)
       (define len : Index (length a*))
       (unless (= l len)
         (error 'sr-coercion "length mismatch"))
       (define st-u      (next-uid! "second-tagged"))
       (Let `((,st-u . ,(Op '+ (list (Op '%<< (list (Quote (length a*)) SECOND-TAG-SHIFT))
                                     SECOND-TUPLE-COERCION-TAG))))
            (sr-alloc "tuple_coercion" l:MEDIATING-COERCION-TAG
                      `(("num"  . ,(Var st-u))
                        .
                        ,(map (lambda ([a : Immediate-Coercion])
                                (cons "item" (sr-immediate-coercion a)))
                              a*))))]
      [(Failed l)
       (sr-alloc "failed-coercion" l:FAILED-COERCION-TAG
                 `(("label" . ,(Quote l))))]
        [other (error 'specify-representation/type "unmatched ~a" other)]))
  (lambda ([b : CoC6-Bnd-Crcn])
    (match-let ([(cons u c) b])
      (Assign u (sr-coercion c)))))

(: untag-deref-gproxy (-> D0-Expr (-> D0-Expr D0-Expr)))
(define ((untag-deref-gproxy index) proxy)
  (Op 'Array-ref
      (list (Op 'binary-xor (list proxy GPROXY-TAG))
            index)))

(: alloc-tag-set-gproxy/twosome
   ((String -> Uid) D0-Expr D0-Expr D0-Expr D0-Expr -> D0-Expr))
(define (alloc-tag-set-gproxy/twosome uid! ref-e src-e tar-e lbl-e)
  ;; TODO Consider using sr-alloc here
  (define proxy (uid! "guarded_proxy"))
  (define ref   (uid! "guarded_ref"))
  (define src   (uid! "source_t"))
  (define tar   (uid! "target_t"))
  (define lbl   (uid! "blame"))
  (define var   (Var proxy))
  (Let `((,ref . ,ref-e) (,src . ,src-e)
         (,tar . ,tar-e) (,lbl . ,lbl-e))
       (Let `((,proxy . ,(Op 'Alloc (list GPROXY/TWOSOME-SIZE))))
            (Begin
              (list
               (Op 'Array-set! (list var GPROXY-FOR-INDEX    (Var ref)))
               (Op 'Array-set! (list var GPROXY-FROM-INDEX   (Var src)))
               (Op 'Array-set! (list var GPROXY-TO-INDEX     (Var tar)))
               (Op 'Array-set! (list var GPROXY-BLAMES-INDEX (Var lbl))))
              (Op 'binary-or (list var GPROXY-TAG))))))

(: alloc-tag-set-gproxy/coercion
   ((String -> Uid) D0-Expr D0-Expr -> D0-Expr))
(define (alloc-tag-set-gproxy/coercion uid! ref-e crcn-e)
  (define proxy (uid! "guarded_proxy"))
  (define ref   (uid! "guarded_ref"))
  (define crcn  (uid! "coercion"))
  (define var   (Var proxy))
  (Let `((,ref . ,ref-e) (,crcn . ,crcn-e))
       (Let `((,proxy . ,(Op 'Alloc (list GPROXY/COERCION-SIZE))))
            (Begin
              (list
               (Op 'Array-set! (list var GPROXY-FOR-INDEX      (Var ref)))
               (Op 'Array-set! (list var GPROXY-COERCION-INDEX (Var crcn))))
              (Op 'binary-or (list var GPROXY-TAG))))))


;; fold map through bindings
(: sr-bnd* ((CoC6-Expr -> D0-Expr) -> (CoC6-Bnd-Data* -> D0-Bnd*)))
(define ((sr-bnd* sr-expr) b*)
  (: sr-bnd (CoC6-Bnd-Data -> D0-Bnd))
  (define (sr-bnd b)
    (cons (car b) (sr-expr (cdr b))))
  (map sr-bnd b*))

(: sr-bnd-code* ((CoC6-Expr Env IndexMap -> D0-Expr)
                 -> (CoC6-Bnd-Code* -> D0-Bnd-Code*)))
(define ((sr-bnd-code* sr-expr/env) b*)
  (: sr-bnd (CoC6-Bnd-Code -> D0-Bnd-Code))
  (define (sr-bnd b)
    (match-let ([(cons u (Code u* e)) b])
      (let ([env (extend* (hash) u* (map var u*))])
        (cons u (Code u* (sr-expr/env e env empty-index-map))))))
  (map sr-bnd b*))




(: sr-observe ((String -> Uid) D0-Expr Schml-Type -> D0-Expr))
(define (sr-observe uid! e t)
  (: generate-print (Uid Schml-Type -> D0-Expr))
  (define (generate-print id ty)
    (cond
      [(Int? t) (Op 'Printf (list (Quote "Int : %d\n") (Var id)))]
      [(Unit? t) (Op 'Printf (list (Quote "Unit : ()\n")))]
      [(Bool? t) (If (Var id)
                     (Op 'Print (list (Quote "Bool : #t\n")))
                     (Op 'Print (list (Quote "Bool : #f\n"))))]
      [(Fn? t) (Op 'Print (list (Quote "Function : ?\n")))]
      [(GRef? t) (Op 'Print (list (Quote "GReference : ?\n")))]
      [(GVect? t) (Op 'Print (list (Quote "GVector : ?\n")))]
      [(STuple? t) (Op 'Print (list (Quote "Tuple : ?\n")))]
      [(Dyn? t) (Op 'Print (list (Quote "Dynamic : ?\n")))]
      [else (error 'sr-observe "printing other things")]))
  (let* ([res (uid! "result")])
    (Let (list (cons res e))
         (Begin (list (generate-print res t)) (Success)))))

#;(TODO GET RID OF TAGS IN THE COMPILER)
(: sr-tag (Tag-Symbol -> (Quote Integer)))
(define (sr-tag t)
  (case t
    [(Int)    DYN-INT-TAG]
    [(Bool)   DYN-BOOL-TAG]
    [(Unit)   DYN-UNIT-TAG]
    [(Atomic) TYPE-ATOMIC-TAG]
    [(Fn)     TYPE-FN-TAG]
    [(GRef)   TYPE-GREF-TAG]
    [(GVect)  TYPE-GVECT-TAG]
    [(Boxed)  DYN-BOXED-TAG]
    [(STuple) TYPE-TUPLE-TAG]))



(: sr-bndp* ((CoC6-Expr Env IndexMap -> D0-Expr)
             -> (CoC6-Bnd-Procedure* -> D0-Bnd-Code*)))
(define ((sr-bndp* sr-expr) b*)
  (: sr-bndp (CoC6-Bnd-Procedure -> D0-Bnd-Code))
  (define (sr-bndp bnd)
    (match-let ([(cons u (Procedure cp param* code ctr? fvar* exp)) bnd])
      (let* ([offset (if ctr? 2 1)]
             [closv  (Var cp)]
             [env (for/hash : Env ([fvar fvar*]
                                   [i (in-naturals offset)])
                    (values fvar (Op 'Array-ref (list closv (Quote i)))))]
             [env (extend* env param* (map var param*))]
             [cenv (index-closure offset cp fvar*)])
        (cons u (Code (cons cp param*) (sr-expr exp env cenv))))))
  (map sr-bndp b*))

(: index-closure (Nat Uid Uid* -> IndexMap))
(define (index-closure offset clos fvar*)
  (define ((fvar-err f))
    (error 'specifiy-representation "failed to index free var ~a from clos ~a"
           f clos))
  (define (clos-err c f)
    (error 'specify-representation
           "unbound closure index ~a from closure ~a inside of clos ~a"
           f c clos))
  (let ([map (for/hash : (HashTable Uid Nat)
                       ([fvar : Uid fvar*]
                        [i : Nat (in-naturals offset)])
               (values fvar i))])
    (lambda ([c : Uid] [f : Uid]) : Nat
            (if (uid=? c clos)
                (hash-ref map f (fvar-err f))
                (clos-err c f)))))


(: sr-bndc* ((CoC6-Expr -> D0-Expr) CoC6-Bnd-Closure* -> (Values D0-Bnd* D0-Expr*)))
(define (sr-bndc* sr-expr b*)
  (: sr-bndc (CoC6-Bnd-Closure -> (Pair D0-Bnd D0-Expr*)))
  (define (sr-bndc bnd)
    (match-let ([(cons uid (Closure-Data lbl ctr? free*)) bnd])
      (let* ([lbl   (sr-expr lbl)]
             [free* (map sr-expr free*)]
             [data  (cons lbl (if ctr? (cons (sr-expr ctr?) free*) free*))]
             [size  (length data)]
             [clos  (Var uid)]
             [bnd   (cons uid (Op 'Alloc `(,(Quote size))))]
             [set*  (for/list : (Listof D0-Expr)
                              ([d : D0-Expr data]
                               [i : Integer (in-naturals)])
                      (Op 'Array-set! (list clos (Quote i) d)))])
        (cons bnd set*))))
  (let* ([b.e*  (map sr-bndc b*)]
         [b*    (map (inst car D0-Bnd Any) b.e*)]
         [e*    (append-map (inst cdr Any D0-Expr*) b.e*)])
    ;; This code implies that the tag of a closure is #b000
    (values b* e*)))



(: sr-clos-ref-code (-> D0-Expr D0-Expr))
(define (sr-clos-ref-code clos)
  (Op 'Array-ref  (list clos CLOS-CODE-INDEX)))

(: sr-clos-ref-caster (-> D0-Expr D0-Expr))
(define (sr-clos-ref-caster clos)
  (Op 'Array-ref  (list clos CLOS-CSTR-INDEX)))


(define-type Env (HashTable Uid D0-Expr))

(define-syntax-rule (extend e k v)
  (hash-set e k v))

(: extend* (-> Env Uid* D0-Expr* Env))
(define (extend* env id* exp*)
  (match* (id* exp*)
    [('() _) env]
    [(_ '()) env]
    [((cons id id*) (cons exp exp*))
     (extend* (extend env id exp) id* exp*)]))

;; The variable is a normal variable
(: var  (-> Uid D0-Expr))
(define (var id) (Var id))

(: label (-> Uid D0-Expr))
(define (label id) (Code-Label id))

(: lookup (-> Env Uid D0-Expr))
(define (lookup e u)
  (hash-ref e u (lookup-error e u)))

(define (lookup-error e u)
  (lambda ()
    (error 'specify-representation/lookup
           "Unbound uid ~a\n\tin program with env ~a" u e)))

(define-type Triv (U (Quote String) (Quote Integer) (Code-Label Uid) (Var Uid)))
(define-predicate triv? Triv)

(: rename (-> String (-> Any String)))
(define (rename name)
  (lambda (_) name))

(define sr-quote : (D0-Literal -> D0-Expr) Quote)

(define (empty-index-map u i)
  (error 'specify-representation "attempt to index without index map ~a ~a" u i))

(: sr-tagged-array-ref (D0-Expr D0-Expr D0-Expr -> D0-Expr))
(define (sr-tagged-array-ref e t i)
  (sr-array-ref (sr-untag e t) i))

(: sr-tagged-array-set! (D0-Expr D0-Expr D0-Expr D0-Expr -> D0-Expr))
(define (sr-tagged-array-set! e t i v)
  (sr-array-set! (sr-untag e t) i v))

(: sr-array-ref (D0-Expr D0-Expr -> D0-Expr))
(define (sr-array-ref e i)
  (Op 'Array-ref (list e i)))

(: sr-array-set! (D0-Expr D0-Expr D0-Expr -> D0-Expr))
(define (sr-array-set! e i v)
  (Op 'Array-set! (list e i v)))

(: sr-untag (D0-Expr D0-Expr -> D0-Expr))
(define (sr-untag e t)
  (Op 'binary-xor `(,e ,t)))

;; there is some naming conflicts that must be taken care of
;; in this file
(: sr-tag-value (D0-Expr D0-Expr -> D0-Expr))
(define (sr-tag-value e t)
  (Op 'binary-or `(,e ,t)))

(: sr-check-tag=? (D0-Expr D0-Expr D0-Expr -> D0-Expr))
(define (sr-check-tag=? e mask tag)
  (Op '= `(,(Op 'binary-and `(,e ,mask)) ,tag)))

(: sr-plus (D0-Expr D0-Expr -> D0-Expr))
(define (sr-plus f s)
  (Op '+ (list f s)))

