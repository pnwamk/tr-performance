#lang typed/racket/base
(require
 racket/match
 racket/format
 racket/list
 (for-syntax typed/racket))

(provide (all-defined-out))





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

(define-for-syntax syntax-id
  (syntax-rules ()
    [(_ x ...) (begin x ...)]))

(define-for-syntax syntax-void
  (syntax-rules ()
    [(_ x ...) (void)]))

;; only run this code if we are working on schml
(define-syntax if-in-construction
  syntax-void)

(struct exn:todo exn ())
(begin-for-syntax (struct exn:todo exn ()))

(define-syntax TODO
  (lambda (x)
    (define loc-string
      (srcloc->string
       (srcloc (syntax-source x) (syntax-line x) (syntax-column x)
               (syntax-position x) (syntax-span x))))
    (raise-syntax-error
     'Unfinished-TODO
     (format "~a: ~a" loc-string (syntax->datum x)))))

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
;       ;;;                                     
;      ;                                        
;      ;                                        
;    ;;;;;;    ;;;      ; ;;;  ;;;;;;    ;;;;;  
;      ;      ;   ;     ;;   ; ;  ;  ;  ;     ; 
;      ;     ;     ;    ;      ;  ;  ;  ;       
;      ;     ;     ;    ;      ;  ;  ;  ;;;;    
;      ;     ;     ;    ;      ;  ;  ;     ;;;; 
;      ;     ;     ;    ;      ;  ;  ;        ; 
;      ;      ;   ;     ;      ;  ;  ;  ;     ; 
;      ;       ;;;      ;      ;  ;  ;   ;;;;;  
;                                               
;                                               
;                                               
;                                               


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
;                                                                                                                                  ;;;;   
;                                ;                                                                                                ;    ;; 
;                                ;                                                                                                      ; 
;     ;;;      ;;;;    ;;;;;   ;;;;;;              ;;;      ; ;;;             ;;;      ;;;      ;;;      ; ;;;    ;;;      ;;;          ; 
;    ;   ;    ;    ;  ;     ;    ;                ;   ;     ;;   ;           ;   ;    ;   ;    ;   ;     ;;   ;  ;   ;    ;   ;        ;; 
;   ;              ;  ;          ;               ;     ;    ;               ;        ;     ;  ;     ;    ;      ;        ;     ;    ;;;   
;   ;         ;;;;;;  ;;;;       ;        ;;;;   ;     ;    ;        ;;;;   ;        ;     ;  ;     ;    ;      ;        ;     ;       ;; 
;   ;        ;;    ;     ;;;;    ;               ;     ;    ;               ;        ;     ;  ;;;;;;;    ;      ;        ;;;;;;;        ; 
;   ;        ;     ;        ;    ;               ;     ;    ;               ;        ;     ;  ;          ;      ;        ;              ; 
;    ;   ;   ;    ;;  ;     ;    ;                ;   ;     ;                ;   ;    ;   ;    ;    ;    ;       ;   ;    ;    ;  ;    ;; 
;     ;;;     ;;;; ;   ;;;;;      ;;;              ;;;      ;                 ;;;      ;;;      ;;;;     ;        ;;;      ;;;;    ;;;;;  
;                                                                                                                                         
;                                                                                                                                         
;                                                                                                                                         
;                                                                                                                                         


(define-type Cast-or-Coerce3-Lang
 (Prog (List String Natural Schml-Type) CoC3-Expr))

(define-type CoC3-Expr
  (Rec E (U ;; Code Labels
          (Code-Label Uid)
          (Labels CoC3-Bnd-Code* E)
          (App-Code E (Listof E))
          ;; Functions as an interface
          (Lambda Uid* (Castable (Option Uid) E))
          (Fn-Caster E)
          (App-Fn E (Listof E))
          ;; Our Lovely Function Proxy Representation
          (App-Fn-or-Proxy Uid E (Listof E))
          (Fn-Proxy (List Index Uid) E E)
          (Fn-Proxy-Huh E)
          (Fn-Proxy-Closure E)
          (Fn-Proxy-Coercion E)
          ;; Coercions
          (Quote-Coercion Schml-Coercion)
          (Compose-Coercions E E)
          (Id-Coercion-Huh E)
          (Fn-Coercion-Huh E)
          (Make-Fn-Coercion Uid E E E)
          (Compose-Fn-Coercion Uid E E)
          (Fn-Coercion (Listof E) E)
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
          (Type Schml-Type)
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
          ;; Binding Forms - Lambda
	  (Letrec CoC3-Bnd* E)
	  (Let CoC3-Bnd* E)
          (Var Uid)
          ;; Controll Flow
          (If E E E)
          (Begin CoC3-Expr* E)
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

(define-type CoC3-Code (Code Uid* CoC3-Expr))


(define-type CoC3-Expr* (Listof CoC3-Expr))
(define-type CoC3-Bnd (Pairof Uid CoC3-Expr))
(define-type CoC3-Bnd* (Listof CoC3-Bnd))
(define-type CoC3-Bnd-Code (Pairof Uid CoC3-Code))
(define-type CoC3-Bnd-Code* (Listof CoC3-Bnd-Code))



;                                                                                                                                                                                      
;                                                                                                                                                                                      
;                                                                                                                                                                                      
;      ;                                                                                                                                            ;                 ;;;              
;      ;                ;                                                     ;                                            ;                        ;                   ;              
;                       ;                                                     ;                                            ;                        ;                   ;              
;    ;;;     ; ;;;;   ;;;;;;     ;;;      ; ;;;  ; ;;;      ; ;;;    ;;;    ;;;;;;              ;;;      ;;;;    ;;;;;   ;;;;;;    ;;;;;            ; ;;;;     ;;;      ;      ; ;;;   
;      ;     ;;   ;;    ;       ;   ;     ;;   ; ;;   ;     ;;   ;  ;   ;     ;                ;   ;    ;    ;  ;     ;    ;      ;     ;           ;;   ;;   ;   ;     ;      ;;   ;  
;      ;     ;     ;    ;      ;     ;    ;      ;     ;    ;      ;     ;    ;               ;              ;  ;          ;      ;                 ;     ;  ;     ;    ;      ;     ; 
;      ;     ;     ;    ;      ;     ;    ;      ;     ;    ;      ;     ;    ;        ;;;;   ;         ;;;;;;  ;;;;       ;      ;;;;       ;;;;   ;     ;  ;     ;    ;      ;     ; 
;      ;     ;     ;    ;      ;;;;;;;    ;      ;     ;    ;      ;;;;;;;    ;               ;        ;;    ;     ;;;;    ;         ;;;;           ;     ;  ;;;;;;;    ;      ;     ; 
;      ;     ;     ;    ;      ;          ;      ;     ;    ;      ;          ;               ;        ;     ;        ;    ;            ;           ;     ;  ;          ;      ;     ; 
;      ;     ;     ;    ;       ;    ;    ;      ;;   ;     ;       ;    ;    ;                ;   ;   ;    ;;  ;     ;    ;      ;     ;           ;     ;   ;    ;    ;      ;;   ;  
;   ;;;;;;;  ;     ;     ;;;     ;;;;     ;      ; ;;;      ;        ;;;;      ;;;              ;;;     ;;;; ;   ;;;;;      ;;;    ;;;;;            ;     ;    ;;;;      ;;;   ; ;;;   
;                                                ;                                                                                                                             ;       
;                                                ;                                                                                                                             ;       
;                                                ;                                                                                                                             ;       
;                                                                                                                                                                                      






;; Configuration that spans multiple passes
(: specialize-casts? (Parameterof Boolean))
(define specialize-casts? (make-parameter #f))



;; inline-guarded-branch
;; Parameter determining if the code generated for gbox-set! and gunbox
;; performs the first check to see if the gref is a unguarded reference
;; or delegates the entire operation to the runtime.
;; This is only used for the twosome representation
(: inline-guarded-branch? (Parameterof Boolean))
(define inline-guarded-branch? (make-parameter #f))

(define-type Function-Proxy-Rep (U 'Data 'Hybrid 'Functional))
(: function-cast-representation (Parameterof Function-Proxy-Rep))
(define function-cast-representation
  (make-parameter 'Hybrid))



;; Expr$ and cond$ will prune branches if the condition is (Quote #t) or (Quote #f)
;; and generates If statements (to construct the cast tree)
(: if/specialization (CoC3-Expr (-> CoC3-Expr) (-> CoC3-Expr) -> CoC3-Expr))
(define (if/specialization t c a)
  (if (Quote? t)
      (if (Quote-literal t) (c) (a))
      (If t (c) (a))))

;; better syntax for calling if/specialization
(define-syntax-rule (if$ t c a)
  (if/specialization t (lambda () c) (lambda () a)))

;; Pure version of the above use for programming in
;; the object language with and/or
(: if$_ (CoC3-Expr CoC3-Expr CoC3-Expr -> CoC3-Expr))
(define (if$_ t c a)
  (if (Quote? t)
      (if (Quote-literal t) c a)
      (If t c a)))

(: and$ (CoC3-Expr CoC3-Expr -> CoC3-Expr))
(define (and$ fst snd)
  (if$_ fst snd (Quote #f)))

(: or$ (CoC3-Expr CoC3-Expr -> CoC3-Expr))
(define (or$ fst snd)
  (if$_ fst (Quote #t) snd))

(define-syntax cond$
  (syntax-rules (else)
    [(_ (else c)) c]
    [(_ (t c) (t* c*) ...)
     (if$ t c (cond$ (t* c*) ...))]))

;; make sure that t is a trivial expression
(define-type CoC3-Trivial (U (Quote-Coercion Schml-Coercion)
                             (Quote Cast-Literal)
                             (Tag Tag-Symbol)
                             (Type Schml-Type)
                             (Var Uid)))
#|
;(: trivial? (CoC3-Expr -> Boolean : Trivial))
(define (trivial? x)
  (or (Quote? x)
      (Tag? x)
      (Type? x)
      (Var? x)))

(: trivialize ((Box Nat) String CoC3-Expr CoC3-Bnd* ->
               (Pair CoC3-Bnd* let$-Trivial)))
(define (trivialize next s e b*)
  (if (or (Quote? e) (Tag? e) (Type? e) (Var? e))
      `(,b* . ,e)
      (let ([u (unbox next)])
        (set-box! next (add1 u))
        ())
      (bind-state
       (uid-state s)
       (lambda ([u : Uid])
         : (State Nat (Pair CoC3-Bnd* (Var Uid)))
         (return-state `(((,u . ,e) . ,b*) . ,(Var u)))))))

;; This is meant to help let$* which accumulates the list of
;; bindings backwards. This gives proper let* behavior
(: let$*-help (CoC3-Bnd* CoC3-Expr -> CoC3-Expr))
(define (let$*-help b* b)
  (if (null? b*)
      b
      (let$*-help (cdr b*) (Let (list (car b*)) b))))
|#

(: make-trivialize :
   (String -> Uid)
   -> 
   (String CoC3-Expr (Listof (Pairof Uid CoC3-Expr))
           ->
           (Values CoC3-Bnd* CoC3-Trivial)))
(define ((make-trivialize next-uid!) name expr bnd*)
  (if (or (Quote? expr) (Tag? expr) (Type? expr)
          (Var? expr) (Quote-Coercion? expr))
      (values bnd* expr)
      (let ([uvar (next-uid! name)])
        (values (cons (cons uvar expr) bnd*) (Var uvar)))))

;; createsCoC3-Expr let bindings for non-trivial CoC3-Expr expressions,
;; since non-trivial expressions must be evaluated only once.
;; This has to be a macro because it plays with what value is bound to
;; the t* variable in the code in order to reduce the number of cases
;; that must be handle
(define-syntax-rule (define-syntax-let$* let$* next-uid!)
  (... ;; Quote-ellipsis
   (begin
     (define trivialize (make-trivialize next-uid!))
     (: let$*-help ((Listof (Pairof Uid CoC3-Expr)) CoC3-Expr -> CoC3-Expr))
     (define (let$*-help b* b)
       (if (null? b*)
           b
           (let$*-help (cdr b*) (Let (list (car b*)) b))))
     (define-syntax let$*
       (syntax-rules ()
         [(_ () b) b]
         [(_ ([t* v*] ...) b)
          (let ([b* : (Listof (Pairof Uid CoC3-Expr)) '()])
            (let*-values ([(b* t*) (trivialize (~a 't*) v* b*)] ...)
              (let ([body : CoC3-Expr b])
                (let$*-help b* body))))])))))

#|
(do (bind-state : (State Nat CoC3-Expr))
    ((cons b* t*) : (Pair CoC3-Bnd* CoC3-Trivial)
     <- (trivialize (~a 't*) v* b*)) ...
     (b^ : CoC3-Expr <- b)
     (if (null? b*)
         (return-state b^)
         (return-state (let$*-help b* b^))))|#



;; performs compile time folding of prim = on literals
;; todo convert this to using eq-huh
;; TODO this should be op=?$
(: op=? (CoC3-Expr CoC3-Expr -> CoC3-Expr))
(define (op=? o x)
  (cond
    [(and (Quote? o) (Quote? x)) (Quote (eq? (Quote-literal o)
                                             (Quote-literal x)))]
    [(and (Tag? o) (Tag? x)) (Quote (eq? (Tag-bits o) (Tag-bits x)))]
    [(and (Type? o) (Type? x)) (Quote (equal? (Type-type o) (Type-type x)))]
    [else (Op '= (list o x))]))

(: op<=? (CoC3-Expr CoC3-Expr -> CoC3-Expr))
(define (op<=? o x)
  (cond
    [(and (Quote? o) (Quote? x))
     (let ([n1 (Quote-literal o)]
           [n2 (Quote-literal x)])
       (if (and (integer? n1) (integer? n2))
           (Quote (<= n1 n2))
           (error 'interpret-casts/op<=? "Unexpected ~a ~a" n1 n2)))]
    [else (Op '<= (list o x))]))

;;These functions type to fold predicates in order to allow ifs to
;;generate only checks that are actually needed
(: type-tag (-> CoC3-Expr CoC3-Expr))
(define (type-tag o)
  (if (Type? o)
      (let ([v (Type-type o)])
        (cond
          [(or (Dyn? v) (Int? v) (Bool? v) (Unit? v))
           (Tag 'Atomic)]
          [(GRef? v) (Tag 'GRef)]
          [(GVect? v) (Tag 'GVect)]
          [(Fn? v) (Tag 'Fn)]
          [(STuple? v) (Tag 'STuple)]
          [else (error 'interpret-casts/type-tag
                       "Unexpected ~a" v)]))
      (Type-Tag o)))

(: type-fn-arity (CoC3-Expr -> CoC3-Expr))
(define (type-fn-arity o)
  (cond
    [(not (Type? o)) (Type-Fn-arity o)]
    [(Fn? (Type-type o)) (Quote (Fn-arity (Type-type o)))]
    [else (error 'ic/type-fn-arity "bad value?: ~a" o)]))

(: type-tuple-num (CoC3-Expr -> CoC3-Expr))
(define (type-tuple-num o)
  (cond
    [(not (Type? o)) (Type-Tuple-num o)]
    [(STuple? (Type-type o))  (Quote (STuple-num (Type-type o)))]
    [else (error 'ic/type-tuple-num "bad value?: ~a" o)]))


(define-syntax-rule
  (define-smart-coercion? (name compile-time? run-time?) ...)
  (begin
    (: name (CoC3-Expr -> CoC3-Expr)) ...
    (define (name x)
      (if (not (Quote-Coercion? x))
          (run-time? x)
          (let ([x (Quote-Coercion-const x)])
            (if (compile-time? x)
                (Quote #t)
                (Quote #f))))) ...))

(define-smart-coercion?
  (id?$              Identity?       Id-Coercion-Huh)
  (seq?$             Sequence?       Sequence-Coercion-Huh)
  (prj?$             Project?        Project-Coercion-Huh)
  (inj?$             Inject?         Inject-Coercion-Huh)
  (fail?$            Failed?         Failed-Coercion-Huh)
  (fnC?$             Fn?             Fn-Coercion-Huh)
  (ref?$             Ref?            Ref-Coercion-Huh)
  (tuple?$           CTuple?         Tuple-Coercion-Huh)
  (mediating-crcn?$  mediating-crcn? Mediating-Coercion-Huh?))

(define (mediating-crcn? x)
  (or (CTuple? x) (Ref? x) (Fn? x)))

(define-syntax-rule
  (define-smart-access (name check kuote compile-time run-time) ...)
  (begin
    (: name (CoC3-Expr -> CoC3-Expr)) ...
    (define (name x)
      (if (not (Quote-Coercion? x))
          (run-time x)
          (let ([x (Quote-Coercion-const x)])
            (if (check x)
                (kuote (compile-time x))
                (error 'interpret-casts "~a applied to ~a" 'name x)))))
    ...))

(define-smart-access
  (seq-fst$    Sequence?  Quote-Coercion Sequence-fst  Sequence-Coercion-Fst)
  (seq-snd$    Sequence?  Quote-Coercion Sequence-snd  Sequence-Coercion-Snd)
  (prj-type$   Project?   Type           Project-type  Project-Coercion-Type)
  (prj-label$  Project?   Quote          Project-label Project-Coercion-Label)
  (inj-type$   Inject?    Type           Inject-type   Inject-Coercion-Type)
  (ref-read$   Ref?       Quote-Coercion Ref-read      Ref-Coercion-Read)
  (ref-write$  Ref?       Quote-Coercion Ref-write     Ref-Coercion-Write)
  (tuple-num$  CTuple?    Quote          CTuple-num    Tuple-Coercion-Num)
  (fail-label$ Failed?    Quote          Failed-label  Failed-Coercion-Label))

(: tuple-crcn-arg$ (CoC3-Expr Index -> CoC3-Expr))
(define (tuple-crcn-arg$ x i)
  (if (not (Quote-Coercion? x))
      (Tuple-Coercion-Item x i)
      (let ([x (Quote-Coercion-const x)])
        (if (CTuple? x)
            (Quote-Coercion (list-ref (CTuple-items x) i))
            (error 'interpret-casts "~a applied to ~a" 'tuple-crcn x)))))

(: tuple-type-arg$ (CoC3-Expr Index -> CoC3-Expr))
(define (tuple-type-arg$ x i)
  (if (not (Type? x))
      (Type-Tuple-item x i)
      (let ([x (Type-type x)])
        (if (STuple? x)
            (Type (list-ref (STuple-items x) i))
            (error 'interpret-casts "~a applied to ~a" 'tuple-type x)))))

(define-syntax-rule
  (define-smart-coercion (name compile-time run-time field ...) ...)
  (begin
    (define (name (field : CoC3-Expr) ...) : CoC3-Expr
      (if (and (Quote-Coercion? field) ...)
          (Quote-Coercion (compile-time (Quote-Coercion-const field) ...))
          (run-time field ...)))
    ...))

(define-smart-coercion
  (seq$  Sequence Sequence-Coercion fst snd)
  (ref$  Ref      Ref-Coercion      read write))

(: inj$ (CoC3-Expr -> CoC3-Expr))
(define (inj$ type)
  (if (Type? type)
      (let ([t (Type-type type)])
        (Quote-Coercion (Inject t)))
      (Inject-Coercion type)))

(: prj$ (CoC3-Expr CoC3-Expr -> CoC3-Expr))
(define (prj$ type label)
  (if (and (Type? type) (Quote? label))
      (let ([t (Type-type type)]
            [s (Quote-literal label)])
        (if (string? s)
            (Quote-Coercion (Project t s))
            (error 'proj$ "given ~a ~a" t s)))
      (Project-Coercion type label)))

(: fail$ (CoC3-Expr -> CoC3-Expr))
(define (fail$ label)
  (cond
    [(not (Quote? label)) (Failed-Coercion label)]
    [else
     (let ([s (Quote-literal label)])
       (if (string? s)
           (Quote-Coercion (Failed s))
           (error 'fail$ "given ~a" s)))]))

(define-syntax-rule
  (define-smart-type? (name compile-time? run-time?) ...)
  (begin
    (: name (CoC3-Expr -> CoC3-Expr)) ...
    (define (name x)
      (if (not (Type? x))
          (run-time? x)
          (let ([x (Type-type x)])
            (if (compile-time? x)
                (Quote #t)
                (Quote #f))))) ...))

(define-smart-type?
  (dyn?$    Dyn?    Type-Dyn-Huh)
  (fnT?$    Fn?     Type-Fn-Huh)
  (gvect?$  GVect?  Type-GVect-Huh)
  (gref?$   GRef?   Type-GRef-Huh)
  (tupleT?$ STuple? Type-Tuple-Huh))

(: fnT-arity$ (CoC3-Expr -> CoC3-Expr))
(define (fnT-arity$ x)
  (if (not (Type? x))
      (Type-Fn-arity x)
      (let ([x (Type-type x)])
        (if (Fn? x)
            (Quote (Fn-arity x))
            (error 'fnT-arity$ "given ~a" x)))))

(: tupleT-num$ (CoC3-Expr -> CoC3-Expr))
(define (tupleT-num$ x)
  (if (not (Type? x))
      (Type-Tuple-num x)
      (let ([x (Type-type x)])
        (if (STuple? x)
            (Quote (STuple-num x))
            (error 'tupleT-num$ "given ~a" x)))))

(: gvect-of$ (CoC3-Expr -> CoC3-Expr))
(define (gvect-of$ x)
  (if (not (Type? x))
      (Type-GVect-Of x)
      (let ([x (Type-type x)])
        (if (GVect? x)
            (Type (GVect-arg x))
            (error 'gvect-of$ "given ~a" x)))))

(: gref-of$ (CoC3-Expr -> CoC3-Expr))
(define (gref-of$ x)
  (if (not (Type? x))
      (Type-GRef-Of x)
      (let ([x (Type-type x)])
        (if (GRef? x)
            (Type (GRef-arg x))
            (error 'gvect-of$ "given ~a" x)))))

(: bnd-non-vars
   (((String -> Uid) CoC3-Expr*) (#:names (Option (Listof String)))
    . ->* .
    (Values CoC3-Bnd* (Listof (Var Uid)))))
(define (bnd-non-vars next-uid! e* #:names [names? #f])
  (define names : (Listof String) (or names? (make-list (length e*) "tmp")))
  (define-values (bnd* var*)
    (for/fold ([bnd* : CoC3-Bnd* '()]
               [var* : (Listof (Var Uid)) '()])
              ([e : CoC3-Expr e*]
               [n : String names])
      (cond
        [(Var? e) (values bnd* (cons e var*))]
        [else
         (let ([u (next-uid! n)])
           (values (cons (cons u e) bnd*) (cons (Var u) var*)))])))
  #;(printf "bnd-non-vars:\ne*=~a\nnames=~a\nbnd*=~a\nvar*=~a\n\n"
          e* names? bnd* var*)
  (values bnd* (reverse var*)))


(: apply-code
   (All (A)
     (Uid -> (->* () #:rest A (App-Code (Code-Label Uid) (Listof A))))))
(define ((apply-code u) . a*)
  (App-Code (Code-Label u) a*))
