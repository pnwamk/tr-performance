#lang typed/racket
#|
A little bit of clarification needs to be made in this pass
This pass is really about flattening the value context. So
that all begins and if are not allowed to occur there.

Remove complex opera is about creating a trivial context
where you known that there is an immediate aviailable without
further evaluation.

Simplify predicates is about getting control flow out of predicate
contexts.

In total these three passes force all computation to occur in
the tail context. This context might be innapropriately named
becuse it is actually more of a stmt contexts itself.

|#


(struct Uid ([prefix : String] [suffix : Natural]) #:transparent)

(define-type Uid* (Listof Uid))

(define FIRST-UID-SUFFIX 0)


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
  (Define rec? id type expression)
  ;; Top Level Forms
  (Expression e)
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
  ;; Prim Multi-way branching
  (Switch expr cases default)
  ;; Perform a No Operation
  (No-Op)
  ;; Effect operations
  ;; Monotonic effects
  (MboxS value) ;; source level mbox has no type annotation
  (Mbox value type)
  (Munbox box)
  (MunboxT box type)
  (Mbox-set! box value)
  (Mbox-set!T box value type)
  (Mbox-val-ref expression)
  (Mbox-val-set! expression1 expression2)
  (Mbox-rtti-ref address)
  (Mbox-rtti-set! address expression)
  (Make-Fn-Type expression1 expression2 expression3) ;; create meeted function type in runtime
  (Make-Tuple-Type expression1 expression2 expression3)
  ;; the underlying value can be accessed by the location encoded in the type
  (MBoxCastedRef addr type)
  (MBoxCastedSet! addr v type)
  (MvectorS value constructor)
  (Mvector value constructor type)
  (Mvector-size value)
  (Mvector-set! vector index value)
  (Mvector-set!T vector index value type)
  (Mvector-ref vector index)
  (Mvector-refT vector index type)
  (Mvector-val-ref vector index)
  (Mvector-val-set! vector index value)
  (Mvector-rtti-ref vector)
  (Mvector-rtti-set! address expression)
  (MVectCastedRef addr index type)
  (MVectCastedSet! addr index value type)
  ;; Guarded effects
  (Gbox value)
  (Gunbox box)
  (Gbox-set! box value)
  (Gvector len init-val)
  (Gvector-set! vector offset value)
  (Gvector-ref vector offset)
  ;;
  (Create-tuple values)
  (Copy-Tuple n v)
  (Tuple-proj tuple index)
  (Coerce-Tuple cast value coercion)
  (Coerce-Tuple-In-Place cast value coercion address)
  (Cast-Tuple cast value t1 t2 lbl)
  (Cast-Tuple-In-Place cast value t1 t2 lbl address)
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
  (Type-Fn index return-type argument-types)
  (Type-GRef type)
  (Type-GVect type)
  (Type-MRef type)
  (Type-MVect type)
  (Type-Fn-arity expression)
  (Type-Fn-arg expression index)
  (Type-Fn-return expression)
  (Type-Fn-Huh type)
  (Type-GVect-Huh type)
  (Type-GRef-Huh type)
  (Type-GRef-Of expression)
  (Type-GVect-Of expression)
  (Type-MRef-Huh expression)
  (Type-MRef-Of expression)
  (Type-MVect-Huh expression)
  (Type-MVect-Of expression)
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
  (Error expression)
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
  (Repeat var start end acc init body)
  (Break-Repeat)
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

(define-type (Switch-Case  e) (Pair (Listof Integer) e))
(define-type (Switch-Case* e) (Listof (Switch-Case e)))

(: map-switch-case :
   (All (A B) (A -> B) -> ((Switch-Case A) -> (Switch-Case B))))
(define ((map-switch-case f) c)
  (cons (car c) (f (cdr c))))

(: map-switch-case* :
   (All (A B) (A -> B) (Switch-Case* A) -> (Switch-Case* B)))
(define (map-switch-case* f c*)
  (map (map-switch-case f) c*))

(define NO-OP (No-Op))



(define-type Blame-Label String)
(define blame-label? string?)


#| Types throughout the languages |#

;; Schml types
(define-forms
  (Unit)
  (Int)
  (Float)
  (Bool)
  (Character)
  (Dyn)
  (Fn arity fmls ret)
  (MRef  arg)
  (MVect arg)
  (GRef  arg)
  (GVect arg)
  (STuple num items))

;;Constants for the types
(define UNIT-TYPE (Unit))
(define INT-TYPE (Int))
(define FLOAT-TYPE (Float))
(define BOOL-TYPE (Bool))
(define CHAR-TYPE (Character))
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
      (Character? t)
      (Float? t)
      (Unit? t)
      (fn-completely-static? t)
      (tuple-completely-static? t)
      (ref-completely-static? t)))




#|-----------------------------------------------------------------------------+
| Types shared by the Schml language family
+-----------------------------------------------------------------------------|#

#| Literals of the schml languages
Only Integers and Booleans in the schml language are first
class literal constants
|#

(define-type Schml-Literal
  (U Integer Boolean Null Real Char))

#;(: platform-integer? (Any -> Boolean : Integer))
#;
(define (platform-integer? x)
  (fixnum? x))

(: schml-literal? (Any -> Boolean : Schml-Literal))
(define (schml-literal? x)
  (or (exact-integer? x)
      (char? x)
      (boolean? x)
      (null? x)
      (real? x)))

(: schml-literal->base-type (Schml-Literal -> Base-Type))
(define (schml-literal->base-type x)
  (cond
    [(char? x) CHAR-TYPE]
    [(boolean? x) BOOL-TYPE]
    [(exact-integer? x) INT-TYPE]
    [(inexact-real? x) FLOAT-TYPE]
    [(null? x)    UNIT-TYPE]
    [else (error 'language/schml-literal->type "~a" x)]))

;; Types in the schml languages
(define-type  Base-Type (U Int Bool Unit Character Float))

(: base-type? (Any -> Boolean : Base-Type))
(define (base-type? x)
  (or (Int? x)
      (Bool? x)
      (Character? x)
      (Unit? x)
      (Float? x)))

(define-type+ Schml-Type ([Schml-Type* Listof]
			  [Schml-Type? Option])
  (U Dyn
     Base-Type
     Schml-Fn-Type
     Schml-Ref-Type
     Schml-Tuple-Type))

;; type known at runtime only for monotonic references, the uid is for
;; the entire reference cell, you have to access the second component
;; of the cell to get the type.

(define-type Schml-Fn-Type
  (Fn Index Schml-Type* Schml-Type))

(define-type Schml-Tuple-Type
  (STuple Index Schml-Type*))

(define-type Schml-Ref-Type
  (U (GRef  Schml-Type)
     (GVect Schml-Type)
     (MRef  Schml-Type)
     (MVect Schml-Type)))

(define-type Atomic-Type (U Base-Type Dyn))

(: atomic-type? : Any -> Boolean : Atomic-Type)
(define (atomic-type? x)
  (or (Dyn? x) (base-type? x)))

(: schml-type? (Any -> Boolean : Schml-Type))
(define (schml-type? x)
  (or (atomic-type? x)
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
(define-predicate schml-ref? Schml-Ref-Type)
(define-type+ Schml-Fml ([Schml-Fml* Listof])
  (Fml Uid Schml-Type))



(define-type ConsistentT (Schml-Type Schml-Type -> Boolean))
(: consistent? ConsistentT)
(define (consistent? t g)
  ;; (error 'foo))
  ;; Typed racket made me structure the code this way.
  (: both-unit? ConsistentT)
  (define (both-unit? t g) (and (Unit? t) (Unit? g)))
  (: both-bool? ConsistentT)
  (define (both-bool? t g) (and (Bool? t) (Bool? g)))
  (: both-int? ConsistentT)
  (define (both-int? t g) (and (Int? t) (Int? g)))
  (: both-char? ConsistentT)
  (define (both-char? t g) (and (Character? t) (Character? g)))
  (: both-float? ConsistentT)
  (define (both-float? t g) (and (Float? t) (Float? g)))
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
  (: consistent-mrefs? ConsistentT)
  (define (consistent-mrefs? t g)
    (and (MRef? t) (MRef? g)
         (consistent? (MRef-arg t) (MRef-arg g))))
  (: consistent-mvects? ConsistentT)
  (define (consistent-mvects? t g)
    (and (MVect? t) (MVect? g)
         (consistent? (MVect-arg t) (MVect-arg g))))
  (or (Dyn? t)
      (Dyn? g)
      (both-unit? t g)
      (both-bool? t g)
      (both-int? t g)
      (both-char? t g)
      (both-float? t g)
      (consistent-fns? t g)
      (consistent-tuples? t g)
      (consistent-grefs? t g)
      (consistent-gvects? t g)
      (consistent-mrefs? t g)
      (consistent-mvects? t g)))

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

(struct Bottom ([t1 : Schml-Type] [t2 : Schml-Type]) #:transparent)
(define-type Schml-Type?! (U Bottom Schml-Type))

#;(: join+ (Schml-Type* -> Schml-Type?!))
#;(define (join+ t+)
  (match t+
    [(list) (error 'join+ "needs non-empty list")]
    [(list t) t]
    [(cons t t+)
     (let ([t?! (join+ t+)])
       (if (Bottom? t?!)
           t?!
           (join t t?!)))]))

(: up ((Bottom -> Schml-Type) -> (Schml-Type Schml-Type -> Schml-Type)))
(define ((up exit) t g)
  (match* (t g)
    [((Dyn) g)     g]
    [(t     (Dyn)) t]
    [(t     t)     t]
    [(t     g)     (exit (Bottom t g))])
 )

(: down ((Bottom -> Schml-Type) -> (Schml-Type Schml-Type -> Schml-Type)))
(define ((down exit) t g)
  (match* (t g)
    [((and t (Dyn)) _) t]
    [(_ (and g (Dyn))) g]
    [(t t) t]
    [(t g) (exit (Bottom t g))])
 )
  
#;(: join (Schml-Type Schml-Type -> Schml-Type?!))
#;(define (join t g)
  ;; Typed racket made me do it...
  (call/ec
   (lambda ([exit : (Bottom -> Schml-Type)])
     (: j (Schml-Type Schml-Type -> Schml-Type))
     (define (j t g)
       (match* (t g)
         [((Dyn) g) g]
         [(t (Dyn)) t]
         [((Unit) (Unit)) UNIT-TYPE]
         [((Int)  (Int))  INT-TYPE]
         [((Bool) (Bool)) BOOL-TYPE]
         [((Fn ta ta* tr) (Fn ga ga* gr)) #:when (= ta ga)
          (Fn ta (map j ta* ga*) (j tr gr))]
         [((STuple ta t*) (STuple ga g*)) #:when (= ta ga)
          (STuple ta (map j t* g*))]
         [((GRef t) (GRef g))
          (GRef (j t g))]
         [((GVect t) (GVect g))
          (GVect (j t g))]
         [((MRef t) (MRef g))
          (j t g)]
         [(t g) (exit (Bottom t g))]))
     (j t g))))

(: move :
   (Schml-Type Schml-Type -> Schml-Type)
   -> (Schml-Type Schml-Type -> Schml-Type))
(define ((move u/d/fail) t g)
  (let m : Schml-Type ([t : Schml-Type t] [g : Schml-Type g])
       (match* (t g)
         [((Fn ta ta* tr) (Fn ga ga* gr)) #:when (= ta ga)
          (Fn ta (map m ta* ga*) (m tr gr))]
         [((STuple ta t*) (STuple ga g*)) #:when (= ta ga)
          (STuple ta (map m t* g*))]
         [((GRef t) (GRef g))
          (GRef (m t g))]
         [((GVect t) (GVect g))
          (GVect (m t g))]
         [((MRef t) (MRef g))
          (MRef (m t g))]
         [(t g) (u/d/fail t g)])))

(: move?! : ((Bottom -> Schml-Type) -> (Schml-Type Schml-Type -> Schml-Type))
   -> (Schml-Type Schml-Type -> Schml-Type?!))
(define ((move?! u/d) t g)
  (call/ec
   (lambda ([return : (Bottom -> Schml-Type)])
     ((move (u/d return)) t g))))

(: move+ : ((Bottom -> Schml-Type) -> (Schml-Type Schml-Type -> Schml-Type))
   -> (Schml-Type* -> Schml-Type?!))
(define ((move+ u/d) t+)
  (call/ec
   (lambda ([return : (Bottom -> Schml-Type)])
     (define m (move (u/d return)))
     (let move+ : Schml-Type ([t+ : Schml-Type* t+])
          (match t+
            [(list) (error 'move+ "must be non empty list")]
            [(list t) t]
            [(cons t t+) (m t (move+ t+))])))))

(: join : Schml-Type Schml-Type -> Schml-Type?!)
(define join (move?! up))

(: join+ : Schml-Type* -> Schml-Type?!)
(define join+ (move+ up))

(: meet : Schml-Type Schml-Type -> Schml-Type?!)
(define meet (move?! down))
(: meet+ : Schml-Type* -> Schml-Type?!)
(define meet+ (move+ down))


(define-forms
  (Coercion coercion)
  (Twosome type1 type2 lbl)
  ;; TODO Come up with a better name for this
  (Quote-Coercion const)
  (Compose-Coercions fst snd)
  (Make-Coercion t1 t2)
  ;; I am swithing to using the Cast and Interpreted Cast for the following
  ;; Forms
  ;(Coerce coercion expression) 
  ;(Interpreted-Coerce coercion expression)
  ;; Identity Cast
  ;; "Calculated No Op Cast"
  (Identity)
  (Id-Coercion-Huh expression)
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
  (Mediating-Coercion-Huh c)
  ;; Guarded Reference Coercion
  ;; "Proxy a Guarded Reference's Reads and writes"
  (Ref read write)
  (Ref-Coercion read write)
  (Ref-Coercion-Read expression)
  (Ref-Coercion-Write ref)
  (MonoRef type) ;; Monotonic Reference Coercion
  (MonoVect type)
  (MRef-Coercion type)
  (MRef-Coercion-Type expression)
  (MVect-Coercion expression)
  (MVect-Coercion-Type expression)
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
  (MRef-Coercion-Huh crcn)
  (MVect-Coercion-Huh crcn)
  (Fn-Coercion-Huh crcn)
  ;; (Make-Coercion t1 t2 lbl)
  (Make-Fn-Coercion make-uid t1 t2 lbl)
  (Compose-Fn-Coercion comp-uid c1 c2))

(define-type Cast-Fml* (Listof Cast-Fml))
(define-type Cast-Fml (Fml Uid Schml-Type))

(define-type Cast-Literal (U Schml-Literal Blame-Label))

(define-type Src srcloc)

(define-type Tag-Symbol (U 'Int 'Bool 'Char 'Unit
                           'Fn 'Atomic 'Boxed 'GRef
                           'GVect 'MRef 'MVect 'STuple))

(define-type Schml-Coercion
  (Rec C (U Identity
            (Project Schml-Type Blame-Label)
            (Inject Schml-Type)
            (Sequence C C)
            (Failed Blame-Label)
            (Fn Index (Listof C) C)
            (Ref C C)
            (MonoRef Schml-Type)
            (MonoVect Schml-Type)
            (CTuple Index (Listof C)))))

(define IDENTITY : Identity (Identity))

(define-type Schml-Coercion* (Listof Schml-Coercion))

(define-type Data-Literal (U Integer Inexact-Real Char String))

(: data-literal? : Any -> Boolean : Data-Literal)
(define (data-literal? x)
  (or (exact-integer? x)
      (inexact-real? x)
      (char? x)
      (string? x)))

#|------------------------------------------------------------------------------
  Compact Types and Coercions are a compile time hash-consing of types
  They are introduced by hoist types in Language Cast-or-Coerce3.1
------------------------------------------------------------------------------|#

;; Represents the shallow tree structure of types where all subtrees
;; of the type are either and atomic type or a identifier for a type.
(define-type Compact-Type
  (U (Fn Index (Listof Immediate-Type) Immediate-Type)
     (STuple Index (Listof Immediate-Type))
     (GRef Immediate-Type) (MRef Immediate-Type)
     (GVect Immediate-Type) (MVect Immediate-Type)))

;; Represent the shallow tree structure of coercions where all
;; subtrees of the type are either atomic types, the identity coercion
;; or coercion identifiers.
(define-type Compact-Coercion
  (U (Project Immediate-Type Blame-Label)
     (Inject Immediate-Type)
     (Sequence Immediate-Coercion Immediate-Coercion)
     (Failed Blame-Label)
     (Fn Index (Listof Immediate-Coercion) Immediate-Coercion)
     (MonoRef Immediate-Type)
     (MonoVect Immediate-Type)
     (CTuple Index (Listof Immediate-Coercion))
     (Ref Immediate-Coercion Immediate-Coercion)))

;; TODO (andre) a more descriptive name for this would be
;; Immediate-Type
(define-type Immediate-Type (U Atomic-Type (Static-Id Uid)))

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
 
(define-type Coercion/Immediate-Type
  (Rec C (U Identity
            (Failed Blame-Label)
            (Project Immediate-Type Blame-Label)
            (Inject Immediate-Type)
            (Sequence C C)
            (Fn Index (Listof C) C)
            (Ref C C)
            (MonoRef Immediate-Type)
            (MonoVect Immediate-Type)
            (CTuple Index (Listof C)))))

(define-type Coercion/Immediate-Type* (Listof Coercion/Immediate-Type))

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

(define-type Schml-Primitive (U Schml-Prim Schml-Prim!))
(define-predicate schml-primitive? Schml-Primitive)

(define-type Schml-Prim
  (U IntxInt->Int-Primitive
     IntxInt->Bool-Primitive
     ->Int-Primitive
     FloatxFloat->Float-Primitive
     Float->Float-Primitive
     ->Float-Primitive
     Int->Float-Primitive
     Float->Int-Primitive
     FloatxFloat->Bool-Primitive
     Char->Int-Primitive
     Int->Char-Primitive 
     ->Char-Primitive))

(define-predicate schml-prim? Schml-Prim)

(define-type Schml-Prim!
  (U Timer-Primitive
     Char->Unit-Primitive
     Int->Unit-Primitive
     FloatxInt->Unit-Primitive))

(define-predicate schml-prim!? Schml-Prim!)
#;(: schml-prim!? (Any -> Boolean : Schml-Prim!))
#;
(define (schml-prim!? x)
  (or (timer-primitive? x)))

(define-type IntxInt->Int-Primitive (U '* '+ '-
                                       'binary-and 'binary-or 'binary-xor
                                       '%/ '%>> '%<< '%%))

(define-type IxI->I-Prim IntxInt->Int-Primitive)

(define-predicate IntxInt->Int-primitive? IntxInt->Int-Primitive)

(define-type ->Int-Primitive (U 'read-int))
(define-type Int->Unit-Primitive (U 'print-int))
(define-type ->I-Prim ->Int-Primitive)

(define-predicate ->Int-primitive? ->Int-Primitive)

(define-type IntxInt->Bool-Primitive (U '< '<= '= '> '>=))
(define-type IxI->B-Prim IntxInt->Bool-Primitive)
(define-predicate IntxInt->Bool-primitive? IntxInt->Bool-Primitive)

(define-type FloatxFloat->Float-Primitive
  (U 'fl+ 'fl- 'fl* 'fl/ 'flmodulo 'flexpt))
(define-type Float->Float-Primitive
  (U 'flabs 'flround 'flfloor 'flceiling 'fltruncate
     'flsin 'flcos 'fltan 'flasin 'flacos 'flatan
     'fllog 'flexp 'flsqrt
     'flmin 'flmax))
(define-type FloatxInt->Unit-Primitive (U 'print-float))
(define-type ->Float-Primitive    (U 'read-float))
(define-type Int->Float-Primitive (U 'int->float))
(define-type Float->Int-Primitive (U 'float->int))
(define-type FloatxFloat->Bool-Primitive
  (U 'fl< 'fl<= 'fl= 'fl>= 'fl>))

(define-type ->Char-Primitive (U 'read-char))
(define-type Int->Char-Primitive (U 'int->char))
(define-type Char->Int-Primitive (U 'char->int))
(define-type Char->Unit-Primitive (U 'print-char 'display-char))

(define-predicate FloatxFloat->Float-primitive? FloatxFloat->Float-Primitive)
(define-predicate Float->Float-primitive? Float->Float-Primitive)
(define-predicate ->Float-primitive? ->Float-Primitive)
(define-predicate Int->Float-primitive? Int->Float-Primitive)
(define-predicate Float->Int-primitive? Float->Int-Primitive)
(define-predicate FloatxFloat->Bool-primitive? FloatxFloat->Bool-Primitive)

(define-type Timer-Primitive (U 'timer-start 'timer-stop 'timer-report))

(: timer-primitive? (Any -> Boolean : Timer-Primitive))
(define (timer-primitive? x)
  (or (eq? 'timer-start  x)
      (eq? 'timer-stop   x)
      (eq? 'timer-report x)))


(define INTxINT-TYPE (list INT-TYPE INT-TYPE))
(define INTxINT->BOOL-TYPE (Fn 2 INTxINT-TYPE BOOL-TYPE))
(define INTxINT->INT-TYPE (Fn 2 INTxINT-TYPE INT-TYPE))
(define ->INT-TYPE (Fn 0 '() INT-TYPE))

(define FLOATxFLOAT-TYPE (list FLOAT-TYPE FLOAT-TYPE))
(define FLOATxFLOAT->BOOL-TYPE (Fn 2 FLOATxFLOAT-TYPE BOOL-TYPE))
(define FLOATxFLOAT->FLOAT-TYPE (Fn 2 FLOATxFLOAT-TYPE FLOAT-TYPE))
(define FLOAT->FLOAT-TYPE (Fn 1 (list FLOAT-TYPE) FLOAT-TYPE))
(define ->FLOAT-TYPE (Fn 0 '() FLOAT-TYPE))

(define INT->FLOAT-TYPE (Fn 1 (list INT-TYPE) FLOAT-TYPE))
(define FLOAT->INT-TYPE (Fn 1 (list FLOAT-TYPE) INT-TYPE))

(define ->UNIT-TYPE (Fn 0 '() UNIT-TYPE))



(define ->CHAR-TYPE (Fn 0 '() CHAR-TYPE))
(define INT->CHAR-TYPE (Fn 1 (list INT-TYPE) CHAR-TYPE))
(define CHAR->INT-TYPE (Fn 1 (list CHAR-TYPE) INT-TYPE))


(define INT->UNIT-TYPE (Fn 1 (list INT-TYPE) UNIT-TYPE))
(define CHAR->UNIT-TYPE (Fn 1 (list CHAR-TYPE) UNIT-TYPE))
(define FLOAT->UNIT-TYPE (Fn 1 (list FLOAT-TYPE) UNIT-TYPE))
(define FLOATxINT->UNIT-TYPE (Fn 2 (list FLOAT-TYPE INT-TYPE) UNIT-TYPE))

(define schml-primitive-type-table
  : (HashTable Schml-Primitive (Fn Index (Listof Base-Type) Base-Type))
  (make-immutable-hash
   `((char->int  . ,CHAR->INT-TYPE)
     (int->char  . ,INT->CHAR-TYPE)
     (print-char . ,CHAR->UNIT-TYPE)
     (display-char . ,CHAR->UNIT-TYPE)
     (read-char  . ,->CHAR-TYPE)
     ;; Fixnum operations
     (* . ,INTxINT->INT-TYPE)
     (+ . ,INTxINT->INT-TYPE)
     (- . ,INTxINT->INT-TYPE)
     (%/ . ,INTxINT->INT-TYPE)
     (%% . ,INTxINT->INT-TYPE)
     (%>> . ,INTxINT->INT-TYPE)
     (%<< . ,INTxINT->INT-TYPE)
     (binary-and . ,INTxINT->INT-TYPE)
     (binary-or  . ,INTxINT->INT-TYPE)
     (binary-xor . ,INTxINT->INT-TYPE)
     (read-int . ,->INT-TYPE)
     (print-int . ,INT->UNIT-TYPE)
     (<  . ,INTxINT->BOOL-TYPE)
     (<= . ,INTxINT->BOOL-TYPE)
     (=  . ,INTxINT->BOOL-TYPE)
     (>  . ,INTxINT->BOOL-TYPE)
     (>= . ,INTxINT->BOOL-TYPE)
     ;; Float operations
     (fl+   . ,FLOATxFLOAT->FLOAT-TYPE)
     (fl-   . ,FLOATxFLOAT->FLOAT-TYPE)
     (fl*   . ,FLOATxFLOAT->FLOAT-TYPE)
     (fl/   . ,FLOATxFLOAT->FLOAT-TYPE)
     (flmodulo . ,FLOATxFLOAT->FLOAT-TYPE)
     (flabs . ,FLOAT->FLOAT-TYPE)
     (fl<   . ,FLOATxFLOAT->BOOL-TYPE)
     (fl<=  . ,FLOATxFLOAT->BOOL-TYPE)
     (fl=   . ,FLOATxFLOAT->BOOL-TYPE)
     (fl>=  . ,FLOATxFLOAT->BOOL-TYPE)
     (fl>   . ,FLOATxFLOAT->BOOL-TYPE)
     (flmin . ,FLOATxFLOAT->FLOAT-TYPE)
     (flmax . ,FLOATxFLOAT->FLOAT-TYPE)
     (flround . ,FLOAT->FLOAT-TYPE)
     (flfloor . ,FLOAT->FLOAT-TYPE)
     (flceiling . ,FLOAT->FLOAT-TYPE)
     (fltruncate . ,FLOAT->FLOAT-TYPE)
     ;; Float operations (trig)
     (flsin . ,FLOAT->FLOAT-TYPE)
     (flcos .  ,FLOAT->FLOAT-TYPE)
     (fltan .  ,FLOAT->FLOAT-TYPE)
     (flasin . ,FLOAT->FLOAT-TYPE)
     (flacos . ,FLOAT->FLOAT-TYPE)
     (flatan . ,FLOAT->FLOAT-TYPE)
     ;; Float operations (math)
     (fllog  . ,FLOAT->FLOAT-TYPE)
     (flexp  . ,FLOAT->FLOAT-TYPE)
     (flsqrt . ,FLOAT->FLOAT-TYPE)
     (flexpt . ,FLOATxFLOAT->FLOAT-TYPE)
     (float->int . ,FLOAT->INT-TYPE)
     (int->float . ,INT->FLOAT-TYPE)
     (read-float . ,->FLOAT-TYPE)
     (print-float . ,FLOATxINT->UNIT-TYPE) 
     (timer-start . ,->UNIT-TYPE)
     (timer-stop . ,->UNIT-TYPE)
     (timer-report . ,->UNIT-TYPE))))


(: schml-primitive->type
   (-> Schml-Primitive (Fn Index (Listof Base-Type) Base-Type)))
(define (schml-primitive->type p)
  (define (err) (error 'schml-primitive->type "invalid: ~a" p))
  (hash-ref schml-primitive-type-table p err))




#|-----------------------------------------------------------------------------
We are going to UIL
-----------------------------------------------------------------------------|#

(define-type UIL-Prim  (U Schml-Prim Array-Prim))
(define-type UIL-Prim! (U Schml-Prim! Array-Prim! Print-Prim! Bottom-Prim))
(define-predicate uil-prim-effect? UIL-Prim!)
(define-predicate uil-prim-value? UIL-Prim)

(define-type UIL-Expr-Prim
  (U ->Float-Primitive Float->Float-Primitive Float->Int-Primitive
     FloatxFloat->Float-Primitive
     Int->Float-Primitive Array-Prim IxI->I-Prim ->I-Prim
     ->Char-Primitive Char->Int-Primitive Int->Char-Primitive))

(define-type UIL-Pred-Prim (U FloatxFloat->Bool-Primitive
                              IntxInt->Bool-Primitive))

(define-predicate uil-prim-pred? UIL-Pred-Prim)

(define-type Array-Prim (U 'Alloc 'Array-ref))
(define-type Array-Prim! 'Array-set!)
(define-type Print-Prim! (U 'Printf 'Print 'print-float
                            'print-int 'print-char 'display-char))
(define-type Bottom-Prim (U 'Exit))

(define-type (UIL-Op E) (Op UIL-Prim (Listof E)))
(define-type (UIL-Op! E) (Op UIL-Prim! (Listof E)))


(: make-begin
   (case->
    (-> D3-Effect* No-Op D3-Effect)
    (-> D3-Effect* D3-Value D3-Value)
    (-> D3-Effect* D3-Tail  D3-Tail)
    (-> D3-Effect* D3-Pred  D3-Pred)
    #;(-> C7-Effect* C7-Value  C7-Value)
    #;(-> C7-Effect* No-Op C7-Effect)
    #;  (-> D3-Effect* D3-Trivial D3-Value)
        (-> D2-Effect* D2-Value  D2-Value)
        (-> D2-Effect* D2-Pred D2-Pred)
        (-> D2-Effect* No-Op D2-Effect)
        (-> D1-Effect* D1-Value  D1-Value)
        (-> D1-Effect* No-Op D1-Effect)
        (-> D4-Effect* D4-Tail D4-Tail)
        (-> D4-Effect* No-Op D4-Effect)
        (-> D5-Effect* D5-Tail D5-Tail)))
;; make a begin language form but splice nested begins into the
;; newly made begin.
(define (make-begin eff* res)
  (let ([eff* (foldr splice-eff '() eff*)])
    (cond
      [(null? eff*) res]
      ;; In effect position a begin of one effect is the ;
      ;; same as the effect alone
      [(and (No-Op? res) (null? (cdr eff*))) (car eff*)]
      ;; If the result is a begin I assume that the begin
      ;; was made with make-begin.
      [(Begin? res)
       (Begin (append eff* (Begin-effects res)) (Begin-value res))]
      [else (Begin eff* res)])))

(: splice-eff
   (case->
    ;; Since D2 effect is a strict subset of D1-effect
    ;; It must come before D1 because the first type to
    ;; match is used
    (-> D5-Effect D5-Effect* D5-Effect*)
    (-> D4-Effect D4-Effect* D4-Effect*)
    (-> D3-Effect D3-Effect* D3-Effect*)
    #;(-> C7-Effect C7-Effect* C7-Effect*)
    (-> D2-Effect D2-Effect* D2-Effect*)
    (-> D1-Effect D1-Effect* D1-Effect*)))
(define (splice-eff eff rest)
  (cond
    [(No-Op? eff) rest]
    [(Begin? eff) (foldr splice-eff rest (Begin-effects eff))]
    [else (cons eff rest)]))



(define-type Data1-Lang
  (Prog (List String Natural Schml-Type)
        (GlobDecs Uid*
                    (Labels D1-Bnd-Code*
                            D1-Tail))))

(define-type D1-Bnd-Code* (Listof D1-Bnd-Code))
(define-type D1-Bnd-Code (Pairof Uid D1-Code))
(define-type D1-Code (Code Uid* D1-Tail))

(define-type D1-Tail
  (Rec T
   (U (If D1-Pred T T)
      (Switch D1-Value (Switch-Case* T) T)
      (Begin D1-Effect* T)
      (App-Code D1-Value D1-Value*)
      (Op UIL-Expr-Prim D1-Value*)
      (Var Uid)
      Halt Success
      (Var Uid)
      (Code-Label Uid)
      (Quote D1-Literal))))

(define-type D1-Value
 (Rec V
      (U (If D1-Pred V V)
         (Switch V (Switch-Case* V) V)
         (Begin D1-Effect* V)
         (App-Code V (Listof V))
         (Op UIL-Expr-Prim (Listof V))
         Halt
         (Var Uid)
         (Code-Label Uid)
         (Quote D1-Literal))))

(define-type D1-Pred
 (Rec P
      (U (If D1-Pred P P)
         (Switch D1-Value (Switch-Case* P) P)
         (Begin D1-Effect* P)
         (Relop UIL-Pred-Prim D1-Value D1-Value))))

(define-type D1-Effect
 (Rec E
      (U (If D1-Pred E E)
         (Switch D1-Value (Switch-Case* E) E)
         (Begin D1-Effect* No-Op)
         (Repeat Uid D1-Value D1-Value #f #f E)
         Break-Repeat
         (App-Code D1-Value D1-Value*)
         (UIL-Op! D1-Value)
         (Assign Uid D1-Value)
         No-Op)))


(define-type D1-Value* (Listof D1-Value))
(define-type D1-Effect* (Listof D1-Effect))

(define-type D1-Bnd  (Pairof Uid D1-Value))

(define-type D1-Bnd* (Listof D1-Bnd))

(define-type D1-Literal Data-Literal)

(define-type Data2-Lang
  (Prog (List String Natural Schml-Type)
        (GlobDecs Uid*
                    (Labels D2-Bnd-Code*
                            D2-Body))))

(define-type D2-Body (Locals Uid* D2-Tail))
(define-type D2-Bnd-Code* (Listof D2-Bnd-Code))
(define-type D2-Bnd-Code (Pairof Uid D2-Code))
(define-type D2-Code (Code Uid* D2-Body))

(define-type D2-Tail D1-Tail)

(define-type D2-Value D1-Value)

(define-type D2-Pred D1-Pred)

(define-type D2-Effect D1-Effect)

(define-type D2-Value* (Listof D2-Value))

(define-type D2-Effect* (Listof D2-Effect))

(define-type D2-Literal Data-Literal)

(define-type Data5-Lang
  (Prog (List String Natural Schml-Type)
	(GlobDecs Uid*
                    (Labels D5-Bnd-Code*
                            D5-Body))))

(define-type D5-Body (Locals Uid* D5-Tail))
(define-type D5-Bnd-Code* (Listof D5-Bnd-Code))
(define-type D5-Bnd-Code (Pairof Uid D5-Code))
(define-type D5-Code (Code Uid* D5-Body))

(define-type D5-Tail
  (Rec T
   (U (If D5-Pred T T)
      (Switch D5-Trivial (Switch-Case* T) T)
      (Begin D5-Effect* T)
      (Return D5-Value)
      (Return Success))))

(define-type D5-Pred (Relop UIL-Pred-Prim D5-Trivial D5-Trivial))

(define-type D5-Effect
  (U (Repeat Uid D5-Trivial D5-Trivial #f #f (Begin D5-Effect* No-Op))
     (If D5-Pred (Begin D5-Effect* No-Op) (Begin D5-Effect* No-Op))
     Break-Repeat
     (Switch D5-Trivial
             (Switch-Case* (Begin D5-Effect* No-Op))
             (Begin D5-Effect* No-Op))
     (UIL-Op! D5-Trivial)
     (Assign Uid D5-Value)
     No-Op))

(define-type D5-Value
  (U D5-Trivial
     Halt
     (UIL-Op D5-Trivial)
     (App-Code D5-Trivial D5-Trivial*)
     (If D5-Pred D5-Trivial D5-Trivial)))

(define-type D5-Trivial
  (U (Code-Label Uid)
     (Var Uid)
     (Quote D5-Literal)))

(define-type D5-Trivial* (Listof D5-Trivial))
(define-type D5-Effect* (Listof D5-Effect))
(define-type D5-Value* (Listof D5-Value))

(define-type D5-Literal Data-Literal)


(define-type Data3-Lang
  (Prog (List String Natural Schml-Type)
	(GlobDecs Uid*
                    (Labels D3-Bnd-Code*
                            D3-Body))))

(define-type D3-Body (Locals Uid* D3-Tail))
(define-type D3-Bnd-Code* (Listof D3-Bnd-Code))
(define-type D3-Bnd-Code (Pairof Uid D3-Code))
(define-type D3-Code (Code Uid* D3-Body))

(define-type D3-Tail
  (Rec T
   (U (If D3-Pred T T)
      (Switch D3-Trivial (Switch-Case* T) T)
      (Begin D3-Effect* T)
      (Return D3-Value)
      (Return Success))))

(define-type D3-Value
 (Rec V
  (U D3-Trivial
     Halt
     (If D3-Pred V V)
     (Switch D3-Trivial (Switch-Case* V) V)
     (Begin D3-Effect* V)
     (Op UIL-Expr-Prim (Listof D3-Trivial))
     (App-Code D3-Trivial D3-Trivial*))))

(define-type D3-Pred
 (Rec P
      (U (If D3-Pred P P)
         (Switch D3-Trivial (Switch-Case* P) P)
         (Begin D3-Effect* P)
         (Relop UIL-Pred-Prim D3-Trivial D3-Trivial))))

(define-type D3-Effect
 (Rec E
      (U (If D3-Pred E E)
         (Switch D3-Trivial (Switch-Case* E) E)
         (Begin D3-Effect* No-Op)
         (Repeat Uid D3-Trivial D3-Trivial #f #f E)
         Break-Repeat
         (App-Code D3-Trivial D3-Trivial*)
         (UIL-Op! D3-Trivial)
         (Assign Uid D3-Value)
         No-Op)))

;; (TODO halt is not trivial though because we are targeting c it may be treated so)
;; remove Halt earlier
(define-type D3-Trivial
  (U (Code-Label Uid)
     (Var Uid)
     (Quote D3-Literal)))

(define-type D3-Value* (Listof D3-Value))
(define-type D3-Trivial* (Listof D3-Trivial))
(define-type D3-Effect* (Listof D3-Effect))

(define-type D3-Literal Data-Literal)

(define-type Data4-Lang
  (Prog (List String Natural Schml-Type)
	(GlobDecs Uid*
                    (Labels D4-Bnd-Code*
                            D4-Body))))

(define-type D4-Body (Locals Uid* D4-Tail))
(define-type D4-Bnd-Code* (Listof D4-Bnd-Code))
(define-type D4-Bnd-Code (Pairof Uid D4-Code))
(define-type D4-Code (Code Uid* D4-Body))

(define-type D4-Tail
  (Rec T
   (U (If D4-Pred T T)
      (Switch D4-Trivial (Switch-Case* T) T)
      (Begin D4-Effect* T)
      (Return D4-Value)
      (Return Success))))

(define-type D4-Pred
 (Rec P
      (U (If D4-Pred P P)
         (Switch D4-Trivial (Switch-Case* P) P)
         (Begin D4-Effect* P)
         (Relop UIL-Pred-Prim D4-Trivial D4-Trivial))))

(define-type D4-Effect
 (Rec E
      (U (If D4-Pred E E)
         (Switch D4-Trivial (Switch-Case* E) E)
         (Begin D4-Effect* No-Op)
         (Repeat Uid D4-Trivial D4-Trivial #f #f E)
         (UIL-Op! D4-Trivial)
         (Assign Uid D4-Value)
         Break-Repeat
         No-Op)))

(define-type D4-Value
  (U D4-Trivial
     Halt
     (UIL-Op D4-Trivial)
     (App-Code D4-Trivial D4-Trivial*)))

(define-type D4-Trivial
  (U (Code-Label Uid)
     (Var Uid)
     (Quote D4-Literal)))


(define-type D4-Trivial* (Listof D4-Trivial))
(define-type D4-Effect* (Listof D4-Effect))

(define-type D4-Literal Data-Literal)


(provide flatten-values)
(: flatten-values (Data3-Lang -> Data4-Lang))
(define (flatten-values prog)
  (error 't))

;; Simple recursion into the body of code bindings
(: fv-bnd-code (D3-Bnd-Code -> D4-Bnd-Code))
(define (fv-bnd-code bnd)
  (error 't))

;; Add new local variables to the declaration to each body
(: fv-body (D3-Body -> D4-Body))
(define (fv-body body)
  (error 't))

(: fv-trivial (D3-Trivial -> D4-Trivial))
(define (fv-trivial triv)
  (error 't))

(: fv-trivial* (D3-Trivial* -> D4-Trivial*))
(define (fv-trivial* t*)
  (error 't))


