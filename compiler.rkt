#lang racket
(require racket/set racket/stream)
(require racket/list)
(require racket/fixnum)
;(require "interp-Lint.rkt")
;(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "interp-Lvec.rkt")
(require "type-check-Lvec.rkt")
(require "interp-Cvec.rkt")
(require "type-check-Cvec.rkt")
(require "interp.rkt")
(require "type-check-Cvar.rkt")
;(require "type-check-Lvar.rkt")
(require "interp-Cif.rkt")
(require "type-check-Cif.rkt")
(require "interp-Lif.rkt")
(require "type-check-Lif.rkt")
(require "interp-Lwhile.rkt")
(require "type-check-Lwhile.rkt")

(require "interp-Cwhile.rkt")
(require "type-check-Cwhile.rkt")
(require "utilities.rkt")
(provide (all-defined-out))
(require graph)
(define physical-registers
  (set 'rax 'rbx 'rcx 'rdx 'rsi 'rdi 'r8 'r9 'r10 'r11 'r15))
(define (is-var? x)
  (not (set-member? physical-registers x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lint examples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The following compiler pass is just a silly one that doesn't change
;; anything important, but is nevertheless an example of a pass. It
;; flips the arguments of +. -Jeremy
(define (flip-exp e)
  (match e
    [(Var x) e]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (Prim '- (list (flip-exp e1)))]
    [(Prim '+ (list e1 e2)) (Prim '+ (list (flip-exp e2) (flip-exp e1)))]))

(define (flip-Lint e)
  (match e
    [(Program info e) (Program info (flip-exp e))]))

(define (shrink-exp e)
  (match e
    [(Int _) e]
    [(Bool _) e]
    [(Var _) e]

    [(Let x rhs body)
     (Let x (shrink-exp rhs)
          (shrink-exp body))]

    [(If c t f)
     (If (shrink-exp c)
         (shrink-exp t)
         (shrink-exp f))]

    [(WhileLoop c body)
     (WhileLoop (shrink-exp c)
                (shrink-exp body))]

    [(SetBang x e1)
     (SetBang x (shrink-exp e1))]

    ;; AND → desugar
    [(Prim 'and (list e1 e2))
     (If (shrink-exp e1)
         (If (shrink-exp e2)
             (Bool #t)
             (Bool #f))
         (Bool #f))]

    ;; OR → desugar
    [(Prim 'or (list e1 e2))
     (If (shrink-exp e1)
         (Bool #t)
         (If (shrink-exp e2)
             (Bool #t)
             (Bool #f)))]

    ;; FIX: handle malformed let coming as Apply
    [(Apply (Var 'let) (cons binding body-exprs))
 (match binding
   ;; FIX: handle nested Apply
   [(Apply (Apply (Var x) (list rhs)) '())
    (Let x (shrink-exp rhs)
         (if (= (length body-exprs) 1)
             (shrink-exp (car body-exprs))
             (Begin
               (map shrink-exp (take body-exprs (- (length body-exprs) 1)))
               (shrink-exp (last body-exprs)))))]
   [_ (error "Malformed let binding" e)])]

    [(Begin es body)
 (Begin (map shrink-exp es)
        (shrink-exp body))]

    [(HasType e t)
     (HasType (shrink-exp e) t)]

    [(Void) (Void)]

    [(Allocate n t) (Allocate n t)]

    [(GlobalValue x) (GlobalValue x)]

    [(Collect n) (Collect n)]

    [(Prim op es)
     (Prim op (map shrink-exp es))]))
(define (shrink p)
  (match p
    [(Program info e)
     (Program info (shrink-exp e))]))
;; Next we have the partial evaluation pass described in the book.
(define (pe-neg r)
  (match r
    [(Int n) (Int (fx- 0 n))]
    [else (Prim '- (list r))]))

(define (pe-add r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Int (fx+ n1 n2))]
    [(_ _) (Prim '+ (list r1 r2))]))

(define (pe-exp e)
  (match e
    [(Int n) (Int n)]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (pe-neg (pe-exp e1))]
    [(Prim '+ (list e1 e2)) (pe-add (pe-exp e1) (pe-exp e2))]
    [(Prim '- (list e1 e2)) (pe-add (pe-exp e1) (pe-neg (pe-exp e2)))]
    ))

(define (pe-Lint p)
  (match p
    [(Program info e) (Program info (pe-exp e))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HW1 Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x)
       (Var (dict-ref env x))]

      [(Int n)
       (Int n)]

      [(Bool b)
       (Bool b)]

      [(If c t f)
       (If ((uniquify-exp env) c)
           ((uniquify-exp env) t)
           ((uniquify-exp env) f))]

      [(WhileLoop c body)
       (WhileLoop ((uniquify-exp env) c)
                  ((uniquify-exp env) body))]

      ;;
      [(Begin es body)
       (Begin
        (for/list ([e es])
          ((uniquify-exp env) e))
        ((uniquify-exp env) body))]

      ;;
      [(SetBang x e1)
       (SetBang (dict-ref env x)
                ((uniquify-exp env) e1))]

      [(Let x e body)
       (let* ([x1 (gensym x)]
              [e1 ((uniquify-exp env) e)]
              [env1 (dict-set env x x1)]
              [body1 ((uniquify-exp env1) body)])
         (Let x1 e1 body1))]

      [(HasType e t)
       (HasType ((uniquify-exp env) e) t)]

      [(Void) (Void)]

      [(Allocate n t) (Allocate n t)]

      [(GlobalValue x) (GlobalValue x)]

      [(Collect n) (Collect n)]

      [(Prim op es)
       (Prim op
             (for/list ([e es])
               ((uniquify-exp env) e)))])))

;; uniquify : Lvar -> Lvar
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]))

(define (atomic? e)
  (match e
    [(Int _) #t]
    [(Var _) #t]
    [else #f]))

(define (rco-atom e)
  (define e1 (rco-exp e))
  (if (atomic? e1)
      (values e1 '())
      (let ([t (gensym 'tmp)])
        (values (Var t)
                (list (cons t e1))))))


(define (rco-args es)
  (match es
    ['() (values '() '())]
    [(cons e rest)
     (define-values (a1 b1) (rco-atom e))
     (define-values (a2 b2) (rco-args rest))
     (values (cons a1 a2)
             (append b1 b2))]))

(define (rco-exp e)
  (match e
    [(Int n) (Int n)]
    [(Bool b) (Bool b)]          ;; ← ADD
    [(Var x) (Var x)]

    [(If c t f)                  ;; ← ADD
     (If (rco-exp c) (rco-exp t) (rco-exp f))]

    [(Begin es body)             ;; ← ADD
     (Begin (map rco-exp es) (rco-exp body))]

    [(SetBang x e1)              ;; ← ADD
     (SetBang x (rco-exp e1))]

    [(WhileLoop c body)
     (WhileLoop (rco-exp c) (rco-exp body))]

    [(Let x rhs body)
     (Let x (rco-exp rhs) (rco-exp body))]

    [(HasType e t)
     (HasType (rco-exp e) t)]

    [(Void) (Void)]

    [(Allocate n t) (Allocate n t)]

    [(GlobalValue x) (GlobalValue x)]

    [(Collect n) (Collect n)]

    [(Prim 'vector-ref (list e (Int i)))
     (define-values (a binds) (rco-atom e))
     (make-lets binds (Prim 'vector-ref (list a (Int i))))]

    [(Prim 'vector-set! (list e (Int i) val))
     (define-values (a1 b1) (rco-atom e))
     (define-values (a2 b2) (rco-atom val))
     (make-lets (append b1 b2)
                (Prim 'vector-set! (list a1 (Int i) a2)))]

    [(Prim op es)
     (define-values (atoms binds) (rco-args es))
     (make-lets binds (Prim op atoms))]))


(define (expose-alloc-exp e)
  (match e
    [(Int n) (Int n)]
    [(Bool b) (Bool b)]
    [(Var x) (Var x)]
    [(Void) (Void)]
    [(Allocate n t) (Allocate n t)]
    [(GlobalValue x) (GlobalValue x)]
    [(Collect n) (Collect n)]

    [(HasType (Prim 'vector es) t)
     (define n (length es))
     (define bytes (* 8 (+ n 1)))
     (define tmp (gensym 'vec))
     (define es^ (map expose-alloc-exp es))
     (Let tmp
       (Begin
         (list (If (Prim '<
                     (list (Prim '+ (list (GlobalValue 'free_ptr) (Int bytes)))
                           (GlobalValue 'fromspace_end)))
                   (Void)
                   (Collect bytes)))
         (Allocate n t))
       (Begin
         (for/list ([e es^] [i (in-naturals)])
           (Prim 'vector-set! (list (Var tmp) (Int i) e)))
         (Var tmp)))]

    [(Prim 'vector es)
     (define n (length es))
     (define bytes (* 8 (+ n 1)))
     (define tmp (gensym 'vec))
     (define es^ (map expose-alloc-exp es))
     (define t `(Vector ,@(make-list n 'Integer)))
     (Let tmp
       (Begin
         (list (If (Prim '<
                     (list (Prim '+ (list (GlobalValue 'free_ptr) (Int bytes)))
                           (GlobalValue 'fromspace_end)))
                   (Void)
                   (Collect bytes)))
         (Allocate n t))
       (Begin
         (for/list ([e es^] [i (in-naturals)])
           (Prim 'vector-set! (list (Var tmp) (Int i) e)))
         (Var tmp)))]

    [(HasType e t)
     (HasType (expose-alloc-exp e) t)]

    [(Prim 'vector-ref (list e (Int i)))
     (Prim 'vector-ref (list (expose-alloc-exp e) (Int i)))]

    [(Prim 'vector-set! (list e (Int i) val))
     (Prim 'vector-set! (list (expose-alloc-exp e) (Int i) (expose-alloc-exp val)))]

    [(Let x rhs body)
     (Let x (expose-alloc-exp rhs) (expose-alloc-exp body))]

    [(If c t f)
     (If (expose-alloc-exp c) (expose-alloc-exp t) (expose-alloc-exp f))]

    [(Begin es body)
     (Begin (map expose-alloc-exp es) (expose-alloc-exp body))]

    [(WhileLoop c body)
     (WhileLoop (expose-alloc-exp c) (expose-alloc-exp body))]

    [(SetBang x e)
     (SetBang x (expose-alloc-exp e))]

    [(Prim op es)
     (Prim op (map expose-alloc-exp es))]))

(define (expose-allocation p)
  (match p
    [(Program info e)
     (Program info (expose-alloc-exp e))]))


;; remove-complex-opera* : Lvar -> Lvar^mon
(define (remove-complex-opera* p)
  (match p
    [(Program info e)
     (Program info (rco-exp e))]))


;; explicate-control : Lvar^mon -> Cvar
(define (explicate-control p)
  (match p
    [(Program info e)
     (let ([blocks (make-hash)])
       (define (new-label prefix)
         (gensym prefix))

       (define (emit label tail)
         (hash-set! blocks label tail))

       (define start-label 'start)
       (emit start-label (explicate-tail e emit new-label))

       (CProgram info blocks))]))






(define (explicate-tail e emit new-label)
  (match e
    ;; -----------------------------
    ;; base cases
    ;; -----------------------------
    [(Int n) (Return (Int n))]
    [(Bool b) (Return (Bool b))]
    [(Var x) (Return (Var x))]

    [(Goto l) (Goto l)]

    ;; -----------------------------
    ;; side effects
    ;; -----------------------------
    [(SetBang x e1)
 (Assign (Var x) e1)]  ;; ← just the assignment, no return

    [(Prim 'read '())
     (Return (Prim 'read '()))]

    [(Void)
     (Return (Void))]

    [(Allocate n t)
     (Return (Allocate n t))]

    [(GlobalValue x)
     (Return (GlobalValue x))]

    [(Collect n)
     (Seq (Collect n) (Return (Void)))]

    [(Prim op es)
     (Return (Prim op es))]

    ;; -----------------------------
    ;; IF
    ;; -----------------------------
    [(If c t f)
     (let ([thn (new-label 'then)]
           [els (new-label 'else)])
       (emit thn (explicate-tail t emit new-label))
       (emit els (explicate-tail f emit new-label))
       (explicate-pred c thn els emit new-label))]

    ;; -----------------------------
    ;; WHILE  ✅ CORRECT VERSION
    ;; -----------------------------
    [(WhileLoop c body)
 (let ([loop (new-label 'loop)]
       [body-lbl (new-label 'body)]
       [cont (new-label 'cont)])

   (emit cont (Return (Int 0)))  ;; temporary placeholder

   (emit loop
     (explicate-pred c (Goto body-lbl) (Goto cont) emit new-label))

   (emit body-lbl
     (append-tail
      (explicate-effect body emit new-label)
      (Goto loop)))

   (Goto loop))]

    ;; -----------------------------
    ;; BEGIN  ✅ FIXED
    ;; -----------------------------
    ;; In explicate-tail, Begin case:
[(Begin es body)
 (let ([tail (explicate-tail body emit new-label)])
   (foldr
    (lambda (e acc)
      (match e
        [(WhileLoop c wb)
         ;; create cont that holds the accumulated continuation
         (let ([loop (new-label 'loop)]
               [body-lbl (new-label 'body)]
               [cont (new-label 'cont)])
           (emit cont acc)  ;; ← cont gets the REAL continuation
           (emit loop
             (explicate-pred c (Goto body-lbl) (Goto cont) emit new-label))
           (emit body-lbl
             (append-tail
              (explicate-effect wb emit new-label)
              (Goto loop)))
           (Goto loop))]
        [_ (append-tail (explicate-effect e emit new-label) acc)]))
    tail
    es))]
    ;; -----------------------------
    ;; LET
    ;; -----------------------------
    [(Let x rhs body)
     (explicate-assign x rhs
       (explicate-tail body emit new-label) emit new-label)]))

(define (append-tail t1 t2)
  (match t1
    [(Return v)
     t2]  ;; ← just discard, jump straight to t2

    [(Seq s t)
     (Seq s (append-tail t t2))]

    [(Goto l)
     (Goto l)]

    [(IfStmt c thn els)
     (IfStmt c thn els)]))

(define (explicate-assign x rhs k emit new-label)
  (match rhs
    [(Int n)
     (Seq (Assign (Var x) (Int n)) k)]

    [(Bool b)
     (Seq (Assign (Var x) (Bool b)) k)]

    [(Var y)
     (Seq (Assign (Var x) (Var y)) k)]

    [(SetBang y e1)
     (Seq (Assign (Var y) e1) k)]

    [(Prim 'read '())
     (Seq (Assign (Var x) (Prim 'read '())) k)]

    [(Prim op es)
     (Seq (Assign (Var x) (Prim op es)) k)]

    [(If c t f)
     (explicate-pred c
                     (explicate-assign x t k emit new-label)
                     (explicate-assign x f k emit new-label)
                     emit new-label)]

    [(Allocate n t)
     (Seq (Assign (Var x) (Allocate n t)) k)]

    [(GlobalValue g)
     (Seq (Assign (Var x) (GlobalValue g)) k)]

    [(Void)
     (Seq (Assign (Var x) (Void)) k)]

    [(Prim 'vector-ref (list e (Int i)))
     (Seq (Assign (Var x) (Prim 'vector-ref (list e (Int i)))) k)]

    [(Prim 'vector-set! (list e (Int i) val))
     (Seq (Assign (Var x) (Prim 'vector-set! (list e (Int i) val))) k)]

    [(Begin es body)
     (define final (explicate-assign x body k emit new-label))
     (foldr
      (lambda (e acc)
        (match e
          [(If c t f)
           (let ([thn (new-label 'then)]
                 [els (new-label 'else)])
             (emit thn (append-tail (explicate-effect t emit new-label) acc))
             (emit els (append-tail (explicate-effect f emit new-label) acc))
             (explicate-pred c thn els emit new-label))]
          [_ (append-tail (explicate-effect e emit new-label) acc)]))
      final
      es)]

    [(Let y r b)
     (explicate-assign y r
       (explicate-assign x b k emit new-label)
       emit new-label)]))

(define (explicate-effect e emit new-label)
  (match e
    ;; side effects we care about
    [(SetBang x e1)
     (Seq (Assign (Var x) e1) (Return (Int 0)))]

    ;; while loop as an effect
    [(WhileLoop c body)
     (let ([loop (new-label 'loop)]
           [body-lbl (new-label 'body)]
           [cont (new-label 'cont)])

       (emit loop
         (explicate-pred c (Goto body-lbl) (Goto cont) emit new-label))

       (emit body-lbl
         (append-tail
          (explicate-effect body emit new-label)
          (Goto loop)))

       ;; cont is empty — just falls to whatever comes after
       (emit cont (Return (Int 0)))

       ;; entry point of the while
       (Goto loop))]

    ;; begin as an effect
    [(Begin es body)
     (foldr
      (lambda (e acc)
        (append-tail (explicate-effect e emit new-label) acc))
      (explicate-effect body emit new-label)
      es)]

    [(Collect n)
     (Seq (Collect n) (Return (Void)))]

    [(Prim 'vector-set! (list e (Int i) val))
     (Seq (Assign (Var (gensym 'tmp))
                  (Prim 'vector-set! (list e (Int i) val)))
          (Return (Void)))]

    ;; anything else, just treat as tail (Int, Var, Prim etc)
    [_ (explicate-tail e emit new-label)]))

(define (explicate-pred c thn els emit new-label)
  (match c
    [(Bool #t)
 (match thn
   [(Goto l) (Goto l)]
   [l (Goto l)])]

[(Bool #f)
 (match els
   [(Goto l) (Goto l)]
   [l (Goto l)])]

    [(If c1 t1 f1)
     (explicate-pred c1
                     (explicate-pred t1 thn els emit new-label)
                     (explicate-pred f1 thn els emit new-label)
                     emit new-label)]

    [(Let x rhs body)
     (explicate-assign x rhs
       (explicate-pred body thn els emit new-label)
       emit new-label)]

    [_
     (define thn^ (match thn [(Goto l) (Goto l)] [l (Goto l)]))
     (define els^ (match els [(Goto l) (Goto l)] [l (Goto l)]))
     (IfStmt c thn^ els^)]))

;; select-instructions : Cvar -> x86var
(define (select-instructions p)
  (match p
    [(CProgram info blocks)
     (X86Program info
       (for/hash ([(lbl tail) (in-dict blocks)])
         (values lbl
                 (Block '() (select-tail tail)))))]))


; we are doing 3.2 which is uncover_live
(define (locations-in-arg a)
  (match a
    [(Reg x) (set x)]
    [(Var x) (set x)]
    [(Deref r _) (set r)]
    [_ (set)]))


(define (reads-of-instr i)
  (match i
    [(Instr 'movq (list s d))
     (locations-in-arg s)]

    [(Instr 'addq (list s d))
     (set-union (locations-in-arg s)
                (locations-in-arg d))]

    [(Instr 'subq (list s d))
     (set-union (locations-in-arg s)
                (locations-in-arg d))]

    [(Instr 'negq (list d))
     (locations-in-arg d)]

    ;; ADD THESE:
    [(Instr 'cmpq (list s d))
     (set-union (locations-in-arg s)
                (locations-in-arg d))]

    [(Instr 'pushq (list s))
     (locations-in-arg s)]

    [(Instr 'popq (list d))
     (set)]

    [(Callq _ _)
     (set 'rdi 'rsi 'rdx 'rcx 'r8 'r9)]

    [(Instr 'movq (list (Global _) d))
     (set)]

    [(Instr 'addq (list _ (Global _)))
     (set)]

    [_ (set)]))


(define (writes-of-instr i)
  (match i
    [(Instr 'movq (list s d))
     (locations-in-arg d)]

    [(Instr 'addq (list s d))
     (locations-in-arg d)]

    [(Instr 'subq (list s d))
     (locations-in-arg d)]

    [(Instr 'negq (list d))
     (locations-in-arg d)]

    ;; ADD THESE:
    [(Instr 'cmpq _)
     (set)]   ;; writes flags only, no registers

    [(Instr 'pushq _)
     (set)]

    [(Instr 'popq (list d))
     (locations-in-arg d)]

    [(Callq _ _)
     (set 'rax 'rcx 'rdx 'rsi 'rdi 'r8 'r9 'r10 'r11)]

    [(Instr 'movq (list _ (Global _)))
     (set)]

    [(Instr 'addq (list _ (Global _)))
     (set)]

    [_ (set)]))

(define (compute-live instrs init-live)
  (define (loop rev-instrs live-after acc)
    (match rev-instrs
      ['() acc]
      [(cons i rest)
       (define R (reads-of-instr i))
       (define W (writes-of-instr i))
       (define live-before
         (set-union R
                    (set-subtract live-after W)))
       (loop rest
             live-before
             (cons live-after acc))]))
  (loop (reverse instrs) init-live '()))

; this is for uncover_live rn
(define (block-successors lbl block blocks)
  (match block
    [(Block _ instrs)
     (for/fold ([succs (set)])
               ([i instrs])
       (match i
         [(Jmp l)    (set-union succs (set l))]
         [(JmpIf _ l) (set-union succs (set l))]
         [_ succs]))]))

(define (block-reads instrs)
  (apply set-union (map reads-of-instr instrs)))

(define (block-writes instrs)
  (apply set-union (map writes-of-instr instrs)))


(define (compute-block-liveness blocks)
  (define live-in (make-hash))
  (define live-out (make-hash))

  ;; initialize
  (for ([(lbl _) (in-dict blocks)])
    (hash-set! live-in lbl (set))
    (hash-set! live-out lbl (set)))

  (define changed #t)

  (let loop ()
    (when changed
      (set! changed #f)

      (for ([(lbl block) (in-dict blocks)])
        (match block
          [(Block _ instrs)

           ;; successors
           (define succs (block-successors lbl block blocks))

           ;; live-out = union of successors' live-in
           (define new-out
             (for/fold ([acc (set)])
                       ([s (in-set succs)])
               (set-union acc (hash-ref live-in s (set)))))

           ;; live-in = R ∪ (live-out - W)
           (define R (block-reads instrs))
           (define W (block-writes instrs))
           (define new-in
             (set-union R
                        (set-subtract new-out W)))

           ;; check changes
           (unless (equal? new-out (hash-ref live-out lbl))
             (hash-set! live-out lbl new-out)
             (set! changed #t))

           (unless (equal? new-in (hash-ref live-in lbl))
             (hash-set! live-in lbl new-in)
             (set! changed #t))]))

      ;; only recurse if changed
      (loop)))

  (values live-in live-out))




(define (uncover_live p)
  (match p
    [(X86Program info blocks)

     (define-values (live-in live-out)
       (compute-block-liveness blocks))

     (define new-blocks
       (for/hash ([(lbl block) (in-dict blocks)])
         (match block
           [(Block _ instrs)
            (define init-live (hash-ref live-out lbl (set)))
            (define lives (compute-live instrs init-live))

            

            (values lbl
                    (Block `(lives ,lives) instrs))])))

     (X86Program info new-blocks)]))



(define (build_interference p)
  (match p
    [(X86Program info blocks)
     (define g (undirected-graph '()))

     ;; First add all vertices
(for ([(lbl block) (in-dict blocks)])
  (match block
    [(Block `(lives ,live-list) instrs)
     ;; from live sets
     (for ([live live-list])
       (for ([v (in-set live)])
         (when (is-var? v)
           (add-vertex! g v))))
     ;; from write sets - catch variables written but never live
     (for ([i instrs])
       (for ([v (in-set (writes-of-instr i))])
         (when (is-var? v)
           (add-vertex! g v))))]))


     ;; Now add edges
     (for ([(lbl block) (in-dict blocks)])
       (match block
         [(Block `(lives ,live-list) instrs)
          (for ([i instrs]
                [live-after live-list])
            (define W (writes-of-instr i))
            (define R (reads-of-instr i))

            (for ([w (in-set W)])
              (when (is-var? w)
                (define neighbors
                  (match i
                    [(Instr 'movq (list s d))
                     (set-subtract live-after (locations-in-arg s))]
                    [_ live-after]))

                (for ([v (in-set neighbors)])
                  (when (and (is-var? v)
                             (not (equal? v w)))
                    (add-edge! g w v))))))]))

     ;; Store graph in info field
     (X86Program (dict-set info 'conflicts g)
                 blocks)]))

(define allocatable-registers
  '(rbx rcx rdx rsi rdi r8 r9 r10 r11))

(define (color-graph g)
  (define color-env (make-hash))
  (define spills '())

  (for ([v (in-vertices g)])
    (define neighbor-regs
      (for/set ([n (in-neighbors g v)]
                #:when (hash-has-key? color-env n))
        (hash-ref color-env n)))

    (define chosen
      (for/first ([r allocatable-registers]
                  #:unless (set-member? neighbor-regs r))
        r))

    (if chosen
        (hash-set! color-env v chosen)
        (set! spills (cons v spills))))

  (values color-env spills))


(define (assign-spills spills)
  (for/fold ([env (hash)] [offset -8])
            ([v spills])
    (values (hash-set env v offset)
            (- offset 8))))

(define (replace-arg a reg-env spill-env)
  (match a
    [(Reg x)
     (cond
       [(hash-has-key? reg-env x)
        (Reg (hash-ref reg-env x))]
       [(hash-has-key? spill-env x)
        (Deref 'rbp (hash-ref spill-env x))]
       [else (Reg x)])]   ;; keep as register if already physical

    [(Var x)
     (cond
       [(hash-has-key? reg-env x)
        (Reg (hash-ref reg-env x))]
       [(hash-has-key? spill-env x)
        (Deref 'rbp (hash-ref spill-env x))]
       [else (error "unallocated var" x)])]

    [(Deref x offset)
     (cond
       [(hash-has-key? reg-env x)
        (Deref (hash-ref reg-env x) offset)]
       [(hash-has-key? spill-env x)
        (Deref 'rbp (hash-ref spill-env x))]
       [else (Deref x offset)])]

    [_ a]))


(define (replace-instr i reg-env spill-env)
  (match i
    [(Instr op args)
     (Instr op
            (map (λ (a)
                   (replace-arg a reg-env spill-env))
                 args))]
    [_ i]))



(define (allocate_registers p)
  (match p
    [(X86Program info blocks)

     (define g (dict-ref info 'conflicts))

     (define-values (reg-env spills)
       (color-graph g))

     (define-values (spill-env _)
       (assign-spills spills))

     (define new-blocks
       (for/hash ([(lbl block) (in-dict blocks)])
         (match block
           [(Block info2 instrs)
            (values lbl
                    (Block info2
                           (map (λ (i)
                                  (replace-instr i reg-env spill-env))
                                instrs)))])))

     (X86Program
      (dict-set info 'num-spills (length spills))
      new-blocks)]))




;;end

(define (select-tail t)
  (match t
    [(Return e)
     (append (select-exp e 'rax)
             (list (Jmp 'conclusion)))]  ;; ← ADD THIS

    [(Seq s t2)
     (append (select-stmt s)
             (select-tail t2))]

    [(IfStmt c thn els)
     (match* (thn els)
       [((Goto l1) (Goto l2))
        (select-pred c l1 l2)])]

    [(Goto l)
     (list (Jmp l))]))


(define (select-pred c thn els)
  (match c
    [(Bool #t)
     (list (Jmp thn))]

    [(Bool #f)
     (list (Jmp els))]

    [(Prim 'eq? (list a b))
     (append (select-exp a 'rax)
             (select-exp b 'r11)
             (list
              (Instr 'cmpq (list (Reg 'r11) (Reg 'rax)))
              (JmpIf 'e thn)
              (Jmp els)))]

    ;;
    [(Prim '< (list a b))
     (append (select-exp a 'rax)
             (select-exp b 'r11)
             (list
              (Instr 'cmpq (list (Reg 'r11) (Reg 'rax)))
              (JmpIf 'l thn)
              (Jmp els)))]

    [_  ;; fallback
     (append (select-exp c 'rax)
             (list
              (Instr 'cmpq (list (Imm 0) (Reg 'rax)))
              (JmpIf 'ne thn)
              (Jmp els)))]))
(define (select-stmt s)
  (match s
    ;; vector-set! must come BEFORE general Assign case
    [(Assign (Var _) (Prim 'vector-set! (list (Var v) (Int i) val)))
     (append
      (select-exp val 'r11)
      (list
       (Instr 'movq (list (Reg 'r11) (Deref v (* 8 (+ i 1)))))))]

    [(Assign (Var x) e)
     (select-exp e x)]

    [(Collect n)
     (list
      (Instr 'movq (list (Reg 'r15) (Reg 'rdi)))
      (Instr 'movq (list (Imm n) (Reg 'rsi)))
      (Callq 'collect 2))]))






(define scratch 'r10)

(define (compute-tag type len)
  (define pointer-bits
    (match type
      [`(Vector ,ts ...)
       (for/fold ([mask 0]) ([t ts] [i (in-naturals)])
         (if (equal? t 'Integer)
             mask
             (bitwise-ior mask (arithmetic-shift 1 i))))]
      [_ 0]))
  (bitwise-ior
   (arithmetic-shift pointer-bits 7)
   (arithmetic-shift len 1)
   1))

(define (select-exp e dst)
  (match e
    [(Int n)
     (list (Instr 'movq (list (Imm n) (Reg dst))))]

    [(Var x)
 (list (Instr 'movq (list (Reg x) (Reg dst))))]

    [(Bool #t)
     (list (Instr 'movq (list (Imm 1) (Reg dst))))]

    [(Bool #f)
     (list (Instr 'movq (list (Imm 0) (Reg dst))))]

    ;; addition
    [(Prim '+ (list a b))
     (if (eq? dst 'rax)
         ;; dst = rax → use scratch as temp register
         (append (select-exp b scratch)
                 (select-exp a 'rax)
                 (list (Instr 'addq (list (Reg scratch) (Reg 'rax)))))
         ;; dst ≠ rax → rax is the safe temp
         (append (select-exp b 'rax)
                 (select-exp a dst)
                 (list (Instr 'addq (list (Reg 'rax) (Reg dst))))))]

    ;; unary minus
    [(Prim '- (list a))
     (append (select-exp a dst)
             (list (Instr 'negq (list (Reg dst)))))]
    
    ;; subtraction
    [(Prim '- (list a b))
     (if (eq? dst 'rax)
         ;; dst = rax → use scratch thing as the temoirary register
         (append (select-exp b scratch)
                 (select-exp a 'rax)
                 (list (Instr 'subq (list (Reg scratch) (Reg 'rax)))))
         ;; dst ≠ rax
         (append (select-exp b 'rax)
                 (select-exp a dst)
                 (list (Instr 'subq (list (Reg 'rax) (Reg dst))))))]

    [(Void)
     (list (Instr 'movq (list (Imm 0) (Reg dst))))]

    [(GlobalValue x)
     (list (Instr 'movq (list (Global x) (Reg dst))))]

    [(Allocate n t)
     (define tag (compute-tag t n))
     (list
      (Instr 'movq (list (Global 'free_ptr) (Var dst)))
      (Instr 'addq (list (Imm (* 8 (+ n 1))) (Global 'free_ptr)))
      (Instr 'movq (list (Imm tag) (Deref dst 0))))]

    [(Prim 'vector-ref (list (Var v) (Int i)))
     (list
      (Instr 'movq (list (Reg v) (Reg 'r11)))
      (Instr 'movq (list (Deref 'r11 (* 8 (+ i 1))) (Reg dst))))]

    [(Prim 'vector-set! (list (Var v) (Int i) val))
     (append
      (select-exp val 'rax)
      (list
       (Instr 'movq (list (Reg 'rax) (Deref v (* 8 (+ i 1)))))
       (Instr 'movq (list (Imm 0) (Reg dst)))))]

    ;; read
    [(Prim 'read '())
     (list (Callq 'read_int 0)
           (Instr 'movq (list (Reg 'rax) (Reg dst))))]))


;; assign-homes : x86var -> x86var
(define (assign-arg arg env)
  (match arg
    [(Var x)
     (Deref 'rbp (dict-ref env x))]

    [(Reg x)
     (if (is-var? x)
         (Deref 'rbp (dict-ref env x))
         (Reg x))]

    [else arg]))


(define (assign-instr instr env)
  (match instr
    [(Instr op args)
     (Instr op (map (λ (a) (assign-arg a env)) args))]
    [(Callq f n) instr]
    [(Jmp l) instr]
    [(JmpIf cc l) instr]
    [else instr]))

(define (assign-block block env)
  (match block
    [(Block info instrs)
     (Block info
       (map (λ (i) (assign-instr i env)) instrs))]))


(define (collect-vars-in-arg a)
  (match a
    [(Var x) (set x)]
    [(Reg x)
     (if (is-var? x)
         (set x)
         (set))]
    [else (set)]))

(define (collect-vars-in-instr i)
  (match i
    [(Instr _ args)
     (apply set-union (map collect-vars-in-arg args))]
    [else (set)]))


(define (collect-vars instrs)
  (apply set-union (map collect-vars-in-instr instrs)))


(define (make-home-env vars)
  (for/fold ([env (hash)] [offset -8])
            ([v (in-set vars)])
    (values (hash-set env v offset)
            (- offset 8))))


(define (assign-homes p)
  (match p
    [(X86Program info blocks)
     (define all-instrs
       (apply append
              (for/list ([b (in-dict-values blocks)])
                (match b [(Block _ is) is]))))

     (define vars (collect-vars all-instrs))

     (define-values (env _) (make-home-env vars))

     (X86Program info
       (for/hash ([(lbl block) (in-dict blocks)])
         (values lbl (assign-block block env))))]))





;; patch-instructions : x86var -> x86int
(define (patch-instr i)
  (match i
    [(Instr 'movq (list s d))
     #:when (equal? s d)
     '()]

    [(Instr 'movq (list s d))
     (if (and (mem? s) (mem? d))
         (list (Instr 'movq (list s patch-scratch))
               (Instr 'movq (list patch-scratch d)))
         (list i))]

    [(Instr op (list s d))
     #:when (member op '(addq subq))
     (if (and (mem? s) (mem? d))
         (list (Instr 'movq (list s patch-scratch))
               (Instr op (list patch-scratch d)))
         (list i))]

    ;; ADD THIS:
    [(Instr 'cmpq (list s d))
     (if (and (mem? s) (mem? d))
         (list (Instr 'movq (list s patch-scratch))
               (Instr 'cmpq (list patch-scratch d)))
         (list i))]

    [else (list i)]))


(define (mem? a)
  (match a
    [(Deref _ _) #t]
    [else #f]))

(define patch-scratch (Reg 'r11))


(define (patch-block block)
  (match block
    [(Block info instrs)
     (Block info (apply append (map patch-instr instrs)))]))


(define (patch-instructions p)
  (match p
    [(X86Program info blocks)
     (X86Program info
       (for/hash ([(lbl block) (in-dict blocks)])
         (values lbl (patch-block block))))]))

;; prelude-and-conclusion : x86int -> x86int
(define (stack-size blocks)
  (define offsets
    (for*/list ([block (in-dict-values blocks)]
                [instr (match block [(Block _ is) is])]
                [arg (match instr [(Instr _ args) args] [_ '()])]
                [n (match arg [(Deref 'rbp n) (list n)] [_ '()])]
                #:when (< n 0))
      (- n)))
  (if (null? offsets) 0 (apply max offsets)))



;(define (prologue size)
;  (list
;    (Instr 'movq (list (Reg 'rsp) (Reg 'rbp)))
;    (Instr 'subq (list (Imm size) (Reg 'rsp)))))
;
;(define (epilogue size)
;  (list
;    (Instr 'addq (list (Imm size) (Reg 'rsp)))
;    (Instr 'retq '())))

(define (prologue size)
  (append
    (list
      (Instr 'pushq (list (Reg 'rbp)))
      (Instr 'movq (list (Reg 'rsp) (Reg 'rbp))))
    (if (> size 0)
        (list (Instr 'subq (list (Imm size) (Reg 'rsp))))
        '())
    (list
      ;; initialize root stack pointer r15
      (Instr 'movq (list (Global 'rootstack_begin) (Reg 'r15)))
      ;; call initialize(rootstack_size, heap_size)
      (Instr 'movq (list (Imm 65536) (Reg 'rdi)))
      (Instr 'movq (list (Imm 65536) (Reg 'rsi)))
      (Callq 'initialize 2))))

(define (epilogue size)
  (append
    (if (> size 0)
        (list (Instr 'addq (list (Imm size) (Reg 'rsp))))
        '())
    (list
      (Instr 'popq (list (Reg 'rbp)))
      (Retq))))



;(define (prelude-and-conclusion p)
;  (match p
;    [(X86Program info blocks)
;     ;; Do NOTHING except ensure retq is present
;     (X86Program info blocks)]))

(define (prelude-and-conclusion p)
  (match p
    [(X86Program info blocks)
     (define size (stack-size blocks))

     (define conclusion-block
       (Block '() (epilogue size)))

     (define new-blocks
       (for/hash ([(lbl block) (in-dict blocks)])
         (match block
           [(Block info2 instrs)
            (if (eq? lbl 'start)
                (values 'main
                  (Block info2
                    (append (prologue size) instrs)))
                (values lbl block))])))

     (X86Program
       (cons (Global 'main) info)
       (hash-set new-blocks 'conclusion conclusion-block))]))

(define (replace-ret-with-jmp instrs conclusion-lbl)
  (apply append
    (map (λ (i)
           (match i
             [(Retq) (list (Jmp conclusion-lbl))]
             [_ (list i)]))
         instrs)))


(define (remove-ret instrs)
  (filter
    (λ (i)
      (not (match i
             [(Retq) #t]
             [_ #f])))
    instrs))




;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `(
    ("shrink" ,shrink ,interp-Lvec ,type-check-Lvec)
    ("uniquify" ,uniquify ,interp-Lvec ,type-check-Lvec)
    ("expose_allocation" ,expose-allocation ,interp-Lvec #f)
    ("remove_complex_opera*" ,remove-complex-opera* ,interp-Lvec #f)
    ("explicate_control" ,explicate-control ,interp-Cvec #f)
    ("select_instructions" ,select-instructions ,interp-pseudo-x86-1)
    ("uncover_live" ,uncover_live ,interp-pseudo-x86-1)
    ("build_interference" ,build_interference ,interp-pseudo-x86-1)
    ("allocate_registers" ,allocate_registers ,interp-pseudo-x86-1)
    ("patch_instructions" ,patch-instructions ,interp-x86-1)
    ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-1)
  ))
