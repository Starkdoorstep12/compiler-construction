#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "interp.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "utilities.rkt")
(provide (all-defined-out))

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

      [(Let x e body)
       (let* ([x1 (gensym x)]
              [e1 ((uniquify-exp env) e)]
              [env1 (dict-set env x x1)]
              [body1 ((uniquify-exp env1) body)])
         (Let x1 e1 body1))]

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
    [(Var x) (Var x)]

    [(Let x rhs body)
     (Let x (rco-exp rhs) (rco-exp body))]

    [(Prim op es)
     (define-values (atoms binds) (rco-args es))
     (make-lets binds (Prim op atoms))]))


;; remove-complex-opera* : Lvar -> Lvar^mon
(define (remove-complex-opera* p)
  (match p
    [(Program info e)
     (Program info (rco-exp e))]))


;; explicate-control : Lvar^mon -> Cvar
(define (explicate-control p)
  (match p
    [(Program info e)
     (CProgram info
               (list (cons 'start (explicate-tail e))))]))






(define (explicate-tail e)
  (match e
    [(Int n)
     (Return (Int n))]

    [(Var x)
     (Return (Var x))]

    [(Prim 'read '())
     (Return (Prim 'read '()))]

    [(Prim op es)
     (Return (Prim op es))]

    [(Let x rhs body)
     (explicate-assign x rhs (explicate-tail body))]))


(define (explicate-assign x rhs k)
  (match rhs
    [(Int n)
     (Seq (Assign (Var x) (Int n)) k)]

    [(Var y)
     (Seq (Assign (Var x) (Var y)) k)]

    [(Prim 'read '())
     (Seq (Assign (Var x) (Prim 'read '())) k)]

    [(Prim op es)
     (Seq (Assign (Var x) (Prim op es)) k)]

    [(Let y r b)
     (explicate-assign y r
       (explicate-assign x b k))]))


;; select-instructions : Cvar -> x86var
(define (select-instructions p)
  (match p
    [(CProgram info blocks)
     (X86Program info
       (for/hash ([(lbl tail) (in-dict blocks)])
         (values lbl
                 (Block '() (select-tail tail)))))]))



(define (select-tail t)
  (match t
    [(Return e)
     (select-exp e 'rax)]

    [(Seq s t2)
     (append (select-stmt s)
             (select-tail t2))]))

(define (select-stmt s)
  (match s
    [(Assign (Var x) e)
     (select-exp e x)]))






(define scratch 'r10)

(define (select-exp e dst)
  (match e
    [(Int n)
     (list (Instr 'movq (list (Imm n) (Reg dst))))]

    [(Var x)
     (list (Instr 'movq (list (Reg x) (Reg dst))))]

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

    ;; read
    [(Prim 'read '())
     (list (Callq 'read_int 0)
           (Instr 'movq (list (Reg 'rax) (Reg dst))))]))


;; assign-homes : x86var -> x86var
(define (assign-arg arg env)
  (match arg
    [(Var x)
     (Deref 'rbp (dict-ref env x))]
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



(define (prologue size)
  (list
    (Instr 'movq (list (Reg 'rsp) (Reg 'rbp)))
    (Instr 'subq (list (Imm size) (Reg 'rsp)))))

(define (epilogue size)
  (list
    (Instr 'addq (list (Imm size) (Reg 'rsp)))
    (Instr 'retq '())))



(define (prelude-and-conclusion p)
  (match p
    [(X86Program info blocks)
     ;; Do NOTHING except ensure retq is present
     (X86Program info blocks)]))





;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `(
     ;; Uncomment the following passes as you finish them.
      ("uniquify" ,uniquify ,interp_Lvar ,type-check-Lvar)
      ("remove complex opera*" ,remove-complex-opera* ,interp_Lvar ,type-check-Lvar)
      ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
      ("instruction selection" ,select-instructions ,interp-pseudo-x86-0)
      ("assign homes" ,assign-homes ,interp-x86-0)
      ("patch instructions" ,patch-instructions ,interp-x86-0)
      ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))
