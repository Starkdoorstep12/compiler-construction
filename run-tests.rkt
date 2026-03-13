#! /usr/bin/env racket
#lang racket

(require "utilities.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "interp.rkt")
(require "interp-Lif.rkt")
(require "type-check-Lif.rkt")
(require "interp-Lwhile.rkt")
(require "type-check-Lwhile.rkt")
(require "compiler.rkt")
;(debug-level 1)
;(AST-output-syntax 'concrete-syntax)

;; all the files in the tests/ directory with extension ".rkt".
(define all-tests
  (map (lambda (p) (car (string-split (path->string p) ".")))
       (filter (lambda (p)
                 (string=? (cadr (string-split (path->string p) ".")) "rkt"))
               (directory-list (build-path (current-directory) "tests")))))

(define (tests-for r)
  (map (lambda (p)
         (caddr (string-split p "_")))
       (filter
        (lambda (p)
          (string=? r (car (string-split p "_"))))
        all-tests)))

;; The following tests the intermediate-language outputs of the passes.
;(interp-tests
; "lif"
; type-check-Lif
; compiler-passes
; interp-Lif
; "lif_test"
; (tests-for "lif"))
(interp-tests
 "lif"
 type-check-Lwhile
 compiler-passes
 interp-Lwhile
 "lif_test"
 (tests-for "lif"))
;; Uncomment the following when all the passes are complete to
;; test the final x86 code.
;(compiler-tests "while" #f compiler-passes "while_test" (tests-for "while"))
