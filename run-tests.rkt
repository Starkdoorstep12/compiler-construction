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
(require "interp-Lfun.rkt")
(require "type-check-Lfun.rkt")
(require "interp-Cfun.rkt")
(require "type-check-Cfun.rkt")
(require (except-in "compiler.rkt" arg-registers)) ;; TEMP

;; =========================
;; HELPERS
;; =========================

(define tests-dir (build-path (current-directory) "tests"))

(define (basename-no-ext p)
  (car (string-split (path->string p) ".")))

(define (tests-for-rkt prefix)
  (map (lambda (p)
         (caddr (string-split (basename-no-ext p) "_")))
       (filter
        (lambda (p)
          (and (string-suffix? (path->string p) ".rkt")
               (string=? prefix
                         (car (string-split (basename-no-ext p) "_")))))
        (directory-list tests-dir))))

(define (tests-for-tyerr prefix)
  (map (lambda (p)
         (caddr (string-split (basename-no-ext p) "_")))
       (filter
        (lambda (p)
          (and (string-suffix? (path->string p) ".tyerr")
               (string=? prefix
                         (car (string-split (basename-no-ext p) "_")))))
        (directory-list tests-dir))))

;; =========================
;; STANDARD TESTS
;; =========================

(compiler-tests "lif" #f compiler-passes "lif_test" (tests-for-rkt "lif"))
(compiler-tests "lwhile" #f compiler-passes "lwhile_test" (tests-for-rkt "lwhile"))
(compiler-tests "vectors" #f compiler-passes "vectors_test" (tests-for-rkt "vectors"))

;; =========================
;; LFUN VALID TESTS
;; =========================

(compiler-tests
 "lfun"
 #f
 compiler-passes
 "functions_test"
 (remove "2" (tests-for-rkt "functions")))
;; =========================
;; LFUN TYPE-ERROR TESTS
;; =========================

(for ([i (tests-for-tyerr "functions")])
  (printf "Expecting type error for functions_test_~a.tyerr\n" i)
  (with-handlers ([exn:fail?
                   (lambda (e)
                     (displayln "✔ correctly failed"))])
    (begin
      (define filename
        (build-path tests-dir
                    (string-append "functions_test_" i ".tyerr")))
      (define program (read-program filename))
      (type-check-Lfun program)
      (displayln "✘ ERROR: should have failed"))))