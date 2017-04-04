#! /usr/bin/env racket
#lang typed/racket


(: baz : (Any -> Any))
(define (baz v)
  (match v
    [`(VARREF ,(? symbol? x)) 'return]
    [`(Lambda ,(app baz fs) ,e ...) 'return]
    [`(CaseLambda ,lc ...) 'return]
    [`(If ,(app baz cond) ,(app baz then) ,(app baz else)) 'return]
    [`(Begin ,e ...) 'return]
    [`(Begin0 ,(app baz e1) ,e ...) 'return]
    [`(LetValues (,lvs ...) ,e ...) 'return]
    [`(LetrecValues (,lvs ...) ,e ...) 'return]
    [`(SetBang ,(? symbol? x) ,(app baz e)) 'return]
    [`(Quote ,(app baz d)) 'return]
    [`(QuoteSyntax ,(app baz d)) 'return]
    [`(WithContMark ,(app baz e1) ,(app baz e2) ,(app baz e3)) 'return]
    [`(App ,e ...) 'return]
    [`(Top ,(? symbol? x)) 'return]
    [`(VariableReference ,(? symbol? x)) 'return]
    [`(VariableReferenceTop ,(? symbol? x)) 'return]
    [`(VariableReference1 ,(? symbol? x)) 'return]
    [`(VariableReferenceTop2 ,(? symbol? x)) 'return]
    ;[`(Quote2 ,(app baz d)) 'return]
    ;[`(QuoteSyntax3 ,(app baz d)) 'return]
    ;[`(VARREF2 ,(? symbol? x)) 'return]
    ;[`(Lambda2 ,(app baz fs) ,e ...) 'return]
    ;[`(CaseLambda2 ,lc ...) 'return]
    ;[`(If2 ,(app baz cond) ,(app baz then) ,(app baz else)) 'return]
    ;[`(Begin2 ,e ...) 'return]
    ;[`(Begin02 ,(app baz e1) ,e ...) 'return]
))
