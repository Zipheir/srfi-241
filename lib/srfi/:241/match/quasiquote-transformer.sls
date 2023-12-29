#!r6rs

;; Copyright (C) Marc Nieper-Wißkirchen (2022).  All Rights Reserved.
;; Copyright (C) Wolfgang Corcoran-Mathe (2023).

;; Permission is hereby granted, free of charge, to any person
;; obtaining a copy of this software and associated documentation
;; files (the "Software"), to deal in the Software without
;; restriction, including without limitation the rights to use, copy,
;; modify, merge, publish, distribute, sublicense, and/or sell copies
;; of the Software, and to permit persons to whom the Software is
;; furnished to do so, subject to the following conditions:

;; The above copyright notice and this permission notice shall be
;; included in all copies or substantial portions of the Software.

;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
;; EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
;; MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
;; NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
;; BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
;; ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
;; CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
;; SOFTWARE.

(library (srfi :241 match quasiquote-transformer)
  (export quasiquote-transformer
          unquote unquote-splicing ...
          append-n-map)
  (import (rnrs (6))
          (srfi :241 match helpers))

  (define (quasiquote-transformer stx)
    (define (never x) #f)

    (define who 'quasiquote)

    (define-record-type template-variable
      (nongenerative) (sealed #t) (opaque #t)
      (fields identifier   ; Name
              expression)) ; Bound expression

    (define (quasiquote-syntax-violation subform msg)
      (syntax-violation 'quasiquote msg stx subform))

    (define (generate-output keyword template level ellipsis?)
      (define (quasiquote? x)
        (and (identifier? x) (free-identifier=? x keyword)))

      (define (generate-ellipsis tmpl* out* vars* depth tmpl2)
        (let loop ([depth depth] [tmpl2 tmpl2])
          (syntax-case tmpl2 ()
            [(ell . tmpl2)
             (ellipsis? #'ell)
             (loop (+ depth 1) #'tmpl2)]
            [tmpl2
             (let-values ([(out2 vars2)
                           (generate-output keyword
                                            #'tmpl2
                                            0
                                            ellipsis?)])
               (for-each
                (lambda (tmpl vars)
                  (when (null? vars)
                    (quasiquote-syntax-violation
                     #'tmpl
                     "no substitutions to repeat here")))
                tmpl* vars*)
               (with-syntax ([((tmp** ...) ...)
                              (map (lambda (vars)
                                     (map template-variable-identifier
                                          vars))
                                   vars*)]
                             [(out1 ...) out*])
                 (values #`(append (append-n-map #,depth
                                                 (lambda (tmp** ...)
                                                   out1)
                                                 tmp** ...)
                                   ...
                                   #,out2)
                         (append (apply append vars*) vars2))))])))

      ;; Make a list of template variables and bind them to
      ;; the *expressions*. Return the variable names and singleton
      ;; lists of the variables as multiple values.
      (define (generate-unquote-list expressions)
        (with-syntax ([(tmps ...) (generate-temporaries expressions)])
          (values #'(tmps ...)
                  (map (lambda (t e)
                         (list (make-template-variable t e)))
                       #'(tmps ...) expressions))))

      ;; Generate code for templates of the form
      ;;   ((unquote . *expressions*) ellipsis . *more-templates*)
      (define (generate-simple-unquote-ellipsis expressions
                                                more-templates)
        (let-values ([(ids vss)
                      (generate-unquote-list expressions)])
          (generate-ellipsis expressions ids vss 0 more-templates)))

      (syntax-case template (unquote unquote-splicing)
        ;; (<ellipsis> <template>). Escape ellipsis in template.
        [(ell tmpl) (ellipsis? #'ell)
         (generate-output keyword #'tmpl level never)]
        ;; (quasiquote <template>)
        [(quasiquote tmpl) (quasiquote? #'quasiquote)
         (generate-nested keyword #'tmpl (+ 1 level) ellipsis?)]
        ;; (unquote <template>)
        [(unquote tmpl)
         (generate-unquote keyword #'tmpl level ellipsis?)]
        ;; ((unquote-splicing <template> ...) <ellipsis> . <template>)
        [((unquote-splicing expr ...) ell . tmpl2)
         (and (zero? level) (ellipsis? #'ell))
         (let-values ([(names varss)
                       (generate-unquote-list #'(expr ...))])
           (generate-ellipsis #'(expr ...) names varss 1 #'tmpl2))]
        ;; (<template> <ellipsis> . <template>)
        [((unquote expr ...) ell . tmpl2)
         (and (zero? level) (ellipsis? #'ell))
         (generate-simple-unquote-ellipsis #'(expr ...) #'tmpl2)]
        [(tmpl1 ell . tmpl2) (and (zero? level) (ellipsis? #'ell))
         (let-values ([(out1 vars1)
                       (generate-output keyword #'tmpl1 0 ellipsis?)])
           (generate-ellipsis #'(tmpl1) (list out1) (list vars1) 0 #'tmpl2))]
        ;; ((unquote <template> ...) . <template>)
        [((unquote tmpl1 ...) . tmpl2)
         (let-values ([(out vars)
                       (generate-output keyword #'tmpl2 level ellipsis?)])
           (if (zero? level)
               (with-syntax ([(tmp ...)
                              (generate-temporaries #'(tmpl1 ...))])
                 (values #`(cons* tmp ... #,out)
                         (append
                          (map make-template-variable #'(tmp ...) #'(tmpl1 ...))
                          vars)))
               (let-values ([(out* vars*)
                             (generate-output* keyword #'(tmpl1 ...) (- level 1) ellipsis?)])
                 (if (and (null? vars)
                          (null? vars*))
                     (values #''((unquote-splicing tmpl1 ...) . tmpl2)
                             '())
                     (values #`(cons (list 'unquote #,@out*) #,out)
                             (append vars* vars))))))]

        ;; ((unquote-splicing <template> ...) . <template>)
        [((unquote-splicing tmpl1 ...) . tmpl2)
         ;; TODO: Use generate-ellipsis.
         (let-values ([(out vars)
                       (generate-output keyword #'tmpl2 level ellipsis?)])
           (if (zero? level)
               (with-syntax ([(tmp ...)
                              (generate-temporaries #'(tmpl1 ...))])
                 (values #`(append tmp ... #,out)
                         (append
                          (map make-template-variable #'(tmp ...) #'(tmpl1 ...))
                          vars)))
               (let-values ([(out* vars*)
                             (generate-output* keyword #'(tmpl1 ...) (- level 1) ellipsis?)])
                 (if (and (null? vars)
                          (null? vars*))
                     (values #''((unquote-splicing tmpl1 ...) . tmpl2)
                             '())
                     (values #`(cons (list 'unquote-splicing #,@out*) #,out)
                             (append vars* vars))))))]
        ;; (<element> . <element>)
        [(el1 . el2)
         (let-values ([(out1 vars1)
                       (generate-output keyword #'el1 level ellipsis?)]
                      [(out2 vars2)
                       (generate-output keyword #'el2 level ellipsis?)])
           (if (and (null? vars1)
                    (null? vars2))
               (values #''(el1 . el2)
                       '())
               (values #`(cons #,out1 #,out2)
                       (append vars1 vars2))))]
        ;; #(<element> ...)
        [#(el ...)
         (let-values ([(out vars)
                       (generate-output keyword #'(el ...) level ellipsis?)])
           (if (null? vars)
               (values #'#(el ...) '())
               (values #`(list->vector #,out) vars)))]
        ;; <constant>
        [constant
         (values #''constant '())]))

      (define (generate-output* keyword template* level ellipsis?)
        (let loop ([tmpl* template*] [out* '()] [vars* '()])
          (if (null? tmpl*)
              (values (reverse out*) vars*)
              (let ([tmpl (car tmpl*)]
                    [tmpl* (cdr tmpl*)])
                (let-values ([(out vars)
                              (generate-output keyword
                                               tmpl
                                               level
                                               ellipsis?)])
                  (loop tmpl* (cons out out*) (append vars vars*)))))))

      (define (generate-nested keyword template level ellipsis?)
        (let-values ([(out vars)
                      (generate-output keyword
                                       template
                                       level
                                       ellipsis?)])
          (if (null? vars)
              (values #`(unquote #,template) '())
              (values #`(list 'quasiquote #,out) vars))))

      (define (generate-unquote keyword template level ellipsis?)
        (if (zero? level)
            (with-syntax ([(t) (generate-temporaries '(t))])
              (values #'t
                      (list (make-template-variable #'t template))))
            (let-values ([(out vs)
                          (generate-output keyword
                                           template
                                           (- level 1)
                                           ellipsis?)])
              (if (null? vs)
                  (values #''(unquote template) '())
                  (values #`(list 'unquote #,out) vs)))))


      (syntax-case stx ()
        [(k tmpl)
         (let-values ([(out vars)
                       (generate-output #'k #'tmpl 0 ellipsis?)])
           (with-syntax ([(x ...)
                          (map template-variable-identifier vars)]
                         [(e ...)
                          (map template-variable-expression vars)])
             #`(let ([x e] ...)
                 #,out)))]
        [_
         (syntax-violation who "invalid syntax" stx)]))

  (define (append-n-map n proc . arg*)
    (let loop ([n n] [arg* arg*])
      (if (zero? n)
          (apply map proc arg*)
          (let ([n (- n 1)])
            (apply append
                   (apply map
                          (lambda arg*
                            (loop n arg*))
                          arg*))))))

  )
