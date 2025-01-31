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

  (define (quasiquote-transformer form)
    (define (never x) #f)

    (define who 'quasiquote)

    (define-record-type template-variable
      (nongenerative) (sealed #t) (opaque #t)
      (fields name   ; Name
              expression)) ; Bound expression

    ;; Make a list of template variables and bind them to
    ;; the *expressions*. Return the variable names & variables
    ;; as multiple values.
    (define (generate-variables expressions)
      (with-syntax ([(tmps ...) (generate-temporaries expressions)])
        (values #'(tmps ...)
                (map make-template-variable
                     #'(tmps ...)
                     expressions))))

    (define (quasiquote-syntax-violation subform msg)
      (syntax-violation 'quasiquote msg form subform))

    (define (generate-output keyword template level ellipsis?)
      (define (quasiquote? x)
        (and (identifier? x) (free-identifier=? x keyword)))

      (define (generate-ellipsis templates
                                 outs
                                 variabless
                                 depth
                                 more-templates)
        (define variable-names
          (map (lambda (vs)
                 (map template-variable-name vs))
               variabless))

        (let loop ([depth depth] [more more-templates])
          (syntax-case more ()
            [(ell . tm) (ellipsis? #'ell)
             (loop (+ depth 1) #'tm)]
            [tm
             (let-values ([(out2 vars2)
                           (generate-output keyword #'tm 0 ellipsis?)])
               (check-bindings templates variabless)
               (with-syntax ([((id ...) ...) variable-names]
                             [(out1 ...) outs])
                 ;; FIXME: Cryptic.
                 (values #`(append (append-n-map #,depth
                                                 (lambda (id ...)
                                                   out1)
                                                 id ...)
                                   ...
                                   #,out2)
                         (append (apply append variabless) vars2))))])))

      ;; Raise an exception for a template with an empty variable list.
      (define (check-bindings templates variabless)
        (for-each (lambda (t vs)
                    (when (null? vs)
                      (quasiquote-syntax-violation
                       t
                       "no substitutions to repeat here")))
                  templates
                  variabless))

      ;; Generate code for templates of the form
      ;;   ((unquote . *expressions*) ellipsis . *more-templates*)
      (define (generate-simple-unquote-ellipsis expressions
                                                more-templates)
        (let*-values ([(ids vs) (generate-variables expressions)]
                      [(vss) (map list vs)])
          (generate-ellipsis expressions ids vss 0 more-templates)))

      ;; Generate code for level-0 templates of the form
      ;;   ((unquote-splicing . *expressions*) ellipsis .
      ;;    *more-templates*)
      (define (generate-simple-splicing-ellipsis expressions
      						 more-templates)
        (let*-values ([(ids vs) (generate-variables expressions)]
                      [(vss) (map list vs)])
          (generate-ellipsis expressions ids vss 1 more-templates)))

      ;; Generate code for level-0 templates of the form
      ;;   ((*template* ellipsis) . *more-templates*)
      (define (generate-simple-ellipsis template more-templates)
        (let-values ([(out vs)
                      (generate-output keyword template 0 ellipsis?)])
          (generate-ellipsis (list template)
                             (list out)
                             (list vs)
                             0
                             more-templates)))

      ;; Generate output for
      ;;
      ;; ((unquote . <unquoted-templates>) . more-templates)
      (define (generate-unquote unquoted-templates more-templates)
        (let-values
         ([(out vars)
           (generate-output keyword more-templates level ellipsis?)])
          (if (zero? level)
              (let*-values ([(ids vs)
                             (generate-variables unquoted-templates)])
                  (values #`(cons* #,@ids #,out)
                          (append vs vars)))
              (let-values
               ([(out* vars*)
                 (generate-list-output keyword
                                       unquoted-templates
                                       (- level 1)
                                       ellipsis?)])
                (if (and (null? vars) (null? vars*))
                    (values
                     #`'((unquote-splicing ,@unquoted-templates) .
                          ,more-templates)
                     '())
                    (values #`(cons (list 'unquote #,@out*) #,out)
                            (append vars* vars)))))))

      ;; Generate output for (template . more-templates).
      (define (generate-pair template more-templates)
        (let-values
         ([(out1 vars1)
           (generate-output keyword template level ellipsis?)]
          [(out2 vars2)
           (generate-output keyword more-templates level ellipsis?)])
          (values #`(cons #,out1 #,out2)
                  (append vars1 vars2))))

      ;; Generate output for #(elements0 ... elementsN).
      (define (generate-vector elements)
        (let-values
         ([(out vs)
           (generate-output keyword elements level ellipsis?)])
          (values #`(list->vector #,out) vs)))

      ;; Body of generate-output.
      (syntax-case template (unquote unquote-splicing)
        [(ell tmpl) (ellipsis? #'ell)
         (generate-output keyword #'tmpl level never)]
        [(quasiquote tmpl) (quasiquote? #'quasiquote)
         (generate-nested keyword #'tmpl (+ 1 level) ellipsis?)]
        [(unquote tmpl)
         (generate-singleton-unquote keyword #'tmpl level ellipsis?)]
        [((unquote-splicing expr ...) ell . tmpl2)
         (and (zero? level) (ellipsis? #'ell))
         (generate-simple-splicing-ellipsis #'(expr ...) #'tmpl2)]
        [((unquote expr ...) ell . tmpl2)
         (and (zero? level) (ellipsis? #'ell))
         (generate-simple-unquote-ellipsis #'(expr ...) #'tmpl2)]
        [((unquote-splicing tmpl1 ...) . tmpl2) (zero? level)
         (generate-simple-unquote-ellipsis #'(tmpl1 ...) #'tmpl2)]
        [(tmpl1 ell . tmpl2) (and (zero? level) (ellipsis? #'ell))
         (generate-simple-ellipsis #'tmpl1 #'tmpl2)]
        [((unquote tmpl1 ...) . tmpl2)
         (generate-unquote #'(tmpl1 ...) #'tmpl2)]
        [(el1 . el2) (generate-pair #'el1 #'el2)]
        [#(el ...) (generate-vector #'(el ...))]
        [constant (values #''constant '())]))

      (define (generate-list-output keyword templates level ellipsis?)
        (fold-right/two-values
         (lambda (outs varss tmpl)
           (let-values ([(o vs)
                         (generate-output keyword tmpl level ellipsis?)])
             (values (cons o outs) (append vs varss))))
         '()
         '()
         templates))

      (define (generate-nested keyword template level ellipsis?)
        (let-values ([(out vars)
                      (generate-output keyword
                                       template
                                       level
                                       ellipsis?)])
          (if (null? vars)
              (values #`(unquote #,template) '())
              (values #`(list 'quasiquote #,out) vars))))

      (define (generate-singleton-unquote keyword
                                          template
                                          level
                                          ellipsis?)
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

      ;; Body of quasiquote-transformer.
      (syntax-case form ()
        [(k tmpl)
         (let-values ([(out vars)
                       (generate-output #'k #'tmpl 0 ellipsis?)])
           (with-syntax ([(x ...) (map template-variable-name vars)]
                         [(e ...)
                          (map template-variable-expression vars)])
             #`(let ([x e] ...)
                 #,out)))]
        [_ (syntax-violation who "invalid syntax" form)]))

  )
