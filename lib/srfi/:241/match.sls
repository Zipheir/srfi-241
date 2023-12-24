#!r6rs

;; Copyright (C) Marc Nieper-Wißkirchen (2022).  All Rights Reserved.
;; Copyright (C) Wolfgang Corcoran-Mathe (2023)

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

(library (srfi :241 match)
  (export match
          unquote ... -> guard)
  (import (rnrs (6))
          (srfi :39 parameters)
          (srfi :241 match helpers)
          (srfi :241 match quasiquote-transformer))

  (define-syntax ->
    (lambda (form)
      (syntax-violation '-> "invalid use of auxiliary syntax" form)))

  ;;; Split the (im)proper list obj into a head and tail, where the
  ;;; tail is of cons-length k. Pass these values to succ, or call
  ;;; fail with no arguments if k is out of range.
  (define (split-right/continuations obj k succ fail)
    (let ([n (length+ obj)])
      (if (and n (<= k n))
          (call-with-values
              (lambda ()
                (split-at obj (- n k)))
            succ)
          (fail))))

  (define-syntax match
    (lambda (form)
      (define who 'match)

      ;; Holds the identifier denoting the matcher's main loop.
      ;; Used by anonymous cata matchers.
      (define match-loop-id (make-parameter #f))

      ;; Holds the identifier denoting the failure continuation for
      ;; each match clause.
      (define fail-clause (make-parameter #f))

      (define (invoke success) (success))

      (define-record-type pattern-variable
        (nongenerative) (sealed #t) (opaque #t)
        (fields identifier  ; Name
                expression  ; Bound expression
                level))     ; Variable level

      (define-record-type cata-binding
        (nongenerative) (sealed #t) (opaque #t)
        (fields procedure-expression ; Catamorphism operator
                value-identifiers    ; Identifiers binding cata values
                meta-identifier))    ; Name of meta pattern-variable

      (define (identifier-hash id)
        (assert (identifier? id))
        (symbol-hash (syntax->datum id)))

      (define (make-identifier-hashtable)
        (make-hashtable identifier-hash bound-identifier=?))

      (define (repeated-pvar-error id)
        (syntax-violation who
                          "repeated pattern variable in match clause"
                          form
                          id))

      ;;; Check a list of pattern-variables for duplicates.
      (define (check-pattern-variables variables)
        (define id-table (make-identifier-hashtable))

        (define (mark id)
          (lambda (x)
            (when x (repeated-pvar-error id))
            #t))

        (for-each
         (lambda (v)
           (let ([id (pattern-variable-identifier v)])
             (hashtable-update! id-table id (mark id) #f)))
         variables))

      (define (repeated-cata-var-error id)
        (syntax-violation who
                          "repeated cata variable in match clause"
                          form
                          id))

      ;;; Check a list of cata-variables for duplicates. Only
      ;;; cata value-ids are checked.
      (define (check-cata-bindings catas)
        (define id-table (make-identifier-hashtable))

        (define (mark id)
          (lambda (x)
            (when x (repeated-cata-var-error id))
            #t))

        (for-each
         (lambda (cata)
           (for-each
            (lambda (id)
              (hashtable-update! id-table id (mark id) #f))
            (cata-binding-value-identifiers cata)))
         catas))

      ;;; Parse a match clause and return the pattern, guard, and
      ;;; body as multiple values.
      (define (parse-clause clause)
        (syntax-case clause (guard)
          [(pattern (guard guard1 ...) body1 body2 ...)
           (values #'pattern #'(and guard1 ...) #'(body1 body2 ...))]
          [(pattern body1 body2 ...)
           (values #'pattern #'#t #'(body1 body2 ...))]
          [_
           (syntax-violation who
                             "ill-formed match clause"
                             form
                             clause)]))

      (define (ill-formed-match-pattern-violation pattern)
        (syntax-violation who
                          "ill-formed match pattern"
                          form
                          pattern))

      (define (generate-matcher expression pattern)
        (syntax-case pattern (-> unquote)
          [,[cata-operator -> y ...]           ; Named cata-pattern
           (for-all identifier? #'(y ...))
           (generate-cata-matcher #'cata-operator expression #'(y ...))]
          [,[y ...]                ; Anonymous cata-pattern
           (for-all identifier? #'(y ...))
           (generate-cata-matcher (match-loop-id) expression #'(y ...))]
          ;; Match this explicitly to avoid matching 'unquote' in a
          ;; tail pattern.
          [(head ellipsis body ... . ,x)
           (and (ellipsis? #'ellipsis) (identifier? #'x))
           (generate-ellipsis-matcher expression
                                      #'head
                                      #'(body ...)
                                      #',x)]
          [(head ellipsis body ... . tail)
           (ellipsis? #'ellipsis)
           (generate-ellipsis-matcher expression
                                      #'head
                                      #'(body ...)
                                      #'tail)]
          [,u (underscore? #'u)      ; underscore is wild
           (values invoke '() '())]  ; no bindings
          [,x
           (identifier? #'x)
           (generate-variable-matcher expression #'x)]
          [(car-pattern . cdr-pattern)
           (generate-pair-matcher expression
                                  #'car-pattern
                                  #'cdr-pattern)]
          [unquote
           (ill-formed-match-pattern-violation pattern)]
          [_ (generate-constant-matcher expression pattern)]))

      (define (generate-cata-matcher operator expression ids)
        (with-syntax ([(x) (generate-temporaries '(x))])
          (values
           invoke
           (list (make-pattern-variable #'x expression 0))
           (list (make-cata-binding operator ids #'x)))))

      ;;; Match expr by binding a pattern variable named *id* to it.
      (define (generate-variable-matcher expression id)
        (values
         invoke
         (list (make-pattern-variable id expression 0))
         '()))

      ;;; Match expr against the constant object.
      (define (generate-constant-matcher expression object)
        (values
         (lambda (succeed)
           #`(if (equal? #,expression '#,object)
                 #,(succeed)
                 (#,(fail-clause))))
         '()
         '()))

      ;;; Match the head of expr with car-pat and its tail with
      ;;; cdr-pat.
      (define (generate-pair-matcher expr car-pattern cdr-pattern)
        (with-syntax ([(e1 e2) (generate-temporaries '(e1 e2))])
          (let*-values ([(mat1 pvars1 catas1)
                         (generate-matcher #'e1 car-pattern)]
                        [(mat2 pvars2 catas2)
                         (generate-matcher #'e2 cdr-pattern)])
            (values
             (lambda (succeed)
               #`(if (pair? #,expr)
                     (let ([e1 (car #,expr)]
                           [e2 (cdr #,expr)])
                       #,(mat1 (lambda () (mat2 succeed))))
                     (#,(fail-clause))))
             (append pvars1 pvars2) (append catas1 catas2)))))

      (define (generate-ellipsis-matcher expression
                                         head-pattern
                                         body-patterns
                                         tail-pattern)
        (with-syntax ([(e1 e2) (generate-temporaries '(e1 e2))])
          (let*-values ([(mat1 pvars1 catas1)
                         (generate-map #'e1 head-pattern)]
                        [(rest-patterns)
                         (append body-patterns tail-pattern)]
                        [(mat2 pvars2 catas2)
                         (generate-list-matcher #'e2 rest-patterns)])
            (values
             (lambda (succeed)
               #`(split-right/continuations
                  #,expression
                  #,(length body-patterns)
                  (lambda (e1 e2)
                    #,(mat1 (lambda () (mat2 succeed))))
                  #,(fail-clause)))
             (append pvars1 pvars2)
             (append catas1 catas2)))))

      ;;; Match the empty list.
      (define (generate-null-matcher expression)
        (values (lambda (succeed)
                  #`(if (null? #,expression)
                        #,(succeed)
                        (#,(fail-clause))))
                '()
                '()))

      ;;; Match expression recursively against patterns.
      (define (generate-list-matcher expression patterns)
        (syntax-case patterns (unquote)
          [() (generate-null-matcher expression)]
          [,x (generate-matcher expression patterns)]
          [(pat . rest-patterns)
           (with-syntax ([(e1 e2) (generate-temporaries '(e1 e2))])
             (let*-values ([(mat1 pvars1 catas1)
                            (generate-matcher #'e1 #'pat)]
                           [(mat2 pvars2 catas2)
                            (generate-list-matcher #'e2  ; recur
                                                   #'rest-patterns)])
               (values
                (lambda (succeed)
                  #`(let ([e1 (car #,expression)]
                          [e2 (cdr #,expression)])
                      #,(mat1
                         (lambda ()
                           (mat2 succeed)))))
                (append pvars1 pvars2)
                (append catas1 catas2))))]
          [_ (generate-matcher expression patterns)]))

      (define (generate-map expression pattern)
        (with-syntax ([(e1 e2 f) (generate-temporaries '(e1 e2 f))])
          (let-values ([(mat ipvars catas)
                        (generate-matcher #'e1 pattern)])
            (with-syntax ([(u ...) (generate-temporaries ipvars)]
                          [(v ...)
                           (map pattern-variable-expression ipvars)])
              (values
               (lambda (succeed)
                 #`(let f ([e2 (reverse #,expression)]
                           [u '()] ...)
                     (if (null? e2)
                         #,(succeed)
                         (let ([e1 (car e2)])
                           #,(mat (lambda ()
                                    #`(f (cdr e2) (cons v u) ...)))))))
               (make-meta-variables #'(u ...) ipvars)
               catas)))))

      ;;; Build a list of pattern-variables with the same names as
      ;;; the variables, but of higher level. These are bound to the
      ;;; expression-ids.
      (define (make-meta-variables expression-ids variables)
        (map (lambda (id v)
               (make-pattern-variable
                (pattern-variable-identifier v)
                id
                (+ (pattern-variable-level v) 1)))
             expression-ids
             variables))

      (define (generate-map-values operator value-ids binding level)
        (let generate-loop ([level level])
          (if (zero? level)
              #`(#,operator #,binding)
              ;; FIXME: Better names.
              (with-syntax ([(tmps ...)
                             (generate-temporaries value-ids)]
                            [(tmp ...) (generate-temporaries value-ids)]
                            [e binding])
                #`(let loop ([e* (reverse e)]
                             [tmps '()] ...)
                    (if (null? e*)
                        (values tmps ...)
                        (let ([e (car e*)]
                              [e* (cdr e*)])
                          (let-values ([(tmp ...)
                                        #,(generate-loop (- level 1))])
                            (loop e* (cons tmp tmps) ...)))))))))

      (define (generate-clause keyword expression-id clause)
        (let*-values ([(pattern guard-expression body)
                       (parse-clause clause)]
                      [(matcher pvars catas)
                       (generate-matcher expression-id pattern)])
          (check-pattern-variables pvars)
          (check-cata-bindings catas)
          (with-syntax ([quasiquote (datum->syntax keyword 'quasiquote)]
                        [(x ...)
                         (map pattern-variable-identifier pvars)]
                        [(u ...)
                         (map pattern-variable-expression pvars)]
                        [(f ...)
                         (map cata-binding-procedure-expression catas)]
                        [((y ...) ...)
                         (map cata-binding-value-identifiers catas)]
                        [(z ...)
                         (map cata-binding-meta-identifier catas)]
                        [(tmp ...) (generate-temporaries catas)])
            (with-syntax ([(e ...) (make-cata-values pvars
                                                     #'(tmp ...)
                                                     #'((y ...) ...)
                                                     #'(z ...))])
              (matcher
               (lambda ()
                 #`(let ([x u] ...)
                     (if #,guard-expression
                         (let ([tmp f] ...)
                           (let-values ([(y ...) e] ...)
                             (let-syntax ([quasiquote
                                           quasiquote-transformer])
                               #,@body)))
                         (#,(fail-clause))))))))))

      (define (make-cata-values variables
                                temporaries
                                value-ids
                                meta-ids)
        (define (meta-id-level id)
          (exists (lambda (v)
                    (let ([x (pattern-variable-identifier v)])
                      (and (bound-identifier=? x id)
                           (pattern-variable-level v))))
                  variables))

        (map (lambda (t ids b)
               (generate-map-values t ids b (meta-id-level b)))
             temporaries
             value-ids
             meta-ids))

      (define (generate-match keyword expression-id clauses)
        (fold-right
         (lambda (clause rest)
           (with-syntax ([(fail) (generate-temporaries '(fail))])
             (parameterize ([fail-clause #'fail])
               #`(let ([fail (lambda () #,rest)])
                   #,(generate-clause keyword expression-id clause)))))
         #`(assertion-violation 'who
                                "value does not match"
                                #,expression-id)
         clauses))

      ;;; Emit the main pattern-matching loop, then the matcher body.
      ;;;
      ;;; Binds the 'match-loop' & 'expr-val' identifiers which are
      ;;; referenced by generated matchers.
      (syntax-case form ()
        [(match expression clause ...)
         (with-syntax ([(lp ev) (generate-temporaries '(lp ev))])
           (parameterize ([match-loop-id #'lp])
             #`(let lp ([ev expression])
                 #,(generate-match #'match #'ev #'(clause ...)))))])))

  )
