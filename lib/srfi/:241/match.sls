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
  ;;; tail is of cons-length k. Pass these values to succeed, or call
  ;;; fail with no arguments if k is out of range.
  (define (split-right/continuations obj k succeed fail)
    (let ([n (length+ obj)])
      (if (and n (<= k n))
          (call-with-values
              (lambda ()
                (split-at obj (- n k)))
            succeed)
          (fail))))

  (define-syntax match
    (lambda (form)
      (define who 'match)

      ;;; Holds the identifier denoting the matcher's main loop.
      ;;; Used by anonymous cata matchers.
      (define match-loop-id (make-parameter #f))

      ;;; Holds the identifier denoting the failure continuation for
      ;;; each match clause.
      (define fail-clause (make-parameter #f))

      (define-record-type pattern-variable
        (nongenerative) (sealed #t) (opaque #t)
        (fields name
                expression  ; Bound expression
                level))     ; Ellipsis level

      (define-record-type cata-binding
        (nongenerative) (sealed #t) (opaque #t)
        (fields procedure-expression ; Catamorphism operator
                value-names          ; Identifiers binding cata values
                mapping-name))       ; Name of pattern variable which
                                     ; maps the cata to an expression.

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
           (let ([id (pattern-variable-name v)])
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
            (cata-binding-value-names cata)))
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

      ;;; The following procedures emit the matcher code by chaining
      ;;; matcher-generators.
      ;;;
      ;;; A matcher-generator is a procedure of one argument. When
      ;;; invoked on a continuation, it produces matching code for its
      ;;; pattern and calls its argument to produce the rest of the
      ;;; matcher.

      ;;; Translates a pattern and input expression and returns three
      ;;; values: a matcher-generator, a list of *patterns*'s pattern
      ;;; variables, and its list of cata-bindings.
      (define (generate-matcher expression pattern)
        (syntax-case pattern (-> unquote)
          [,[cata-operator -> y ...]           ; Named cata-pattern
           (for-all identifier? #'(y ...))
           (generate-cata-matcher #'cata-operator expression #'(y ...))]
          [,[y ...]                ; Anonymous cata-pattern
           (for-all identifier? #'(y ...))
           (generate-cata-matcher (match-loop-id) expression #'(y ...))]
          ;; Match a pattern with a variable at the tail in order to
          ;; avoid misparsing '... . (unquote x)' as '... unquote x'.
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
          [#(pat ...) (generate-vector-matcher expression #'(pat ...))]
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
         (lambda (generate-more)
           #`(if (equal? #,expression '#,object)
                 #,(generate-more)
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
             (lambda (generate-more)
               #`(if (pair? #,expr)
                     (let ([e1 (car #,expr)]
                           [e2 (cdr #,expr)])
                       #,(mat1 (lambda () (mat2 generate-more))))
                     (#,(fail-clause))))
             (append pvars1 pvars2) (append catas1 catas2)))))

      (define (generate-ellipsis-matcher expression
                                         head-pattern
                                         body-patterns
                                         tail-pattern)
        (with-syntax ([(e1 e2) (generate-temporaries '(e1 e2))])
          (let*-values ([(mat1 pvars1 catas1)
                         (generate-glob-matcher #'e1 head-pattern)]
                        [(rest-patterns)
                         (append body-patterns tail-pattern)]
                        [(mat2 pvars2 catas2)
                         (generate-list-matcher #'e2 rest-patterns)])
            (values
             (lambda (generate-more)
               #`(split-right/continuations
                  #,expression
                  #,(length body-patterns)
                  (lambda (e1 e2)
                    #,(mat1 (lambda () (mat2 generate-more))))
                  #,(fail-clause)))
             (append pvars1 pvars2)
             (append catas1 catas2)))))

      ;;; Match the empty list.
      (define (generate-null-matcher expression)
        (values (lambda (generate-more)
                  #`(if (null? #,expression)
                        #,(generate-more)
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
                (lambda (generate-more)
                  #`(let ([e1 (car #,expression)]
                          [e2 (cdr #,expression)])
                      #,(mat1
                         (lambda ()
                           (mat2 generate-more)))))
                (append pvars1 pvars2)
                (append catas1 catas2))))]
          [_ (generate-matcher expression patterns)]))

      ;;; Build a matcher for an ellipsized pattern. This generates
      ;;; meta-variables (pattern variables with level > 1) to hold
      ;;; the lists of values matched by *pattern's* variables.
      (define (generate-glob-matcher expression pattern)
        (with-syntax ([(e es loop)
                       (generate-temporaries '(e es loop))])
          (let-values ([(mat ipvars catas)
                        (generate-matcher #'e pattern)])
            (with-syntax ([(a ...)   ; ids for value accumulators
                           (generate-temporaries ipvars)]
                          [(ve ...)
                           (map pattern-variable-expression ipvars)])
              (values
               (lambda (generate-more)
                 #`(let loop ([es (reverse #,expression)]
                              [a '()] ...)
                     (if (null? es)
                         #,(generate-more)
                         (let ([e (car es)])
                           #,(mat
                              (lambda ()
                                #`(loop (cdr es)
                                        (cons ve a) ...)))))))
               (make-meta-variables #'(a ...) ipvars)
               catas)))))

      ;;; Build a list of pattern-variables with the same names as
      ;;; the variables, but of higher level. These are bound to the
      ;;; expression-ids.
      (define (make-meta-variables expression-ids variables)
        (map (lambda (id v)
               (make-pattern-variable
                (pattern-variable-name v)
                id
                (+ (pattern-variable-level v) 1)))
             expression-ids
             variables))

      ;;; STUB
      ;;; Build a matcher for a vector pattern with an ellipsis
      ;;; sub-pattern.
      (define (generate-ellipsis-vector-matcher expression
                                                head-patterns
                                                ellipsis-pattern
                                                tail-patterns)
        (syntax-violation who
                          "vector patterns not yet implemented"
                          expression))

      ;;; STUB
      ;;; Build a matcher for a simple vector pattern.
      (define (generate-vector-matcher expression patterns)
        (with-syntax ([(ve) (generate-temporaries '(ve))])
          (let-values ([(generate pvars catas)
                        (vector-matcher-help #'ve patterns 0)])
            (values
             (lambda (generate-more)
               #`(let ([ve #,expression])
                   (if (and (vector? ve)
                            (= (vector-length ve) #,(length patterns)))
                       #,(generate generate-more)
                       (#,(fail-clause)))))
             pvars
             catas))))

      ;;; Build matchers for the elements of a vector pattern.
      ;;; FIXME: Avoid emitting nested lets when binding names to
      ;;; vector elements.
      (define (vector-matcher-help expression patterns index)
        (syntax-case patterns ()
          [() (values invoke '() '())]
          [(pat . more-patterns)
           (with-syntax ([(e) (generate-temporaries '(e))])
             (let*-values ([(mat1 pvars1 catas1)
                            (generate-matcher #'e #'pat)]
                           [(mat2 pvars2 catas2)
                            (vector-matcher-help expression
                                                 #'more-patterns
                                                 (+ index 1))])
               (values
                (lambda (generate-more)
                  #`(let ([e (vector-ref #,expression #,index)])
                      #,(mat1 (lambda () (mat2 generate-more)))))
                (append pvars1 pvars2)
                (append catas1 catas2))))]))

      ;;; Bind cata value-ids to (lists of ...) recursively-generated
      ;;; values, with the resulting list-depth being equal to the
      ;;; ellipsis level of the cata variables.
      ;;;
      ;;; Unellipsized cata variables are bound to the result of
      ;;; invoking the catamorphism operator on the bound expression.
      (define (generate-map-values operator value-ids binding level)
        (let generate-loop ([level level])
          (if (zero? level)
              #`(#,operator #,binding)
              ;; The cata variables are ellipsized, so we have to bind
              ;; them to lists of results.
              (with-syntax ([(vs ...)  ; value accumulators
                             (generate-temporaries value-ids)]
                            [(v ...) (generate-temporaries value-ids)]
                            [e binding])
                #`(let loop ([e* (reverse e)]
                             [vs '()] ...)
                    (if (null? e*)
                        (values vs ...)
                        (let ([e (car e*)]
                              [e* (cdr e*)])
                          (let-values ([(v ...)
                                        #,(generate-loop (- level 1))])
                            (loop e* (cons v vs) ...)))))))))

      ;;; Parses and translates a matcher clause.
      (define (generate-clause keyword expression-id clause)
        (let*-values ([(pattern guard-expression body)
                       (parse-clause clause)]
                      [(matcher pvars catas)
                       (generate-matcher expression-id pattern)])
          (check-pattern-variables pvars)
          (check-cata-bindings catas)
          (with-syntax ([quasiquote (datum->syntax keyword 'quasiquote)]
                        [(x ...)
                         (map pattern-variable-name pvars)]
                        [(u ...)
                         (map pattern-variable-expression pvars)]
                        [(f ...)
                         (map cata-binding-procedure-expression catas)]
                        [((y ...) ...)
                         (map cata-binding-value-names catas)]
                        [(z ...)
                         (map cata-binding-mapping-name catas)]
                        [(tmp ...) (generate-temporaries catas)])
            (with-syntax ([(e ...) (make-cata-values pvars
                                                     #'(tmp ...)
                                                     #'((y ...) ...)
                                                     #'(z ...))])
              (matcher
               (lambda ()
                 #`(let ([x u] ...)  ; bind all pattern variables
                     (if #,guard-expression
                         (let ([tmp f] ...)  ; bind cata operators?
                           ;; Bind cata variables to generated values
                           (let-values ([(y ...) e] ...)
                             (let-syntax ([quasiquote
                                           quasiquote-transformer])
                               #,@body)))
                         (#,(fail-clause))))))))))

      ;;; Emits code to bind cata mapping variables to their
      ;;; recursively-generated values. The actual cata-variable
      ;;; identifiers will later be bound to these values directly.
      (define (make-cata-values variables
                                temporaries
                                value-ids
                                mapping-ids)
        ;; Returns the ellipsis level of the pattern variable
        ;; named *id*.
        (define (mapping-id-level id)
          (exists (lambda (v)
                    (let ([x (pattern-variable-name v)])
                      (and (bound-identifier=? x id)
                           (pattern-variable-level v))))
                  variables))

        (map (lambda (t ids b)
               (generate-map-values t ids b (mapping-id-level b)))
             temporaries
             value-ids
             mapping-ids))

      ;;; Fold the match clauses, emitting their code "from the
      ;;; inside out". At each step, the *fail-clause* parameter
      ;;; is bound to a continuation that aborts the current match
      ;;; and proceeds to the rest of the clauses. The final failure
      ;;; continuation raises an exception.
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
      (syntax-case form ()
        [(match expression clause ...)
         (with-syntax ([(lp ev) (generate-temporaries '(lp ev))])
           (parameterize ([match-loop-id #'lp])
             #`(let lp ([ev expression])
                 #,(generate-match #'match #'ev #'(clause ...)))))])))

  )
