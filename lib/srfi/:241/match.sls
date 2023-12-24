#!r6rs

;; Copyright (C) Marc Nieper-Wißkirchen (2022).  All Rights Reserved.

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
    (lambda (stx)
      (syntax-violation '-> "invalid use of auxiliary syntax" stx)))

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
    (lambda (stx)
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
                          stx
                          id))

      ;;; Check a list of pattern-variables for duplicates.
      (define (check-pattern-variables pvars)
        (define id-table (make-identifier-hashtable))

        (define (mark id)
          (lambda (val)
            (when val (repeated-pvar-error id))
            #t))

        (for-each
         (lambda (pvar)
           (let ([id (pattern-variable-identifier pvar)])
             (hashtable-update! id-table id (mark id) #f)))
         pvars))

      (define (repeated-cata-var-error id)
        (syntax-violation who
                          "repeated cata variable in match clause"
                          stx
                          id))

      ;;; Check a list of cata-variables for duplicates. Only
      ;;; cata value-ids are checked.
      (define (check-cata-bindings catas)
        (define id-table (make-identifier-hashtable))

        (define (mark id)
          (lambda (val)
            (when val (repeated-cata-var-error id))
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
           (syntax-violation who "ill-formed match clause" stx clause)]))

      (define (generate-matcher expression pattern)
        (define (ill-formed-match-pattern-violation)
          (syntax-violation who "ill-formed match pattern" stx pattern))

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
           (ill-formed-match-pattern-violation)]
          [_ (generate-constant-matcher expression pattern)]))

      (define (generate-cata-matcher cata-op expr ids)
        (with-syntax ([(x) (generate-temporaries '(x))])
          (values
           invoke
           (list (make-pattern-variable #'x expr 0))
           (list (make-cata-binding cata-op ids #'x)))))

      ;;; Match expr by binding a pattern variable named *id* to it.
      (define (generate-variable-matcher expr id)
        (values
         invoke
         (list (make-pattern-variable id expr 0))
         '()))

      ;;; Match expr against the constant obj.
      (define (generate-constant-matcher expr obj)
        (values
         (lambda (succeed)
           #`(if (equal? #,expr '#,obj)
                 #,(succeed)
                 (#,(fail-clause))))
         '()
         '()))

      ;;; Match the head of expr with car-pat and its tail with
      ;;; cdr-pat.
      (define (generate-pair-matcher expr car-pat cdr-pat)
        (with-syntax ([(e1 e2) (generate-temporaries '(e1 e2))])
          (let*-values ([(mat1 pvars1 catas1)
                         (generate-matcher #'e1 car-pat)]
                        [(mat2 pvars2 catas2)
                         (generate-matcher #'e2 cdr-pat)])
            (values
             (lambda (succeed)
               #`(if (pair? #,expr)
                     (let ([e1 (car #,expr)]
                           [e2 (cdr #,expr)])
                       #,(mat1 (lambda () (mat2 succeed))))
                     (#,(fail-clause))))
             (append pvars1 pvars2) (append catas1 catas2)))))

      (define (generate-ellipsis-matcher expr head-pat body-pats tail-pat)
        (with-syntax ([(e1 e2) (generate-temporaries '(e1 e2))])
          (let*-values ([(mat1 pvars1 catas1)
                         (generate-map #'e1 head-pat)]
                        [(rest-pat*) (append body-pats tail-pat)]
                        [(mat2 pvars2 catas2)
                         (generate-matcher* #'e2 rest-pat*)])
            (values
             (lambda (succeed)
               #`(split-right/continuations
                  #,expr
                  #,(length body-pats)
                  (lambda (e1 e2)
                    #,(mat1 (lambda () (mat2 succeed))))
                  #,(fail-clause)))
             (append pvars1 pvars2)
             (append catas1 catas2)))))

      ;;; Match the empty list.
      (define (generate-null-matcher expr)
        (values (lambda (succeed)
                  #`(if (null? #,expr)
                        #,(succeed)
                        (#,(fail-clause))))
                '()
                '()))

      ;;; Match expr recursively against the list pattern pat*.
      (define (generate-matcher* expr pat*)
        (syntax-case pat* (unquote)
          [() (generate-null-matcher expr)]
          [,x (generate-matcher expr pat*)]
          [(pat . pat*)
           (with-syntax ([(e1 e2) (generate-temporaries '(e1 e2))])
             (let*-values ([(mat1 pvars1 catas1)
                            (generate-matcher #'e1 #'pat)]
                           [(mat2 pvars2 catas2)
                            (generate-matcher* #'e2 #'pat*)]) ; recur
               (values
                (lambda (succeed)
                  #`(let ([e1 (car #,expr)]
                          [e2 (cdr #,expr)])
                      #,(mat1
                         (lambda ()
                           (mat2 succeed)))))
                (append pvars1 pvars2)
                (append catas1 catas2))))]
          [_ (generate-matcher expr pat*)]))

      (define (generate-map expr pat)
        (with-syntax ([(e1 e2 f) (generate-temporaries '(e1 e2 f))])
          (let-values ([(mat ipvars catas) (generate-matcher #'e1 pat)])
            (with-syntax ([(u ...) (generate-temporaries ipvars)]
                          [(v ...)
                           (map pattern-variable-expression ipvars)])
              (values
               (lambda (succeed)
                 #`(let f ([e2 (reverse #,expr)]
                           [u '()] ...)
                     (if (null? e2)
                         #,(succeed)
                         (let ([e1 (car e2)])
                           #,(mat (lambda ()
                                    #`(f (cdr e2) (cons v u) ...)))))))
               (make-meta-variables #'(u ...) ipvars)
               catas)))))

      ;;; Build a list of pattern-variables with the same names as
      ;;; the pvars, but of higher level. These are bound to the
      ;;; expr-ids.
      (define (make-meta-variables expr-ids pvars)
        (map (lambda (id pvar)
               (make-pattern-variable
                (pattern-variable-identifier pvar)
                id
                (+ (pattern-variable-level pvar) 1)))
             expr-ids
             pvars))

      (define (generate-map-values proc-expr y* e n)
        (let generate-loop ([n n])
          (if (zero? n)
              #`(#,proc-expr #,e)
              (with-syntax ([(tmps ...) (generate-temporaries y*)]
                            [(tmp ...) (generate-temporaries y*)]
                            [e e])
                #`(let loop ([e* (reverse e)]
                             [tmps '()] ...)
                    (if (null? e*)
                        (values tmps ...)
                        (let ([e (car e*)]
                              [e* (cdr e*)])
                          (let-values ([(tmp ...)
                                        #,(generate-loop (- n 1))])
                            (loop e* (cons tmp tmps) ...)))))))))

      (define (generate-clause k expression-id cl)
        (let*-values ([(pat guard-expr body) (parse-clause cl)]
                      [(matcher pvars catas)
                       (generate-matcher expression-id pat)])
          (check-pattern-variables pvars)
          (check-cata-bindings catas)
          (with-syntax ([quasiquote (datum->syntax k 'quasiquote)]
                        [(x ...)
                         (map pattern-variable-identifier pvars)]
                        [(u ...)
                         (map pattern-variable-expression pvars)]
                        [(f ...) (map cata-binding-procedure-expression catas)]
                        [((y ...) ...)
                         (map cata-binding-value-identifiers catas)]
                        [(z ...) (map cata-binding-meta-identifier catas)]
                        [(tmp ...) (generate-temporaries catas)])
            (with-syntax ([(e ...) (make-cata-values pvars
                                                     #'(tmp ...)
                                                     #'((y ...) ...)
                                                     #'(z ...))])
              (matcher
               (lambda ()
                 #`(let ([x u] ...)
                     (if #,guard-expr
                         (let ([tmp f] ...)
                           (let-values ([(y ...) e] ...)
                             (let-syntax ([quasiquote
                                           quasiquote-transformer])
                               #,@body)))
                         (#,(fail-clause))))))))))

      (define (make-cata-values pvars tmps val-ids bind-ids)
        (define (bind-id-level z)
          (exists (lambda (pvar)
                    (let ([x (pattern-variable-identifier pvar)])
                      (and (bound-identifier=? x z)
                           (pattern-variable-level pvar))))
                  pvars))

        (map (lambda (tmp y* z)
               (generate-map-values tmp y* z (bind-id-level z)))
             tmps
             val-ids
             bind-ids))

      (define (generate-match k expression-id cl*)
        (fold-right
         (lambda (cl rest)
           (with-syntax ([(fail) (generate-temporaries '(fail))])
             (parameterize ([fail-clause #'fail])
               #`(let ([fail (lambda () #,rest)])
                   #,(generate-clause k expression-id cl)))))
         #`(assertion-violation 'who
                                "value does not match"
                                #,expression-id)
         cl*))

      ;;; Emit the main pattern-matching loop, then the matcher body.
      ;;;
      ;;; Binds the 'match-loop' & 'expr-val' identifiers which are
      ;;; referenced by generated matchers.
      (syntax-case stx ()
        [(match expression clause ...)
         (with-syntax ([(lp ev) (generate-temporaries '(lp ev))])
           (parameterize ([match-loop-id #'lp])
             #`(let lp ([ev expression])
                 #,(generate-match #'match #'ev #'(clause ...)))))])))

  )
