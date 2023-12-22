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
          unquote ... _ -> guard)
  (import (rnrs (6))
          (srfi :241 match helpers)
          (srfi :241 match quasiquote-transformer))

  (define-syntax ->
    (lambda (stx)
      (syntax-violation '-> "invalid use of auxiliary syntax" stx)))

  ;;;; match

  (define-syntax match
    (lambda (stx)
      ;;; Helper procedures & syntax
      (define who 'match)

      (define (split-cps obj k succ fail)
        (let ([n (cons-length obj)])
          (if (<= k n)
              (call-with-values
               (lambda ()
                 (split-at obj (- n k)))
               succ)
              (fail))))

      (define (make-identifier-hashtable)
        (let ((identifier-hash
               (lambda (id)
                 (assert (identifier? id))
                 (symbol-hash (syntax->datum id)))))
          (make-hashtable identifier-hash bound-identifier=?)))

      (define (invoke cont) (cont))

      (define-record-type pattern-variable
        (nongenerative) (sealed #t) (opaque #t)
        (fields identifier   ; The pattern variable's name.
                expression   ; The expression it's bound to.
                level))      ; Recursion level of binding.

      (define-record-type cata-binding
        (nongenerative) (sealed #t) (opaque #t)
        (fields proc-expr    ; The catamorphism operator.
                value-ids    ; The identifiers bound to the results.
                identifier)) ; Name of associated, hidden pattern var.

      (define repeated-pvar-error
        (lambda (id)
          (syntax-violation
           who
           "repeated pattern variable in match clause" stx id)))

      ;; Check *pvars* for repeated pattern variables.
      (define (check-pattern-variables pvars)
        (let ((ht (make-identifier-hashtable)))
          (for-each
           (lambda (pvar)
             (let* ((id (pattern-variable-identifier pvar))
                    (update (lambda (val)
                              (when val (repeated-pvar-error id))
                              #t)))
               (hashtable-update! ht id update #f)))
           pvars)))

      (define (repeated-cata-var-error id)
        (syntax-violation who
                          "repeated cata variable in match clause"
                          stx
                          id))

      ;; Check *catas* for repeated cata variables.
      (define (check-cata-bindings catas)
        (let ((ht (make-identifier-hashtable)))
          (for-each
           (lambda (cata)
             (for-each
              (lambda (id)
                (let ((update (lambda (val)
                                (when val (repeated-cata-var-error id))
                                #t)))
                  (hashtable-update! ht id update #f)))
              (cata-binding-value-ids cata)))
           catas)))

      ;; Splits a match clause into pattern, guard, and body components,
      ;; then returns those as multiple values.
      (define (parse-clause cl)
        (syntax-case cl (guard)
          [(pat (guard guard-expr ...) e1 e2 ...)
           (values #'pat #'(and guard-expr ...) #'(e1 e2 ...))]
          [(pat e1 e2 ...)
           (values #'pat #'#t #'(e1 e2 ...))]
          [_
           (syntax-violation who "ill-formed match clause" stx cl)]))

      (define (ill-formed-match-pattern-violation pat)
        (syntax-violation who "ill-formed match pattern" stx pat))

      ;; Construct and return a matcher procedure, a list of pattern
      ;; variables, and a list of cata variables for matching *expr* to
      ;; *pat*.
      (define (gen-matcher expr pat)
        (syntax-case pat (-> unquote)
          [,[f -> y ...]     ; Cata pattern with named operator.
           (for-all identifier? #'(y ...))
           (gen-cata-matcher expr #'f #'(y ...))]
          [,[y ...]          ; (Anonymous) cata pattern.
           (for-all identifier? #'(y ...))
           (gen-cata-matcher expr #'loop #'(y ...))]
          [(pat1 ell pat2 ... . pat3)  ; Ellipsis pattern.
           (ellipsis? #'ell)
           (gen-ellipsis-matcher expr #'pat1 #'(pat2 ...) #'pat3)]
          [,u
           (underscore? #'u)
           (values invoke '() '())]
          [,x
           (identifier? #'x)
           (gen-variable-matcher expr #'x)]
          [(pat1 . pat2) (gen-pair-matcher expr #'pat1 #'pat2)]
          [unquote (ill-formed-match-pattern-violation pat)]
          [_ (gen-constant-matcher expr #'pat)]))

      ;; Build a catamorphism matcher which recursively applies
      ;; *op* and binds the results to the *ids*.
      (define (gen-cata-matcher expr op ids)
        (with-syntax ([(x) (generate-temporaries '(x))])
          (values
           invoke
           (list (make-pattern-variable #'x expr 0))
           (list (make-cata-binding #'op #'ids #'x)))))

      ;; Build a simple matcher which binds the pattern variable
      ;; with name *id* to the value of *expr*.
      (define (gen-variable-matcher expr id)
        (values invoke
                (list (make-pattern-variable #'id expr 0))
                '()))

      ;; Build a matcher which matches *expr* against the literal
      ;; pattern *pat*.
      (define (gen-constant-matcher expr pat)
        (values
         (lambda (succeed)
           #`(if (equal? #,expr '#,pat)
                  #,(succeed)
                  (fail)))
         '()
         '()))

      ;; Build a matcher which matches the head of *expr* against
      ;; *car-pat* and its tail against *cdr-pat*.
      (define (gen-pair-matcher expr car-pat cdr-pat)
        ;; Temporary expression values for the head & tail matchers.
        (with-syntax ([(e1 e2) (generate-temporaries '(e1 e2))])
          ;; Build head & tail matchers.
          (let*-values ([(car-match car-pvars car-catas)
                         (gen-matcher #'e1 #'car-pat)]
                        [(cdr-match cdr-pvars cdr-catas)
                         (gen-matcher #'e2 #'cdr-pat)])
            (values
             (lambda (succeed)     ; Combine matchers.
               #`(if (pair? #,expr)
                     (let ([e1 (car #,expr)]
                           [e2 (cdr #,expr)])
                       #,(car-match (lambda () (cdr-match succeed))))
                     (fail)))
             (append car-pvars cdr-pvars)
             (append car-catas cdr-catas)))))

      ;; Build a matcher which matches *expr* against the pattern
      ;;
      ;;     (ell-pat ... body-pat0 ::: body-patN . tail-pat)
      ;;
      ;; where body-pats = (body-pat0 ::: body-patN).
      (define (gen-ellipsis-matcher expr ell-pat body-pats tail-pat)
        (with-syntax ([(e1 e2) (generate-temporaries '(e1 e2))])
          (let*-values ([(head-match head-pvars head-catas)
                         (gen-glob-matcher #'e1 ell-pat)]
                        [(rest-pats) (append body-pats tail-pat)]
                        [(tail-match tail-pvars tail-catas)
                         (gen-list-matcher #'e2 rest-pats)])
            (values
             (lambda (succeed)
               #`(split-cps
                  #,expr
                  #,(length body-pats)
                  (lambda (e1 e2)
                    #,(head-match (lambda () (tail-match succeed))))
                  fail))
             (append head-pvars tail-pvars)
             (append head-catas tail-catas)))))

      ;; Build a matcher for *expr* from a proper or improper list
      ;; of patterns.
      (define (gen-list-matcher expr pats)
        (syntax-case pats (unquote)
          [() (values (null-matcher expr) '() '())]
          [,x (gen-matcher expr pats)]
          [(pat . pats)
           (with-syntax ([(e1 e2) (generate-temporaries '(e1 e2))])
             (let*-values ([(mat1 pvars1 catas1)
                            (gen-matcher #'e1 #'pat)]
                           [(mat2 pvars2 catas2)
                            (gen-list-matcher #'e2 #'pat*)])  ; recur
               (values  ; combine head & tail matchers
                (lambda (succeed)
                  #`(let ([e1 (car #,expr)]
                          [e2 (cdr #,expr)])
                      #,(mat1
                         (lambda ()
                           (mat2 succeed)))))
                (append pvars1 pvars2)
                (append catas1 catas2))))]
          [_  ; pass the buck
           (gen-matcher expr pats)]))

      ;; Matcher for the empty list.
      (define (null-matcher expr)
        (lambda (succeed)
          #`(if (null? #,expr)
                #,(succeed)
                (fail))))

      ;; Build a matcher for the ellipsized pattern *pat*.
      (define (gen-glob-matcher expr pat)
        (with-syntax ([(head lis loop)
                       (generate-temporaries '(head lis loop))])
          (let-values ([(matcher ipvars catas)
                        (gen-matcher #'head pat)])
            (with-syntax ([(u ...)
                           (generate-temporaries ipvars)]
                          [(v ...)
                           (map pattern-variable-expression ipvars)])
              (values
               ;; Matches each element of the list expr, accumulating
               ;; bindings of u's to v's.
               (lambda (succeed)
                 #`(let loop ([lis (reverse #,expr)]
                              [u '()] ...)
                     (if (null? lis)
                         #,(succeed)
                         (let ([head (car lis)])
                           #,(matcher
                              (lambda ()
                                #`(loop (cdr lis) (cons v u) ...)))))))
               ;; Make "meta" pattern variables for the ellipsized
               ;; variables. These will be bound to lists of values
               ;; matched individually.
               (map
                (lambda (id pvar)
                  (make-pattern-variable
                   (pattern-variable-identifier pvar)
                   id
                   (+ (pattern-variable-level pvar) 1)))
                #'(u ...)
                ipvars)
               catas)))))

      (define (gen-cata-values proc-expr cata-val-ids bind-id level)
        (let gen-loop ([level level])
          (if (zero? level)
              #`(#,proc-expr #,bind-id)
              (with-syntax ([(tmps ...)
                             (generate-temporaries cata-val-ids)]
                            [(tmp ...)
                             (generate-temporaries cata-val-ids)]
                            [bind-id bind-id])
                #`(let loop ([e* (reverse bind-id)]
                             [tmps '()] ...)
                    (if (null? e*)
                        (values tmps ...)
                        (let ([e (car e*)]
                              [e* (cdr e*)])
                          (let-values ([(tmp ...)
                                        #,(gen-loop (- level 1))])
                            (loop e* (cons tmp tmps) ...)))))))))

      (define (gen-clause key clause)
        (let*-values ([(pat guard-expr body)
                       (parse-clause clause)]
                      [(matcher pvars catas)
                       (gen-matcher #'expr-val pat)])
          (check-pattern-variables pvars)
          (check-cata-bindings catas)
          (with-syntax ([quasiquote
                         (datum->syntax key 'quasiquote)]
                        [(x ...)
                         (map pattern-variable-identifier pvars)]
                        [(u ...)
                         (map pattern-variable-expression pvars)]
                        [(f ...)
                         (map cata-binding-proc-expr catas)]
                        [((y ...) ...)
                         (map cata-binding-value-ids catas)]
                        [(z ...)
                         (map cata-binding-identifier catas)]
                        [(tmp ...)
                         (generate-temporaries catas)])
            (with-syntax ([(e ...)
                           (extract-cata-values pvars
                                                #'(tmp ...)
                                                #'((y ...) ...)
                                                #'(z ...))])
              (matcher
               (lambda ()
                 #`(let ([x u] ...)
                     (if #,guard-expr
                         (let ([tmp f] ...)
                           (let-values ([(y ...) e] ...)
                             (let-syntax ([quasiquote quasiquote-transformer])
                               #,@body)))
                         (fail)))))))))

      (define (extract-cata-values pvars tmps val-ids bind-ids)
        (define (binding-id-level z)
          (exists (lambda (pvar)
                    (let ([id (pattern-variable-identifier pvar)])
                      (and (bound-identifier=? id z)
                           (pattern-variable-level pvar))))
                  pvars))

        (map (lambda (tmp ys z)
               (let ([n (binding-id-level z)])
                 (gen-cata-values tmp ys z n)))
             tmps
             val-ids
             bind-ids))

      ;; Parse each *clause* and combine the results into a single
      ;; matcher. This binds the 'fail' continuations which are used
      ;; by other gen- procedures.
      (define (gen-match key clauses)
        (fold-right
         (lambda (cl rest)
           #`(let ([fail (lambda () #,rest)])
               #,(gen-clause key cl)))
         #'(assertion-violation 'who "value does not match" expr-val)
         clauses))

      (syntax-case stx ()
        [(key expr clause ...)
         #`(let loop ([expr-val expr])
             #,(gen-match #'key #'(clause ...)))])))

  )
