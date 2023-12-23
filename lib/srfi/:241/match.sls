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
          unquote ... _ -> guard)
  (import (rnrs (6))
          (srfi :241 match helpers)
          (srfi :241 match quasiquote-transformer))

  (define-syntax ->
    (lambda (stx)
      (syntax-violation '-> "invalid use of auxiliary syntax" stx)))

  (define (split/continuations obj k succ fail)
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

      (define (invoke success) (success))

      (define-record-type pattern-variable
        (nongenerative) (sealed #t) (opaque #t)
        (fields identifier expression level))

      (define-record-type cata-binding
        (nongenerative) (sealed #t) (opaque #t)
        (fields proc-expr value-id* identifier))

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

      (define (check-pattern-variables pvars)
        (define ht (make-identifier-hashtable))

        (define (mark id)
          (lambda (val)
            (when val (repeated-pvar-error id))
            #t))

        (for-each
         (lambda (pvar)
           (let ([id (pattern-variable-identifier pvar)])
             (hashtable-update! ht id (mark id) #f)))
         pvars))

      (define (repeated-cata-var-error id)
        (syntax-violation who
                          "repeated cata variable in match clause"
                          stx
                          id))

      (define (check-cata-bindings catas)
        (define ht (make-identifier-hashtable))

        (define (mark id)
          (lambda (val)
            (when val (repeated-cata-var-error id))
            #t))

        (for-each
         (lambda (cata)
           (for-each
            (lambda (id)
              (hashtable-update! ht id (mark id) #f))
            (cata-binding-value-id* cata)))
         catas))

      (define (parse-clause cl)
        (syntax-case cl (guard)
          [(pat (guard guard-expr ...) e1 e2 ...)
           (values #'pat #'(and guard-expr ...) #'(e1 e2 ...))]
          [(pat e1 e2 ...) (values #'pat #'#t #'(e1 e2 ...))]
          [_ (syntax-violation who "ill-formed match clause" stx cl)]))

      (define (gen-matcher expr pat)
        (define (ill-formed-match-pattern-violation)
          (syntax-violation who "ill-formed match pattern" stx pat))

        (syntax-case pat (-> unquote)
          [,[f -> y ...]
           (for-all identifier? #'(y ...))
           (gen-cata-matcher #'f expr #'(y ...))]
          [,[y ...]
           (for-all identifier? #'(y ...))
           (gen-cata-matcher #'match-loop expr #'(y ...))]
          [(pat1 ell pat2 ... . pat3)
           (ellipsis? #'ell)
           (gen-ellipsis-matcher expr #'pat1 #'(pat2 ...) #'pat3)]
          [,x
           (identifier? #'x)
           (gen-variable-matcher expr #'x)]
          [(pat1 . pat2) (gen-pair-matcher expr #'pat1 #'pat2)]
          [unquote
           (ill-formed-match-pattern-violation)]
          [_ (gen-constant-matcher expr pat)]))

      (define (gen-cata-matcher cata-op expr ids)
        (with-syntax ([(x) (generate-temporaries '(x))])
          (values
           invoke
           (list (make-pattern-variable #'x expr 0))
           (list (make-cata-binding cata-op ids #'x)))))

      (define (gen-variable-matcher expr id)
        (values
         invoke
         (list (make-pattern-variable id expr 0))
         '()))

      (define (gen-constant-matcher expr obj)
        (values
         (lambda (succeed)
           #`(if (equal? #,expr '#,obj)
                 #,(succeed)
                 (fail)))
         '()
         '()))

      (define (gen-pair-matcher expr car-pat cdr-pat)
        (with-syntax ([(e1 e2) (generate-temporaries '(e1 e2))])
          (let*-values ([(mat1 pvars1 catas1)
                         (gen-matcher #'e1 car-pat)]
                        [(mat2 pvars2 catas2)
                         (gen-matcher #'e2 cdr-pat)])
            (values
             (lambda (succeed)
               #`(if (pair? #,expr)
                     (let ([e1 (car #,expr)]
                           [e2 (cdr #,expr)])
                       #,(mat1 (lambda () (mat2 succeed))))
                     (fail)))
             (append pvars1 pvars2) (append catas1 catas2)))))

      (define (gen-ellipsis-matcher expr pat1 pat2* pat3)
        (with-syntax ([(e1 e2) (generate-temporaries '(e1 e2))])
          (let*-values ([(mat1 pvars1 catas1)
                         (gen-map #'e1 pat1)]
                        [(mat2 pvars2 catas2)
                         (gen-matcher* #'e2 (append pat2* pat3))])
            (values
             (lambda (succeed)
               #`(split/continuations
                  #,expr
                  #,(length pat2*)
                  (lambda (e1 e2)
                    #,(mat1 (lambda () (mat2 succeed))))
                  fail))
             (append pvars1 pvars2)
             (append catas1 catas2)))))

      (define (null-matcher expr)
        (lambda (succeed)
          #`(if (null? #,expr)
                #,(succeed)
                (fail))))

      (define (gen-matcher* expr pat*)
        (syntax-case pat* (unquote)
          [() (values (null-matcher expr) '() '())]
          [,x (gen-matcher expr pat*)]
          [(pat . pat*)
           (with-syntax ([(e1 e2) (generate-temporaries '(e1 e2))])
             (let*-values ([(mat1 pvars1 catas1)
                            (gen-matcher #'e1 #'pat)]
                           [(mat2 pvars2 catas2)
                            (gen-matcher* #'e2 #'pat*)])
               (values
                (lambda (succeed)
                  #`(let ([e1 (car #,expr)]
                          [e2 (cdr #,expr)])
                      #,(mat1
                         (lambda ()
                           (mat2 succeed)))))
                (append pvars1 pvars2)
                (append catas1 catas2))))]
          [_ (gen-matcher expr pat*)]))

      (define (gen-map expr pat)
        (with-syntax ([(e1 e2 f) (generate-temporaries '(e1 e2 f))])
          (let-values ([(mat ipvars catas) (gen-matcher #'e1 pat)])
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

      (define (make-meta-variables ids pvars)
        (map (lambda (id pvar)
               (make-pattern-variable
                (pattern-variable-identifier pvar)
                id
                (+ (pattern-variable-level pvar) 1)))
             ids
             pvars))

      (define (gen-map-values proc-expr y* e n)
        (let gen-loop ([n n])
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
                                        #,(gen-loop (- n 1))])
                            (loop e* (cons tmp tmps) ...)))))))))

      (define (gen-clause k cl)
        (let*-values ([(pat guard-expr body) (parse-clause cl)]
                      [(matcher pvars catas)
                       (gen-matcher #'expr-val pat)])
          (check-pattern-variables pvars)
          (check-cata-bindings catas)
          (with-syntax ([quasiquote (datum->syntax k 'quasiquote)]
                        [(x ...)
                         (map pattern-variable-identifier pvars)]
                        [(u ...)
                         (map pattern-variable-expression pvars)]
                        [(f ...) (map cata-binding-proc-expr catas)]
                        [((y ...) ...)
                         (map cata-binding-value-id* catas)]
                        [(z ...) (map cata-binding-identifier catas)]
                        [(tmp ...) (generate-temporaries catas)])
            (with-syntax ([(e ...)
                           (map
                            (lambda (tmp y* z)
                              (let ([n
                                     (exists
                                      (lambda (pvar)
                                        (let ([x (pattern-variable-identifier pvar)])
                                          (and (bound-identifier=? x z)
                                               (pattern-variable-level pvar))))
                                      pvars)])
                                (gen-map-values tmp y* z n)))
                            #'(tmp ...) #'((y ...) ...) #'(z ...))])
              (matcher
               (lambda ()
                 #`(let ([x u] ...)
                     (if #,guard-expr
                         (let ([tmp f] ...)
                           (let-values ([(y ...) e] ...)
                             (let-syntax ([quasiquote quasiquote-transformer])
                               #,@body)))
                         (fail)))))))))

      (define (gen-match k cl*)
        (fold-right
         (lambda (cl rest)
           #`(let ([fail (lambda () #,rest)])
               #,(gen-clause k cl)))
         #'(assertion-violation 'who "value does not match" expr-val)
         cl*))

      ;; Binds the 'match-loop' & 'expr-val' identifiers which are
      ;; referenced by generated matchers.
      (syntax-case stx ()
        [(k expr cl ...)
         #`(let match-loop ([expr-val expr])
             #,(gen-match #'k #'(cl ...)))])))

  )
