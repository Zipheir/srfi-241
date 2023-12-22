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

  ;;; Helper procedures & syntax

  (define-syntax ->
    (lambda (stx)
      (syntax-violation '-> "invalid use of auxiliary syntax" stx)))

  (define (split obj k succ fail)
    (let ([n (cons-length obj)])
      (if (<= k n)
          (call-with-values
           (lambda ()
             (split-at obj (- n k)))
           succ)
          (fail))))

  (define who 'match)

  (define (make-identifier-hashtable)
    (let ((identifier-hash
           (lambda (id)
             (assert (identifier? id))
             (symbol-hash (syntax->datum id)))))
      (make-hashtable identifier-hash bound-identifier=?)))

  (define (repeated-pvar-error stx id)
    (syntax-violation
     who
     "repeated pattern variable in match clause" stx id))

  (define (repeated-cata-var-error stx id)
    (syntax-violation who
                      "repeated cata variable in match clause"
                      stx
                      id))

  ;;;; match

  (define-syntax match
    (lambda (stx)
      (define-record-type pattern-variable
        (nongenerative) (sealed #t) (opaque #t)
        (fields identifier expression level))

      (define-record-type cata-binding
        (nongenerative) (sealed #t) (opaque #t)
        (fields proc-expr value-ids identifier))

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
          [,[f -> y ...]
           (for-all identifier? #'(y ...))
           (with-syntax ([(x) (generate-temporaries '(x))])
             (values
              (lambda (k)
                (k))
              (list (make-pattern-variable #'x expr 0))
              (list (make-cata-binding #'f #'(y ...) #'x))))]
          [,[y ...]
           (for-all identifier? #'(y ...))
           (with-syntax ([(x) (generate-temporaries '(x))])
             (values
              (lambda (k)
                (k))
              (list (make-pattern-variable #'x expr 0))
              (list (make-cata-binding #'loop #'(y ...) #'x))))]
          [(pat1 ell pat2 ... . pat3)
           (ellipsis? #'ell)
           (gen-ellipsis-matcher expr #'pat1 #'(pat2 ...) #'pat3)]
          [,x
           (identifier? #'x)
           (values
            (lambda (k)
              (k))
            (list (make-pattern-variable #'x expr 0))
            '())]
          [(pat1 . pat2)
           (with-syntax ([(e1 e2) (generate-temporaries '(e1 e2))])
             (let*-values ([(mat1 pvars1 catas1)
                            (gen-matcher #'e1 #'pat1)]
                           [(mat2 pvars2 catas2)
                            (gen-matcher #'e2 #'pat2)])
               (values
                (lambda (k)
                  #`(if (pair? #,expr)
                        (let ([e1 (car #,expr)]
                              [e2 (cdr #,expr)])
                          #,(mat1 (lambda () (mat2 k))))
                        (fail)))
                (append pvars1 pvars2) (append catas1 catas2))))]
          [unquote
           (ill-formed-match-pattern-violation)]
          [_
           (values
            (lambda (k)
              #`(if (equal? #,expr '#,pat)
                    #,(k)
                    (fail)))
            '() '())]))

      (define (gen-ellipsis-matcher expr pat1 pat2* pat3)
        (with-syntax ([(e1 e2) (generate-temporaries '(e1 e2))])
          (let*-values ([(mat1 pvars1 catas1)
                         (gen-map #'e1 pat1)]
                        [(mat2 pvars2 catas2)
                         (gen-matcher* #'e2 (append pat2* pat3))])
            (values
             (lambda (k)
               #`(split
                  #,expr
                  #,(length pat2*)
                  (lambda (e1 e2)
                    #,(mat1 (lambda () (mat2 k))))
                  fail))
             (append pvars1 pvars2)
             (append catas1 catas2)))))

      (define (gen-matcher* expr pat*)
        (syntax-case pat* (unquote)
          [()
           (values
            (lambda (k)
              #`(if (null? #,expr)
                    #,(k)
                    (fail)))
            '() '())]
          [,x
           (gen-matcher expr pat*)]
          [(pat . pat*)
           (with-syntax ([(e1 e2) (generate-temporaries '(e1 e2))])
             (let*-values ([(mat1 pvars1 catas1)
                            (gen-matcher #'e1 #'pat)]
                           [(mat2 pvars2 catas2)
                            (gen-matcher* #'e2 #'pat*)])
               (values
                (lambda (k)
                  #`(let ([e1 (car #,expr)]
                          [e2 (cdr #,expr)])
                      #,(mat1
                         (lambda ()
                           (mat2 k)))))
                (append pvars1 pvars2)
                (append catas1 catas2))))]
          [_
           (gen-matcher expr pat*)]))

      (define (gen-map expr pat)
        (with-syntax ([(e1 e2 f) (generate-temporaries '(e1 e2 f))])
          (let-values ([(mat ipvars catas)
                        (gen-matcher #'e1 pat)])
            (with-syntax ([(u ...)
                           (generate-temporaries ipvars)]
                          [(v ...)
                           (map pattern-variable-expression ipvars)])
              (values
               (lambda (k)
                 #`(let f ([e2 (reverse #,expr)]
                           [u '()] ...)
                     (if (null? e2)
                         #,(k)
                         (let ([e1 (car e2)])
                           #,(mat (lambda ()
                                    #`(f (cdr e2) (cons v u) ...)))))))
               (map
                (lambda (id pvar)
                  (make-pattern-variable
                   (pattern-variable-identifier pvar)
                   id
                   (+ (pattern-variable-level pvar) 1)))
                #'(u ...) ipvars)
               catas)))))

      (define (gen-map-values proc-expr y* e n)
        (let f ([n n])
          (if (zero? n)
              #`(#,proc-expr #,e)
              (with-syntax ([(tmps ...)
                             (generate-temporaries y*)]
                            [(tmp ...)
                             (generate-temporaries y*)]
                            [e e])
                #`(let f ([e* (reverse e)]
                          [tmps '()] ...)
                    (if (null? e*)
                        (values tmps ...)
                        (let ([e (car e*)]
                              [e* (cdr e*)])
                          (let-values ([(tmp ...)
                                        #,(f (- n 1))])
                            (f e* (cons tmp tmps) ...)))))))))

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
                           (map
                            (lambda (tmp ys z)
                              (let ([n
                                     (exists
                                      (lambda (pvar)
                                        (let ([id (pattern-variable-identifier pvar)])
                                          (and (bound-identifier=? id z)
                                               (pattern-variable-level pvar))))
                                      pvars)])
                                (gen-map-values tmp ys z n)))
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
