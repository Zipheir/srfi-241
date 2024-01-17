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

(library (srfi :241 match helpers)
  (export make-identifier-hashtable invoke ellipsis? underscore? length+
          append-n-map fold-right/two-values list/mv check-no-ellipses)
  (import (rnrs))

  (define (identifier-hash id)
    (assert (identifier? id))
    (symbol-hash (syntax->datum id)))

  (define (make-identifier-hashtable)
    (make-hashtable identifier-hash bound-identifier=?))

  (define (invoke f) (f))

  (define (ellipsis? x)
    (and (identifier? x)
         (free-identifier=? x #'(... ...))))

  (define (underscore? x)
    (and (identifier? x)
         (free-identifier=? x #'_)))

  (define (length+ x)
    (let f ([x x] [y x] [n 0])
      (if (pair? x)
          (let ([x (cdr x)]
                [n (+ n 1)])
            (if (pair? x)
                (let ([x (cdr x)]
                      [y (cdr y)]
                      [n (+ n 1)])
                  (and (not (eq? x y))
                       (f x y n)))
                n))
          n)))

  ;; Flatten the arguments n times, then map *proc* over the
  ;; remaining list.
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

  (define (fold-right/two-values f z1 z2 xs)
    (if (null? xs)
        (values z1 z2)
        (let-values ([(a b) (fold-right/two-values f z1 z2 (cdr xs))])
          (f a b (car xs)))))

  ;; Simplified version of SRFI 210 form.
  (define-syntax list/mv
    (syntax-rules ()
      [(_ producer)
       (let-values ([vs producer]) vs)]))

  (define (check-no-ellipses who form pattern)
    (when (if (list? pattern)
              (exists ellipsis? pattern)
              (ellipsis? pattern))
      (syntax-violation who "extra ellipses in pattern"
                        pattern form)))
  )
