;;; Copyright © Wolfgang Corcoran-Mathe (2024)
;;;
;;; Permission is hereby granted, free of charge, to any person obtaining a
;;; copy of this software and associated documentation files (the
;;; "Software"), to deal in the Software without restriction, including
;;; without limitation the rights to use, copy, modify, merge, publish,
;;; distribute, sublicense, and/or sell copies of the Software, and to
;;; permit persons to whom the Software is furnished to do so, subject to
;;; the following conditions:
;;;
;;; The above copyright notice and this permission notice shall be included
;;; in all copies or substantial portions of the Software.
;;;
;;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
;;; OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
;;; MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
;;; IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
;;; CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
;;; TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
;;; SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

(library (srfi :241 match matchers)
  (export make-matcher matcher-generator matcher-pattern-variables
          matcher-cata-variables unit-matcher matcher-sequence
          make-simple-matcher)
  (import (rnrs base (6))
          (rnrs control (6))
          (rnrs lists (6))
          (rnrs records syntactic (6)))

  (define-record-type (matcher make-matcher matcher?)
    (fields generator     ; Procedure of one continuation argument
            pattern-variables
            cata-variables))

  ;;; Left & right unit of matcher-sequence.
  (define unit-matcher (make-matcher (lambda (k) (k)) '() '()))

  ;;; Fold together a sequence of matchers, chaining
  ;;; the code generators and appending the variable lists.
  (define (matcher-sequence . matchers)
    (fold-right %matcher-sequence-2 unit-matcher matchers))

  (define (%matcher-sequence-2 m1 m2)
    (let ([gen1 (matcher-generator m1)] [gen2 (matcher-generator m2)])
      (make-matcher
       (lambda (gen-more) (gen1 (lambda () (gen2 gen-more))))
       (append (matcher-pattern-variables m1)
               (matcher-pattern-variables m2))
       (append (matcher-cata-variables m1)
               (matcher-cata-variables m2)))))

  ;;; Convenience constructor for matchers without bindings.
  (define (make-simple-matcher proc)
    (make-matcher proc '() '()))

  )
