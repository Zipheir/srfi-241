#!r6rs

;; Copyright (C) Marc Nieper-Wißkirchen (2021).  All Rights Reserved.
;; Copyright (C) Wolfgang Corcoran-Mathe (2024)

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

(import (rnrs)
        (srfi :64)
        (srfi :241 match))

;;; Examples from R. Kent Dybvig's "Using Match"

(test-group "Dybvig"
  (test-equal 3
              (match '(a 17 37)
                [(a ,x) 1]
                [(b ,x ,y) 2]
                [(a ,x ,y) 3]))

  (test-equal 629
              (match '(a 17 37)
                [(a ,x) (- x)]
                [(b ,x ,y) (+ x y)]
                [(a ,x ,y) (* x y)]))

  (test-equal '(17 37)
              (match '(a 17 37) [(a ,x* ...) x*]))

  (test-equal '(a stitch in time saves nine)
              (match '(say (a time) (stitch saves) (in nine))
                [(say (,x* ,y*) ...) (append x* y*)]))

  (test-equal '((a e h j) ((b c d) (f g) (i) ()))
              (match '((a b c d) (e f g) (h i) (j))
                [((,x* ,y** ...) ...) (list x* y**)]))

  (letrec*
   ((simple-eval
     (lambda (x)
       (match x
         [,i (guard (integer? i)) i]
         [(+ ,[x*] ...) (apply + x*)]
         [(* ,[x*] ...) (apply * x*)]
         [(- ,[x] ,[y]) (- x y)]
         [(/ ,[x] ,[y]) (/ x y)]
         [,x
          (assertion-violation 'simple-eval "invalid expression" x)]))))

    (test-equal 6 (simple-eval '(+ 1 2 3)))
    (test-equal 4 (simple-eval '(+ (- 0 1) (+ 2 3))))
    (test-assert (guard (c [(assertion-violation? c) #t])
                   (simple-eval '(- 1 2 3)))))

  (letrec*
   ((translate
     (lambda (x)
       (match x
         [(let ((,var* ,expr*) ...) ,body ,body* ...)
          `((lambda ,var* ,body ,body* ...) ,expr* ...)]
         [,x
          (assertion-violation 'translate "invalid expression" x)]))))

    (test-equal '((lambda (x y) (+ x y)) 3 4)
                (translate '(let ((x 3) (y 4)) (+ x y)))))

  (letrec* ((f
             (lambda (x)
               (match x
                 [((,a ...) (,b ...)) `((,a . ,b) ...)]))))
    (test-equal '((1 . a) (2 . b) (3 . c))
                (f '((1 2 3) (a b c))))

    (test-assert (guard (c [(assertion-violation? c) #t])
                   (f '((1 2 3) (a b))))))

  (letrec* ((g
             (lambda (x)
               (match x
                 [(,a ,b ...) `((,a ,b) ...)]))))
    (test-assert (guard (c [(assertion-violation? c) #t])
                   (g '(1 2 3 4)))))

  (letrec* ((h
             (lambda (x)
               (match x
                 [(let ([,x ,e1 ...] ...) ,b1 ,b2 ...)
                  `((lambda (,x ...) ,b1 ,b2 ...)
                    (begin ,e1 ...) ...)]))))
    (test-equal
     '((lambda (x y) (list x y))
       (begin (write 'one) 3)
       (begin (write 'two) 4))
     (h '(let ((x (write 'one) 3) (y (write 'two) 4)) (list x y)))))

  (letrec* ((k
             (lambda (x)
               (match x
                 [(foo (,x ...) ...)
                  `(list (car ,x) ... ...)]))))
    (test-equal
     '(list (car a) (car b) (car c) (car d) (car e) (car f) (car g))
     (k '(foo (a) (b c d e) () (f g)))))

  ;; TODO: More tests of this parser.
  (letrec*
   ([Prog
     (lambda (x)
       (match x
         [(program ,[Stmt -> s*] ... ,[Expr -> e])
          `(begin ,s* ... ,e)]
         [,x (assertion-violation 'parse "invalid program" x)]))]
    [Stmt
     (lambda (x)
       (match x
         [(if ,[Expr -> e] ,[Stmt -> s1] ,[Stmt -> s2])
          `(if ,e ,s1 ,s2)]
         [(set! ,v ,[Expr -> e])
          (guard (symbol? v))
          `(set! ,v ,e)]
         [,x (assertion-violation 'parse "invalid statement" x)]))]
    [Expr
     (lambda (x)
       (match x
         [,v (guard (symbol? v)) v]
         [,n (guard (integer? n)) n]
         [(if ,[e1] ,[e2] ,[e3])
          `(if ,e1 ,e2 ,e3)]
         [(,[rator] ,[rand*] ...) `(,rator ,rand* ...)]
         [,x (assertion-violation 'parse "invalid expression" x)]))])

    (test-equal '(begin 4) (Prog '(program 4)))
    (test-equal '(begin (if (f x y) (set! z 4) (set! z 5)) z)
                (Prog
                 '(program
                   (if (f x y)
                       (set! z 4)
                       (set! z 5))
                   z)))
    (test-equal '(begin ((if z f g) (if a (+ a 2) b)))
                (Prog '(program ((if z f g) (if a (+ a 2) b)))))
    (test-assert (guard (c [(assertion-violation? c) #t])
                   (Prog '(program (set! x 3)))))
    (test-assert (guard (c [(assertion-violation? c) #t])
                   (Prog '(program (set-bang x 3) 4))))
    (test-assert (guard (c [(assertion-violation? c) #t])
                   (Prog '(program (set! x 3) (set! y 2) 5.2))))
    (test-equal '(begin (set! x 3) (+ x 4))
                (Prog '(program (set! x 3) (+ x 4)))))

  ;; TODO: More tests of this parser.
  (letrec*
   ([Prog
     (lambda (x)
       (match x
         [(program ,[Stmt -> s*] ... ,[(Expr '()) -> e])
          `(begin ,s* ... ,e)]
         [,x (assertion-violation 'parse "invalid program" x)]))]
    [Stmt
     (lambda (x)
       (match x
         [(if ,[(Expr '()) -> e] ,[Stmt -> s1] ,[Stmt -> s2])
          `(if ,e ,s1 ,s2)]
         [(set! ,v ,[(Expr '()) -> e])
          (guard (symbol? v))
          `(set! ,v ,e)]
         [,x (assertion-violation 'parse "invalid statement" x)]))]
    [Expr
     (lambda (env)
       (lambda (x)
         (match x
           [,v (guard (symbol? v)) v]
           [,n (guard (integer? n)) n]
           [(if ,[e1] ,[e2] ,[e3])
            (guard (not (memq 'if env)))
            `(if ,e1 ,e2 ,e3)]
           [(let ([,v ,[e]]) ,[(Expr (cons v env)) -> body])
            (guard (not (memq 'let env)) (symbol? v))
            `(let ([,v ,e]) ,body)]
           [(,[rator] ,[rand*] ...)
            `(call ,rator ,rand* ...)]
           [,x (assertion-violation 'parse "invalid expression" x)])))])

    (test-equal '(begin 4) (Prog '(program 4)))
    (test-equal '(begin (if (call f x y) (set! z 4) (set! z 5)) z)
                (Prog
                 '(program
                   (if (f x y)
                       (set! z 4)
                       (set! z 5))
                   z)))
    (test-equal '(begin (call (if z f g) (if a (call + a 2) b)))
                (Prog '(program ((if z f g) (if a (+ a 2) b)))))
    (test-equal '(begin (set! x 5)
                        (if (let ((v 10)) (call even? (call + x v)))
                            1
                            2))
                (Prog '(program
                        (set! x 5)
                        (if (let ((v 10))
                              (even? (+ x v)))
                            1
                            2))))
    (test-assert (guard (c [(assertion-violation? c) #t])
                   (Prog '(program (set! x 3)))))
    (test-assert (guard (c [(assertion-violation? c) #t])
                   (Prog '(program (set-bang x 3) 4))))
    (test-assert (guard (c [(assertion-violation? c) #t])
                   (Prog '(program (set! x 3) (set! y 2) 5.2))))
    (test-assert (guard (c [(assertion-violation? c) #t])
                   (Prog '(program (let ((if 1)) (if 1 2 3))))))
    (test-assert (guard (c [(assertion-violation? c) #t])
                   (Prog '(program (let ((let 1))
                                     (let ((x 2))
                                       x))))))
    (test-equal '(begin
                  (let ([if (if x list values)])
                    (call if 1 2 3)))
                (Prog
                 '(program
                    (let ([if (if x list values)])
                      (if 1 2 3))))))

  (letrec* ((split
             (lambda (ls)
               (match ls
                 [() (values '() '())]
                 [(,x) (values `(,x) '())]
                 [(,x ,y . ,[odds evens])
                  (values (cons x odds)
                          (cons y evens))]))))

    (test-equal '((a c e) (b d f))
                (call-with-values
                 (lambda ()
                   (split '(a b c d e f)))
                 list)))
  )

(test-group "Lists"
  (test-assert (match '() [() #t] [,_ #f]))
  (test-assert (match '(1) [() #f] [,_ #t]))
  (test-assert (match '(1) [(1 . ()) #t] [,_ #f]))
  (test-assert (match '(1 2) [(1 . (2)) #t] [,_ #f]))
  (test-assert (match '(1 . 2) [(1 . (2)) #f] [,_ #t]))
  (test-assert (match '(1 . 2) [(1 . 2) #t] [,_ #f]))

  (test-assert (match '(3) [(1 ... 3) #t] [,_ #f]))
  (test-assert (match '(1 3) [(1 ... 3) #t] [,_ #f]))
  (test-assert (match '(1 1 1 3) [(1 ... 3) #t] [,_ #f]))
  (test-assert (match '(2 3) [(1 ... 3) #f] [,_ #t]))
  (test-assert (match '(1 2 3) [(1 2 ... 3) #t] [,_ #f]))
  (test-assert (match '(1 2 3 4) [(1 2 ... 3) #f] [,_ #t]))
  (test-assert (match '(1 2 3 4) [(1 2 ... 3 4) #t] [,_ #f]))
  (test-assert (match '(1 3 4) [(1 2 ... 3 4) #t] [,_ #f]))
  (test-assert (match '(1 2 2 2 3 4) [(1 2 ... 3 4) #t] [,_ #f]))
  (test-assert (match '(1 2 2 2 3 4) [(1 2 ... . ,_) #f] [,_ #t]))
  (test-assert (match '(1 2 2 2 3 . 4) [(1 2 ... 3 . 4) #t] [,_ #f]))

  (test-assert (match '() [((1 ...) ...) #t] [,_ #f]))
  (test-assert (match '((1)) [((1 ...) ...) #t] [,_ #f]))
  (test-assert (match '((1 1) (1) ()) [((1 ...) ...) #t] [,_ #f]))
  (test-assert (match '(((1))) [((1 ...) ...) #f] [,_ #t]))
  (test-assert (match '(((1) (1 1))) [(((1 ...) ...) ...) #t] [,_ #f]))
  (test-assert (match '(((1) (1 2))) [(((1 ...) ...) ...) #f] [,_ #t]))

  (test-eqv 1 (match '(1) [(,x) x] [,_ #f]))
  (test-eqv 6 (match '(3 2) [(,x ,y) (* x y)] [,_ #f]))
  (test-eqv 6 (match '(3 . 2) [(,x . ,y) (* x y)] [,_ #f]))
  (test-equal '(2 1) (match '(1 2) [(,x ,y) (list y x)] [,_ '()]))
  (test-equal '()
              (match '(1 2)
                [(,_ ... . ,x) x]  ; final cdr
                [,_ #f]))
  (test-equal '(1 (2 2) 3 ())
              (match '(1 2 2 3)
                [(,x ,y ... ,z . ,u) (list x y z u)]
                [,_ '()]))
  (test-equal '(1 (2 2) 3 4)
              (match '(1 2 2 3 . 4)
                [(,x ,y ... ,z . ,u) (list x y z u)]
                [,_ '()]))
  (test-equal '(1 () 3 ())
              (match '(1 3)
                [(,x ,y ... ,z . ,u) (list x y z u)]
                [,_ '()]))
  (test-equal '(1 2 (2) 3 ())
              (match '(1 2 2 3)
                [(,x ,y ,z ... ,u . ,v) (list x y z u v)]
                [,_ '()]))
  (test-equal '(1 2 (2) 3 4)
              (match '(1 2 2 3 . 4)
                [(,x ,y ,z ... ,u . ,v) (list x y z u v)]
                [,_ '()]))

  (test-assert (match '(a)
                 [(,x) (guard (integer? x)) #f]
                 [(,x) (guard (symbol? x)) #t]))

  (test-equal '(a b c d)
              (match '(((a b c d)))
                [(((,x ...))) x]
                [,_ '()]))
  (test-equal '((a b c d))
              (match '(((a b c d)))
                [(((,x ...) ...)) x]
                [,_ '()]))
  (test-equal '(((a b c d)))
              (match '(((a b c d)))
                [(((,x ...) ...) ...) x]
                [,_ '()]))
  (test-equal '((a b c) (d e f))
              (match '((a b c) (d e f))
                [((,x ...) ...) x]
                [,_ '()]))
  (test-equal '((a b c) (d e f))
              (match '((1 a b c) (1 d e f))
                [((1 ,x ...) ...) x]
                [,_ '()]))
  )

(test-group "Wildcards"
  ;;; Wildcard patterns. These are invalid in MNW's original matcher.

  (test-assert (match '(1 2) [(,_ ,_) #t] [,_ #f]))
  (test-assert (match '(1 2) [(,_ . ,_) #t] [,_ #f]))
  (test-assert (match '(1 2) [(,_ ,_ ,_) #f] [,_ #t]))
  (test-assert (match '(1 2 3 4) [(,_ ,_ ,_) #f] [,_ #t]))
  (test-assert (match '(1 2 3 4) [(,_ ,_ ,_ ,_) #t] [,_ #f]))

  (test-equal '(a b c)
              (match '((1 a m) (2 b n) (3 c o))
                [((,_ ,x ,_) ...) x]
                [,_ '()]))

  ;; _ can't be used as a cata variable.
  (test-assert (guard (c [(assertion-violation? c) #t])
                 (match '(1 2)
                   [,k (guard (integer? k)) k]
                   [(,[_] ,[x]) (+ _ x)])))
  )

(test-group "Vectors"
  (test-assert (match '#() [#() #t] [,_ #f]))
  (test-assert (match '#(1) [#() #f] [,_ #t]))
  (test-assert (match '#() [#(1) #f] [,_ #t]))
  (test-assert (match '#(1) [#(1) #t] [,_ #f]))
  (test-assert (match '#(1 2) [#(1) #f] [,_ #t]))
  (test-assert (match '#(1) [#(1 2) #f] [,_ #t]))
  (test-assert (match '#(1 2) [#(1 2) #t] [,_ #f]))

  (test-equal '(2 1)
              (match '#(#(1) #(2))
                [#(#(,_) #(,_)) (list 2 1)]
                [,_ '()]))
  (test-equal '(2 1)
              (match '#(1 2) [#(,x ,y) (list y x)] [,_ '()]))
  (test-equal '((4 3) 2 1)
              (match '#(1 2 (3 4))
                [#(,x ,y (,u ,v)) (list (list v u) y x)]
                [,_ '()]))

  (letrec*
   ([binary-vector-eval
     (lambda (expr)
       (match expr
         [,k (guard (number? k)) k]
         [#(+ ,[a] ,[b]) (+ a b)]
         [#(- ,[a] ,[b]) (- a b)]
         [#(* ,[a] ,[b]) (* a b)]
         [#(/ ,[a] ,[b]) (/ a b)]
         [,_ (assertion-violation 'binary-vector-eval
                                  "invalid expression"
                                  expr)]))])
    (test-eqv 0 (binary-vector-eval 0))
    (test-eqv 4 (binary-vector-eval '#(+ 1 3)))
    (test-eqv 7 (binary-vector-eval '#(+ #(- 7 6) #(/ 12 2))))
    (test-eqv 6 (binary-vector-eval '#(- #(* 5 6) #(+ 20 #(/ 8 2))))))
  )

(test-group "Vectors + Ellipsis"
  (test-assert (match '#() [#(,_ ...) #t] [,_ #f]))
  (test-assert (match '#(1) [#(,_ ...) #t] [,_ #f]))
  (test-assert (match '#(1) [#(1 ...) #t] [,_ #f]))
  (test-assert (match '#(1 2 3) [#(1 ...) #f] [,_ #t]))
  (test-assert (match '#(1 1 3) [#(1 ... 3) #t] [,_ #f]))
  (test-assert (match '#(1 1 3) [#(1 1 ... 3) #t] [,_ #f]))
  (test-assert (match '#(1 1 1 1 3) [#(1 1 ... 3) #t] [,_ #f]))
  (test-assert (match '#(1 1 2 1 3) [#(1 1 ... 3) #f] [,_ #t]))

  (test-assert (null? (match '#(1 3) [#(,x ... 1 3) x] [,_ #f])))
  (test-assert (null? (match '#(1 3) [#(1 ,x ... 3) x] [,_ #f])))
  (test-assert (null? (match '#(1 3) [#(1 3 ,x ...) x] [,_ #f])))

  (test-equal '(1 1)
              (match '#(1 1 3)
                [#(,x ... 3) x]
                [,_ '()]))
  (test-equal '(1 2)
              (match '#(1 2 3)
                [#(,x ... 3) x]
                [,_ '()]))
  (test-equal '(1 2)
              (match '#(0 1 2 3)
                [#(0 ,x ... 3) x]
                [,_ '()]))
  (test-equal '((1 1) 3)
              (match '#(1 1 1 1 3)
                [#(1 ,x ... 1 ,y) (list x y)]
                [,_ '()]))
  (test-equal '((a b c) (1 2 3))
              (match '#((a 1) (b 2) (c 3))
                [#((,x ,k) ...) (list x k)]
                [,_ '()]))

  (letrec*
   ((vector-simple-eval
     (lambda (x)
       (match x
         [,i (guard (integer? i)) i]
         [#(+ ,[x*] ...) (apply + x*)]
         [#(* ,[x*] ...) (apply * x*)]
         [#(- ,[x] ,[y]) (- x y)]
         [#(/ ,[x] ,[y]) (/ x y)]
         [,x
          (assertion-violation 'simple-eval "invalid expression" x)]))))

    (test-equal 6 (vector-simple-eval '#(+ 1 2 3)))
    (test-equal 4 (vector-simple-eval '#(+ #(- 0 1) #(+ 2 3))))
    (test-equal 22
                (vector-simple-eval '#(* #(/ 4 2) #(+ 3 4 #(- 5 1)))))
    (test-equal 1 (vector-simple-eval '#(+ #(*) #(+))))
    (test-assert (guard (c [(assertion-violation? c) #t])
                   (vector-simple-eval '#(- 1 2 3))))
    (test-assert (guard (c [(assertion-violation? c) #t])
                   (vector-simple-eval '#(/ #(- 4.3 1) 2)))))

  )

;;; Extra tests

(test-group "Extra"
  (test-assert (match 'a
                 [(,x) #f]
                 [,_ #t]))

  (test-assert (match 'else
                 [else #t]))

  (test-assert (guard (c [(assertion-violation? c) #t])
                 (match 'whatever
                   [else #f])))
  )

;; Local Variables:
;; mode: scheme
;; End:
