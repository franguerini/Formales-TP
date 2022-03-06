(ns tp.core-test
  (:require [clojure.test :refer :all]
            [tp.core :refer :all]))

; user=> (fnc-sumar ())
; 0
; user=> (fnc-sumar '(3))
; 3
; user=> (fnc-sumar '(3 4))
; 7
; user=> (fnc-sumar '(3 4 5))
; 12
; user=> (fnc-sumar '(3 4 5 6))
; 18
; user=> (fnc-sumar '(A 4 5 6))
; (;ERROR: +: Wrong type in arg1 A)
; user=> (fnc-sumar '(3 A 5 6))
; (;ERROR: +: Wrong type in arg2 A)
; user=> (fnc-sumar '(3 4 A 6))
; (;ERROR: +: Wrong type in arg2 A)
(deftest fnc-sumar-test
  (testing "fnc-sumar tests:"
      (is (= 0 (fnc-sumar ())))
      (is (= 3 (fnc-sumar '(3))))
      (is (= 7 (fnc-sumar '(3 4))))
      (is (= 12 (fnc-sumar '(3 4 5))))
      (is (= 18 (fnc-sumar '(3 4 5 6))))
      (is (= -2 (fnc-sumar '(-5 1 2))))
      (is (= 0 (fnc-sumar '(-5 5))))
      (is (= 0 (fnc-sumar '(0))))
      (is (= 0 (fnc-sumar '(1 2 3 4 5 -15))))
      (is (= (list (symbol ";ERROR:") (symbol "+:") 'Wrong 'type 'in 'arg1 'A)) (fnc-sumar '(A 3 4 5 6)))
      (is (= (list (symbol ";ERROR:") (symbol "+:") 'Wrong 'type 'in 'arg2 'A)) (fnc-sumar '(3 A 5 6)))
      (is (= (list (symbol ";ERROR:") (symbol "+:") 'Wrong 'type 'in 'arg2 'A)) (fnc-sumar '(3 4 A 6)))
  )
)

; user=> (fnc-restar ())
; (;ERROR: -: Wrong number of args given)
; user=> (fnc-restar '(3))
; -3
; user=> (fnc-restar '(3 4))
; -1
; user=> (fnc-restar '(3 4 5))
; -6
; user=> (fnc-restar '(3 4 5 6))
; -12
; user=> (fnc-restar '(A 4 5 6))
; (;ERROR: -: Wrong type in arg1 A)
; user=> (fnc-restar '(3 A 5 6))
; (;ERROR: -: Wrong type in arg2 A)
; user=> (fnc-restar '(3 4 A 6))
; (;ERROR: -: Wrong type in arg2 A)
(deftest fnc-restar-test
  (testing "fnc-restar tests:"
      (is (= (list (symbol ";ERROR:") (symbol "-:") (symbol "Wrong") (symbol "numbers") (symbol "of") (symbol "args") (symbol "given") (fnc-restar ()))))
      (is (= -3 (fnc-restar '(3))))
      (is (= -1 (fnc-restar '(3 4))))
      (is (= -6 (fnc-restar '(3 4 5))))
      (is (= -12 (fnc-restar '(3 4 5 6))))
      (is (= 0 (fnc-restar '(0))))
      (is (= (list (symbol ";ERROR:") (symbol "-:") 'Wrong 'type 'in 'arg1 'A) (fnc-restar '(A 3 4 5 6))))
      (is (= (list (symbol ";ERROR:") (symbol "-:") 'Wrong 'type 'in 'arg2 'A) (fnc-restar '(3 A 5 6))))
      (is (= (list (symbol ";ERROR:") (symbol "-:") 'Wrong 'type 'in 'arg2 'A) (fnc-restar '(3 4 A 6))))
  )
)

; user=> (fnc-menor ())
; #t
; user=> (fnc-menor '(1))
; #t
; user=> (fnc-menor '(1 2))
; #t
; user=> (fnc-menor '(1 2 3))
; #t
; user=> (fnc-menor '(1 2 3 4))
; #t
; user=> (fnc-menor '(1 2 2 4))
; #f
; user=> (fnc-menor '(1 2 1 4))
; #f
; user=> (fnc-menor '(A 1 2 4))
; (;ERROR: <: Wrong type in arg1 A)
; user=> (fnc-menor '(1 A 1 4))
; (;ERROR: <: Wrong type in arg2 A)
; user=> (fnc-menor '(1 2 A 4))
; (;ERROR: <: Wrong type in arg2 A)
(deftest fnc-menor-test
  (testing "fnc-menor tests:"
      (is (= (symbol "#t") (fnc-menor ())))
      (is (= (symbol "#t") (fnc-menor '(1))))
      (is (= (symbol "#t") (fnc-menor '(1 2 3))))
      (is (= (symbol "#t") (fnc-menor '(1 2 3 4))))
      (is (= (symbol "#f") (fnc-menor '(1 2 1 4))))
      (is (= (symbol "#t") (fnc-menor '(1 2 3 4 5 6 7 8 9 10 11))))
      (is (= (symbol "#f") (fnc-menor '(1 -1))))
      (is (= (list (symbol ";ERROR:") (symbol "<:") 'Wrong 'type 'in 'arg1 'A) (fnc-menor '(A 1 2 4))))
      (is (= (list (symbol ";ERROR:") (symbol "<:") 'Wrong 'type 'in 'arg2 'A) (fnc-menor '(1 A 2 4))))
      (is (= (list (symbol ";ERROR:") (symbol "<:") 'Wrong 'type 'in 'arg2 'A) (fnc-menor '(1 2 A 4))))
  )
)

; user=> (fnc-mayor ())
; #t
; user=> (fnc-mayor '(1))
; #t
; user=> (fnc-mayor '(2 1))
; #t
; user=> (fnc-mayor '(3 2 1))
; #t
; user=> (fnc-mayor '(4 3 2 1))
; #t
; user=> (fnc-mayor '(4 2 2 1))
; #f
; user=> (fnc-mayor '(4 2 1 4))
; #f
; user=> (fnc-mayor '(A 3 2 1))
; (;ERROR: >: Wrong type in arg1 A)
; user=> (fnc-mayor '(3 A 2 1))
; (;ERROR: >: Wrong type in arg2 A)
; user=> (fnc-mayor '(3 2 A 1))
; (;ERROR: >: Wrong type in arg2 A)
(deftest fnc-mayor-test
  (testing "fnc-mayor tests:"
      (is (= (symbol "#t") (fnc-mayor ())))
      (is (= (symbol "#t") (fnc-mayor '(1))))
      (is (= (symbol "#t") (fnc-mayor '(2 1))))
      (is (= (symbol "#t") (fnc-mayor '(3 2 1))))
      (is (= (symbol "#f") (fnc-mayor '(4 2 2 1))))
      (is (= (symbol "#f") (fnc-mayor '(4 2 1 4))))
      (is (= (symbol "#t") (fnc-mayor '(10 9 8 7 6 5 4 3 2 1))))
      (is (= (symbol "#t") (fnc-mayor '(-10 -100 -1000))))
      (is (= (symbol "#f") (fnc-mayor '(-10 0 10))))
      (is (= (list (symbol ";ERROR:") (symbol ">:") 'Wrong 'type 'in 'arg1 'A) (fnc-mayor '(A 3 2 1))))
      (is (= (list (symbol ";ERROR:") (symbol ">:") 'Wrong 'type 'in 'arg2 'A) (fnc-mayor '(3 A 2 1))))
      (is (= (list (symbol ";ERROR:") (symbol ">:") 'Wrong 'type 'in 'arg2 'A) (fnc-mayor '(3 2 A 1))))
  )
)

; user=> (fnc-mayor ())
; #t
; user=> (fnc-mayor '(1))
; #t
; user=> (fnc-mayor '(2 1))
; #t
; user=> (fnc-mayor '(3 2 1))
; #t
; user=> (fnc-mayor '(4 3 2 1))
; #t
; user=> (fnc-mayor '(4 2 2 1))
; #f
; user=> (fnc-mayor '(4 2 1 4))
; #f
; user=> (fnc-mayor '(A 3 2 1))
; (;ERROR: >: Wrong type in arg1 A)
; user=> (fnc-mayor '(3 A 2 1))
; (;ERROR: >: Wrong type in arg2 A)
; user=> (fnc-mayor '(3 2 A 1))
; (;ERROR: >: Wrong type in arg2 A)
(deftest fnc-mayor-o-igual-test
  (testing "fnc-mayor-o-igual tests:"
      (is (= (symbol "#t") (fnc-mayor-o-igual ())))
      (is (= (symbol "#t") (fnc-mayor-o-igual '(1))))
      (is (= (symbol "#t") (fnc-mayor-o-igual '(2 1))))
      (is (= (symbol "#t") (fnc-mayor-o-igual '(3 2 1))))
      (is (= (symbol "#t") (fnc-mayor-o-igual '(4 2 2 1))))
      (is (= (symbol "#f") (fnc-mayor-o-igual '(4 2 1 4))))
      (is (= (symbol "#t") (fnc-mayor-o-igual '(4 4 4 4))))
      (is (= (symbol "#t") (fnc-mayor-o-igual '(10 9 8 7 6 5 4 3 2 1 0 -1))))
      (is (= (symbol "#t") (fnc-mayor-o-igual '(-10 -100 -1000))))
      (is (= (list (symbol ";ERROR:") (symbol ">=:") 'Wrong 'type 'in 'arg1 'A) (fnc-mayor-o-igual '(A 3 2 1))))
      (is (= (list (symbol ";ERROR:") (symbol ">=:") 'Wrong 'type 'in 'arg2 'A) (fnc-mayor-o-igual '(3 A 2 1))))
      (is (= (list (symbol ";ERROR:") (symbol ">=:") 'Wrong 'type 'in 'arg2 'A) (fnc-mayor-o-igual '(3 2 A 1))))
  )
)

; user=> (fnc-append '( (1 2) (3) (4 5) (6 7)))
; ; (1 2 3 4 5 6 7)
; ; user=> (fnc-append '( (1 2) 3 (4 5) (6 7)))
; ; (;ERROR: append: Wrong type in arg 3)
; ; user=> (fnc-append '( (1 2) A (4 5) (6 7)))
; ; (;ERROR: append: Wrong type in arg A)
(deftest fnc-append-test
  (testing "fnc-append tests:"
      (is (= '(1 2 3 4 5 6 7) (fnc-append '((1 2) (3) (4 5) (6 7)))))
      (is (= '(1 2 3 4 5 A B) (fnc-append '((1 2) (3) (4 5) (A B)))))
      (is (= '(A B C D E F G H) (fnc-append '((A B C D) (E) (F G) (H)))))
      (is (= '(A B (C D) E (F) G H) (fnc-append '((A B (C D)) (E) ((F) G) (H)))))
      (is (= (list (symbol ";ERROR:") (symbol "append:") 'Wrong 'type 'in 'arg '3) (fnc-append '( (1 2) 3 (4 5) (6 7)))))
      (is (= (list (symbol ";ERROR:") (symbol "append:") 'Wrong 'type 'in 'arg 'A) (fnc-append '( (1 2) A (4 5) (6 7)))))
  )
)


; user=> (error? (list (symbol ";ERROR:") 'mal 'hecho))
; true
; user=> (error? (list 'mal 'hecho))
; false
; user=> (error? (list (symbol ";WARNING:") 'mal 'hecho))
; true
(deftest error?-test
  (testing "error? tests:"
      (is (= true (error? (list (symbol ";ERROR:") 'mal 'hecho))))
      (is (= false (error? (list 'mal 'hecho))))
      (is (= true (error? (list (symbol ";WARNING:") 'mal 'hecho))))
      (is (= false (error? '(1 2 3))))
  )
)


; user=> (fnc-equal? ())
; #t
; user=> (fnc-equal? '(A))
; #t
; user=> (fnc-equal? '(A a))
; #t
; user=> (fnc-equal? '(A a A))
; #t
; user=> (fnc-equal? '(A a A a))
; #t
; user=> (fnc-equal? '(A a A B))
; #f
; user=> (fnc-equal? '(1 1 1 1))
; #t
; user=> (fnc-equal? '(1 1 2 1))
; #f
(deftest fnc-equal?-test
  (testing "fnc-equal tests:"
      (is (= (symbol "#t") (fnc-equal? ())))
      (is (= (symbol "#t") (fnc-equal? '(A))))
      (is (= (symbol "#f") (fnc-equal? '(A B C))))
      (is (= (symbol "#t") (fnc-equal? '(A a A))))
      (is (= (symbol "#f") (fnc-equal? '(A a A B))))
      (is (= (symbol "#t") (fnc-equal? '(1 1 1 1))))
      (is (= (symbol "#f") (fnc-equal? '(1 1 2 1))))
      (is (= (symbol "#f") (fnc-equal? '((1 1) (2 1)))))
      (is (= (symbol "#t") (fnc-equal? '((1 1) (1 1)))))
      (is (= (symbol "#t") (fnc-equal? '((A A (B) (C D)) (A A (B) (C D)) (A A (B) (C D)) (A A (B) (C D))))))
      (is (= (symbol "#f") (fnc-equal? '((A A B (C D)) (A A (B) (C D))))))
  )
)


; user=> (verificar-parentesis "(hola 'mundo")
; 1
; user=> (verificar-parentesis "(hola '(mundo)))")
; -1
; user=> (verificar-parentesis "(hola '(mundo) () 6) 7)")
; -1
; user=> (verificar-parentesis "(hola '(mundo) () 6) 7) 9)")
; -1
; user=> (verificar-parentesis "(hola '(mundo) )")
; 0
(deftest verificar-parentesis-test
  (testing "verificar-parentesis tests:"
      (is (= 1 (verificar-parentesis "(hola 'mundo")))
      (is (= -1 (verificar-parentesis "(hola '(mundo)))")))
      (is (= -1 (verificar-parentesis "(hola '(mundo) () 6) 7)")))
      (is (= -1 (verificar-parentesis "(hola '(mundo) () 6) 7) 9)")))
      (is (= 0 (verificar-parentesis "(hola '(mundo) )")))
      (is (= -1 (verificar-parentesis "(hola '(mundo) ))")))
      (is (= 5 (verificar-parentesis "(((((hola")))
      (is (= 1 (verificar-parentesis "(((((hola))))")))
      (is (= 0 (verificar-parentesis "(((((hola)))))")))
      (is (= -1 (verificar-parentesis "(((((hola))))))")))
  )
)

; user=> (igual? 'if 'IF)
; true
; user=> (igual? 'if 'if)
; true
; user=> (igual? 'IF 'IF)
; true
; user=> (igual? 'IF "IF")
; false
; user=> (igual? 6 "6")
; false
(deftest igual?-test
  (testing "igual? tests:"
    (is (= true (igual? 'if 'IF)))
    (is (= true (igual? 'if 'if)))
    (is (= true (igual? 'IF 'IF)))
    (is (= true (igual? 'define 'define)))
    (is (= true (igual? 10 10)))
    (is (= false (igual? 6 "6")))
    (is (= false (igual? 1000 "1000")))
    (is (= true (igual? 0 0)))
    (is (= false (igual? "0" 0)))
    (is (= true (igual? false false)))
    (is (= false (igual? true false)))
    (is (= true (igual? 'igual? 'IGUAL?)))
    (is (= true (igual? "TesT" "test")))
  )
)

; user=> (evaluar-escalar 32 '(x 6 y 11 z "hola"))
; (32 (x 6 y 11 z "hola"))
; user=> (evaluar-escalar "chau" '(x 6 y 11 z "hola"))
; ("chau" (x 6 y 11 z "hola"))
; user=> (evaluar-escalar 'y '(x 6 y 11 z "hola"))
; (11 (x 6 y 11 z "hola"))
; user=> (evaluar-escalar 'z '(x 6 y 11 z "hola"))
; ("hola" (x 6 y 11 z "hola"))
; user=> (evaluar-escalar 'n '(x 6 y 11 z "hola"))
; ((;ERROR: unbound variable: n) (x 6 y 11 z "hola"))
(deftest evaluar-escalar-test
  (testing "evaluar-escalar tests:"
    (is (= '(32 (x 6 y 11 z "hola")) (evaluar-escalar 32 '(x 6 y 11 z "hola"))))
    (is (= '("chau" (x 6 y 11 z "hola")) (evaluar-escalar "chau" '(x 6 y 11 z "hola"))))
    (is (= '(11 (x 6 y 11 z "hola")) (evaluar-escalar 'y '(x 6 y 11 z "hola"))))
    (is (= '("hola" (x 6 y 11 z "hola")) (evaluar-escalar 'z '(x 6 y 11 z "hola"))))
    (is (= (list (symbol ";ERROR:") 'unbound (symbol "variable:") 'n) (evaluar-escalar 'n '(x 6 y 11 z "hola"))))
  )
)

; user=> (proteger-bool-en-str "(or #F #f #t #T)")
; "(or %F %f %t %T)"
; user=> (proteger-bool-en-str "(and (or #F #f #t #T) #T)")
; "(and (or %F %f %t %T) %T)"
; user=> (proteger-bool-en-str "")
; ""
(deftest proteger-bool-en-str-test
  (testing "proteger-bool-en-str tests:"
    (is (= "(or %F %f %t %T)" (proteger-bool-en-str "(or #F #f #t #T)")))
    (is (= "(and (or %F %f %t %T) %T)" (proteger-bool-en-str "(and (or #F #f #t #T) #T)")))
    (is (= "" (proteger-bool-en-str "")))
  )
)

; user=> (restaurar-bool (read-string (proteger-bool-en-str "(and (or #F #f #t #T) #T)")))
; (and (or #F #f #t #T) #T)
; user=> (restaurar-bool (read-string "(and (or %F %f %t %T) %T)") )
; (and (or #F #f #t #T) #T)
(deftest restaurar-bool-test
  (testing "restaurar-bool tests:"
    (is (= (list 'and (list 'or (symbol "#F") (symbol "#F") (symbol "#T") (symbol "#T")) (symbol "#T")) (restaurar-bool (read-string (proteger-bool-en-str "(and (or #F #f #t #T) #T)")))))
    (is (= (list 'and (list 'or (symbol "#F") (symbol "#F") (symbol "#T") (symbol "#T")) (symbol "#T")) (restaurar-bool (read-string "(and (or %F %f %t %T) %T)"))))
  )
)

; user=> (actualizar-amb '(a 1 b 2 c 3) 'd 4)
; (a 1 b 2 c 3 d 4)
; user=> (actualizar-amb '(a 1 b 2 c 3) 'b 4)
; (a 1 b 4 c 3)
; user=> (actualizar-amb '(a 1 b 2 c 3) 'b (list (symbol ";ERROR:") 'mal 'hecho))
; (a 1 b 2 c 3)
; user=> (actualizar-amb () 'b 7)
; (b 7)
(deftest actualizar-amb-test
  (testing "actualizar-amb tests:"
    (is (= '(a 1 b 2 c 3 d 4) (actualizar-amb  '(a 1 b 2 c 3) 'd 4)))
    (is (= '(a 1 b 4 c 3) (actualizar-amb '(a 1 b 2 c 3) 'b 4)))
    (is (= '(a 1 b 2 c 3) (actualizar-amb  '(a 1 b 2 c 3) 'b (list (symbol ";ERROR:") 'mal 'hecho))))
    (is (= '(b 7) (actualizar-amb () 'b 7)))
  )
)

; user=> (evaluar-define '(define x 2) '(x 1))
; (#<unspecified> (x 2))
; user=> (evaluar-define '(define (f x) (+ x 1)) '(x 1))
; (#<unspecified> (x 1 f (lambda (x) (+ x 1))))
; user=> (evaluar-define '(define) '(x 1))
; ((;ERROR: define: missing or extra expression (define)) (x 1))
; user=> (evaluar-define '(define x) '(x 1))
; ((;ERROR: define: missing or extra expression (define x)) (x 1))
; user=> (evaluar-define '(define x 2 3) '(x 1))
; ((;ERROR: define: missing or extra expression (define x 2 3)) (x 1))
; user=> (evaluar-define '(define ()) '(x 1))
; ((;ERROR: define: missing or extra expression (define ())) (x 1))
; user=> (evaluar-define '(define () 2) '(x 1))
; ((;ERROR: define: bad variable (define () 2)) (x 1))
; user=> (evaluar-define '(define 2 x) '(x 1))
; ((;ERROR: define: bad variable (define 2 x)) (x 1))
"Evalua una expresion `define`. Devuelve una lista con el resultado y un ambiente actualizado con la definicion."
(deftest evaluar-define-test
  (testing "evaluar-define tests:"
    (is (= (list (symbol "#<unspecified>") '(x 2)) (evaluar-define '('define x 2) '(x 1))))
    (is (= (list (list (symbol ";ERROR:") (symbol "define:") 'missing 'or 'extra 'expression (symbol "define")) '(x 1))) (evaluar-define '(define) '(x 1)))
    (is (= (list (list (symbol ";ERROR:") (symbol "define:") 'missing 'or 'extra 'expression '(define x)) '(x 1)) (evaluar-define '(define x) '(x 1))))
    (is (= (list (list (symbol ";ERROR:") (symbol "define:") 'bad 'variable (list (symbol "define") 2 'x)) '(x 1)) (evaluar-define '(define 2 x) '(x 1))))
    (is (= (list (list (symbol ";ERROR:") (symbol "define:") 'missing 'or 'extra 'expression (list (symbol "define") 'x '2 '3)) '(x 1)) (evaluar-define '(define x 2 3) '(x 1))))
    (is (= (list (list (symbol ";ERROR:") (symbol "define:") 'missing 'or 'extra 'expression (list (symbol "define") '())) '(x 1)) (evaluar-define '(define ()) '(x 1))))
    (is (= (list (list (symbol ";ERROR:") (symbol "define:") 'bad 'variable (list (symbol "define") (list 2) 'x)) '(x 1)) (evaluar-define (list 'define (list 2) 'x) '(x 1))))
    (is (= (list (symbol "#<unspecified>") '(x 1 f (lambda () (println "test")))) (evaluar-define '((symbol "define") (f) (println "test")) '(x 1))))
    (is (= (list (symbol "#<unspecified>") '(x 1 f (lambda () (println "test") (println "test2") (println "test3")))) (evaluar-define '((symbol "define") (f) (println "test") (println "test2") (println "test3") ) '(x 1))))
    (is (= (list (symbol "#<unspecified>") '(x 1 f (lambda (x) (+ x 1)))) (evaluar-define '((symbol "define") (f x) (+ x 1)) '(x 1))))
    (is (= (list (symbol "#<unspecified>") '(x 1 f (lambda (x y) (+ x y)))) (evaluar-define '((symbol "define") (f x y) (+ x y)) '(x 1))))
    (is (= (list (symbol "#<unspecified>") '(x 1 f (lambda (x y z w u) (- x y z w u)))) (evaluar-define '((symbol "define") (f x y z w u) (- x y z w u)) '(x 1))))
    (is (= (list (symbol "#<unspecified>") '(x 1 f (lambda (x) (display x) (newline) (+ x 1)))) (evaluar-define '(define (f x) (display x) (newline) (+ x 1)) '(x 1))))
  )
)

; user=> (evaluar-set! '(set! x 1) '(x 0))
; (#<unspecified> (x 1))
; user=> (evaluar-set! '(set! x 1) '())
; ((;ERROR: unbound variable: x) ())
; user=> (evaluar-set! '(set! x) '(x 0))
; ((;ERROR: set!: missing or extra expression (set! x)) (x 0))
; user=> (evaluar-set! '(set! x 1 2) '(x 0))
; ((;ERROR: set!: missing or extra expression (set! x 1 2)) (x 0))
; user=> (evaluar-set! '(set! 1 2) '(x 0))
; ((;ERROR: set!: bad variable 1) (x 0))
(deftest set!-test
  (testing "set! tests:"
    (is (= (list (symbol "#<unspecified>") '(x 1)) (evaluar-set! '(set! x 1) '(x 0))))
    (is (= (list (symbol "#<unspecified>") '(x 3)) (evaluar-set! '(set! x 3) '(x 0))))
    (is (= (list (symbol "#<unspecified>") '(x 0 y "mundo")) (evaluar-set! '(set! y "mundo") '(x 0 y "hola"))))
    (is (= (list (list (symbol ";ERROR:") 'unbound (symbol "variable:") 'x) '()) (evaluar-set! '(set! x 1) '())))
    (is (= (list (list (symbol ";ERROR:") (symbol "set!:") 'missing 'or 'extra 'expression '(set! x)) '(x 0)) (evaluar-set! '(set! x) '(x 0))))
    (is (= (list (list (symbol ";ERROR:") (symbol "set!:") 'missing 'or 'extra 'expression '(set! x 1 2)) '(x 0)) (evaluar-set! '(set! x 1 2) '(x 0))))
    (is (= (list (list (symbol ";ERROR:") (symbol "set!:") 'bad 'variable '(set! 1 2)) '(x 0)) (evaluar-set! '(set! 1 2) '(x 0))))
  )
)

; user=> (evaluar-or (list 'or) (list (symbol "#f") (symbol "#f") (symbol "#t") (symbol "#t")))
; (#f (#f #f #t #t))
; user=> (evaluar-or (list 'or (symbol "#t")) (list (symbol "#f") (symbol "#f") (symbol "#t") (symbol "#t")))
; (#t (#f #f #t #t))
; user=> (evaluar-or (list 'or 7) (list (symbol "#f") (symbol "#f") (symbol "#t") (symbol "#t")))
; (7 (#f #f #t #t))
; user=> (evaluar-or (list 'or (symbol "#f") 5) (list (symbol "#f") (symbol "#f") (symbol "#t") (symbol "#t")))
; (5 (#f #f #t #t))
; user=> (evaluar-or (list 'or (symbol "#f")) (list (symbol "#f") (symbol "#f") (symbol "#t") (symbol "#t")))
; (#f (#f #f #t #t))
(deftest evaluar-or-test
  (testing "evaluar-or tests:"
    (is (= (list (symbol "#f") (list (symbol "#f") (symbol "#f") (symbol "#t") (symbol "#t"))) (evaluar-or (list 'or) (list (symbol "#f") (symbol "#f") (symbol "#t") (symbol "#t")))))
    (is (= (list (symbol "#t") (list (symbol "#f") (symbol "#f") (symbol "#t") (symbol "#t"))) (evaluar-or (list 'or (symbol "#t")) (list (symbol "#f") (symbol "#f") (symbol "#t") (symbol "#t")))))
    (is (= (list 7 (list (symbol "#f") (symbol "#f") (symbol "#t") (symbol "#t"))) (evaluar-or (list 'or 7) (list (symbol "#f") (symbol "#f") (symbol "#t") (symbol "#t")))))
    (is (= (list 5 (list (symbol "#f") (symbol "#f") (symbol "#t") (symbol "#t"))) (evaluar-or (list 'or (symbol "#f") 5) (list (symbol "#f") (symbol "#f") (symbol "#t") (symbol "#t")))))
    (is (= (list (symbol "#f") (list (symbol "#f") (symbol "#f") (symbol "#t") (symbol "#t"))) (evaluar-or (list 'or (symbol "#f")) (list (symbol "#f") (symbol "#f") (symbol "#t") (symbol "#t")))))
    (is (= (list '3 (list (symbol "#f") (symbol "#f") (symbol "#t") (symbol "#t"))) (evaluar-or (list 'or (symbol "#f") (symbol "#f") (+ 1 2)) (list (symbol "#f") (symbol "#f") (symbol "#t") (symbol "#t")))))
  )
)

; user=> (evaluar-if '(if 1 2) '(n 7))
; (2 (n 7))
; user=> (evaluar-if '(if 1 n) '(n 7))
; (7 (n 7))
; user=> (evaluar-if '(if 1 n 8) '(n 7))
; (7 (n 7))
; user=> (evaluar-if (list 'if (symbol "#f") 'n) (list 'n 7 (symbol "#f") (symbol "#f")))
; (#<unspecified> (n 7 #f #f))
; user=> (evaluar-if (list 'if (symbol "#f") 'n 8) (list 'n 7 (symbol "#f") (symbol "#f")))
; (8 (n 7 #f #f))
; user=> (evaluar-if (list 'if (symbol "#f") 'n '(set! n 9)) (list 'n 7 (symbol "#f") (symbol "#f")))
; (#<unspecified> (n 9 #f #f))
; user=> (evaluar-if '(if) '(n 7))
; ((;ERROR: if: missing or extra expression (if)) (n 7))
; user=> (evaluar-if '(if 1) '(n 7))
; ((;ERROR: if: missing or extra expression (if 1)) (n 7))
(deftest evaluar-if-test
  (testing "evaluar-if tests:"
    (is (= (list 2 '(n 7)) (evaluar-if '(if 1 2) '(n 7))))
    (is (= (list 7 '(n 7)) (evaluar-if '(if 1 n) '(n 7))))
    (is (= (list 7 '(n 7)) (evaluar-if '(if 1 n 8) '(n 7))))
    (is (= (list (symbol "#<unspecified>") (list 'n 7 (symbol "#f") (symbol "#f"))) (evaluar-if (list 'if (symbol "#f") 'n) (list 'n 7 (symbol "#f") (symbol "#f")))))
    (is (= (list 8 (list 'n 7 (symbol "#f") (symbol "#f"))) (evaluar-if (list 'if (symbol "#f") 'n 8) (list 'n 7 (symbol "#f") (symbol "#f")))))
    (is (= (list (symbol "#<unspecified>") (list 'n 9 (symbol "#f") (symbol "#f"))) (evaluar-if (list 'if (symbol "#f") 'n '(set! n 9)) (list 'n 7 (symbol "#f") (symbol "#f")))))
    (is (= (list 7 (list 'n 7 (symbol "#f") (symbol "#f"))) (evaluar-if (list 'if (symbol "#t") 'n '(set! n 9)) (list 'n 7 (symbol "#f") (symbol "#f")))))
    (is (= (list (list (symbol ";ERROR:") (symbol "if:") 'missing 'or 'extra 'expression '(if)) '(n 7)) (evaluar-if '(if) '(n 7))))
    (is (= (list (list (symbol ";ERROR:") (symbol "if:") 'missing 'or 'extra 'expression '(if 1)) '(n 7)) (evaluar-if '(if 1) '(n 7))))
  )
)