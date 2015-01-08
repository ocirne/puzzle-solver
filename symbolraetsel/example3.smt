
; Example 3
; =========
;
; ACE + DAC = JFD
;  -     +     -
; AAA - HFC =  GI
;  =     =     =
;  AH + III = JBJ
;
; (source: http://de.wikipedia.org/wiki/Mathematisches_R%C3%A4tsel, 2015-01-08)

; map this to the aggregated variables
(assert (is x00 a c e))
(assert (is x10 d a c))
(assert (is x20 j f d))
(assert (is x01 a a a))
(assert (is x11 h f c))
(assert (is x21 0 g i))
(assert (is x02 0 a h))
(assert (is x12 i i i))
(assert (is x22 j b j))

; first digits are not zero
(assert (not (= a 0)))
(assert (not (= d 0)))
(assert (not (= j 0)))
(assert (not (= h 0)))
(assert (not (= i 0)))

; model the relations
(assert (= (+ x00 x10) x20))
(assert (= (- x01 x11) x21))
(assert (= (+ x02 x12) x22))

(assert (= (- x00 x01) x02))
(assert (= (+ x10 x11) x12))
(assert (= (- x20 x21) x22))

; solve
(check-sat)

; print values
(get-value (a b c d e f g h i j))

; usage:
; > cat common.smt example3.smt | yices-smt2
; sat
; ((a 2) (b 0) (c 4) (d 7) (e 3) (f 6) (g 5) (h 1) (i 8) (j 9))

