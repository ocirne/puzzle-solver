
; Example 2
; =========
;
; ABC - DDE = ECA
;  +     +     +
; DFG -  EE = ECD
; ---------------
; HED - DGI = GAH

; map this to the aggregated variables
(assert (is x00 a b c))
(assert (is x10 d d e))
(assert (is x20 e c a))
(assert (is x01 d f g))
(assert (is x11 0 e e))
(assert (is x21 e c d))
(assert (is x02 h e d))
(assert (is x12 d g i))
(assert (is x22 g a h))

; first digits are not zero
(assert (not (= a 0)))
(assert (not (= d 0)))
(assert (not (= e 0)))
(assert (not (= h 0)))
(assert (not (= g 0)))

; model the relations
(assert (= (- x00 x10) x20))
(assert (= (- x01 x11) x21))
(assert (= (- x02 x12) x22))

(assert (= (+ x00 x01) x02))
(assert (= (+ x10 x11) x12))
(assert (= (+ x20 x21) x22))

; solve
(check-sat)

; print values
(get-value (a b c d e f g h i j))

; usage:
; > cat common.smt example2.smt | yices-smt2
; sat
; ((a 6) (b 1) (c 8) (d 3) (e 2) (f 0) (g 5) (h 9) (i 4) (j 7))

