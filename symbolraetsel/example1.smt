
; Example 1
; =========
;
; ABC - DFG = HBE
;  +     -     +
;   D + GCH = GCA
; ---------------
; AAE - GIE = IGF

; map this to the aggregated variables
(assert (is x00 a b c))
(assert (is x10 d f g))
(assert (is x20 h b e))
(assert (is x01 0 0 d))
(assert (is x11 g c h))
(assert (is x21 g c a))
(assert (is x02 a a e))
(assert (is x12 g i e))
(assert (is x22 i g f))

; first digits are not zero
(assert (not (= a 0)))
(assert (not (= d 0)))
(assert (not (= h 0)))
(assert (not (= d 0)))
(assert (not (= g 0)))
(assert (not (= i 0)))

; model the relations
(assert (= (- x00 x10) x20))
(assert (= (+ x01 x11) x21))
(assert (= (- x02 x12) x22))

(assert (= (+ x00 x01) x02))
(assert (= (- x10 x11) x12))
(assert (= (+ x20 x21) x22))

; solve
(check-sat)

; print values
(get-value (a b c d e f g h i j))

; usage:
; > cat common.smt example1.smt | yices-smt2
; sat
; ((a 9) (b 8) (c 4) (d 7) (e 1) (f 0) (g 3) (h 2) (i 6) (j 5))

