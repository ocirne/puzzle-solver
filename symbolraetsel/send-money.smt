
; Send More Money!
; ================
;
;   SEND
; + MORE
; ------
;  MONEY
;
; How much is "MONEY"?
;
; (source: http://de.wikipedia.org/wiki/Mathematisches_R%C3%A4tsel, 2015-01-08)

(set-option :print-success false)
(set-option :produce-models true)

; we need a logic with functions and calculations
(set-logic QF_AUFLIA)

; the variables set(s, e, n, d, m, o, r, e, m, o, n, e, y)
(declare-fun s () Int)
(declare-fun e () Int)
(declare-fun n () Int)
(declare-fun d () Int)
(declare-fun m () Int)
(declare-fun o () Int)
(declare-fun r () Int)
(declare-fun y () Int)

; variables are all pairwise different, see yices FAQ
(declare-fun u (Int) Int)
(assert (and (= (u s) 0) (= (u e) 1) (= (u n) 2) (= (u d) 3) (= (u m) 4)
             (= (u o) 5) (= (u r) 6) (= (u y) 7)))

; range: from <= x <= to
(define-fun between ((x Int) (from Int) (to Int)) Bool
    (and (<= from x) (<= x to)))

; number as vwxyz is e = v * 10000 + w * 1000 + x * 100 + y * 10 + z
(define-fun is ((e Int) (v Int) (w Int) (x Int) (y Int) (z Int)) Bool
    (= e (+ (* v 10000) (* w 1000) (* x 100) (* y 10) z)))

; solutions are in the range [0, 9]
(assert (and (between s 0 9)
             (between e 0 9)
             (between n 0 9)
             (between d 0 9)
             (between m 0 9)
             (between o 0 9)
             (between r 0 9)
             (between y 0 9)))

(declare-fun  send () Int)
(declare-fun  more () Int)
(declare-fun money () Int)

; map this to the aggregated variables
(assert (is  send 0 s e n d))
(assert (is  more 0 m o r e))
(assert (is money m o n e y))

; first digits are not zero
(assert (not (= s 0)))
(assert (not (= m 0)))

; model the relation
(assert (= (+ send more) money))

; solve
(check-sat)

; print values
(get-value (m o n e y))

; usage:
; > yices-smt2 send-money.smt
; sat
; ((m 1) (o 0) (n 6) (e 5) (y 2))

; solution is unique, proof with additional clause:
; (assert (not (and (= m 1) (= o 0) (= n 6) (= e 5) (= y 2))))

