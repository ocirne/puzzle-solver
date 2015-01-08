
(set-option :print-success false)
(set-option :produce-models true)

; we need a logic with functions and calculations
(set-logic QF_AUFLIA)

; the ten solutions a .. j
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(declare-fun d () Int)
(declare-fun e () Int)
(declare-fun f () Int)
(declare-fun g () Int)
(declare-fun h () Int)
(declare-fun i () Int)
(declare-fun j () Int)

; a, b .. j are all pairwise different, see yices FAQ
(declare-fun u (Int) Int)
(assert (and (= (u a) 0) (= (u b) 1) (= (u c) 2) (= (u d) 3) (= (u e) 4)
             (= (u f) 5) (= (u g) 6) (= (u h) 7) (= (u i) 8) (= (u j) 9)))

; range: from <= x <= to
(define-fun between ((x Int) (from Int) (to Int)) Bool
    (and (<= from x) (<= x to)))

; number as xyz is e = x * 100 + y * 10 + z
(define-fun is ((e Int) (x Int) (y Int) (z Int)) Bool
    (= e (+ (* x 100) (* y 10) z)))

; solutions are in the range [0, 9]
(assert (and (between a 0 9)
             (between b 0 9)
             (between c 0 9)
             (between d 0 9)
             (between e 0 9)
             (between f 0 9)
             (between g 0 9)
             (between h 0 9)
             (between i 0 9)
             (between j 0 9)))

; The general form of the puzzle is
;
; x00 . x10 . x20
;  .     .     .
; x01 . x11 . x21
; ---------------
; x02 . x12 . x22
;
; with x00 .. x22 some up to 3 digit numbers and . in [+, -, =].

(declare-fun x00 () Int)
(declare-fun x01 () Int)
(declare-fun x02 () Int)
(declare-fun x10 () Int)
(declare-fun x11 () Int)
(declare-fun x12 () Int)
(declare-fun x20 () Int)
(declare-fun x21 () Int)
(declare-fun x22 () Int)

