
(declare-sort U 0)
(declare-fun p () Bool)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(declare-fun f (U) U)
(assert
  (and
   (= a (ite p b c))
   (not (= (f a) (f b)))
   (not (= (f a) (f c)))
  ))
(check-sat)
; :status unsat
