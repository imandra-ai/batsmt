
(declare-sort U 0)
(declare-fun a () U)
(declare-fun f (U) U)
(assert
  (and
   (= a (f (f (f a))))
   (= a (f (f (f (f (f a))))))
   (not (= a (f a)))
  ))
(check-sat)
; :status unsat
