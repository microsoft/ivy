; benchmark generated from python API
(set-info :status unknown)
(declare-fun __X () Int)
(declare-fun nset.index.succ (Int Int) Bool)
(assert
 (let (($x259 (forall ((|X:nset.index| Int) (|Y:nset.index| Int) )(= (nset.index.succ |X:nset.index| |Y:nset.index|) (= |Y:nset.index| (+ |X:nset.index| 1))))
 ))
 (and $x259)))
(assert
 (and (not (<= 0 __X)) (not (< __X 0))))
(check-sat)
