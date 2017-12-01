; benchmark generated from python API
(set-info :status unknown)
(declare-sort foo)
(declare-sort bar)
(declare-fun |0:foo| () foo)
(declare-fun d.val () foo)
(declare-fun __foo$0 () foo)
(declare-fun __bar$0 () bar)
(declare-fun |__new_fml:z| () Bool)
(declare-fun cp.was_up () Bool)
(assert
 (and (not (=> cp.was_up (not |__new_fml:z|))) (= |__new_fml:z| (= d.val |0:foo|))))
(assert
 and)
(assert
 (forall ((|Xfoo:foo| foo) )(or (= |Xfoo:foo| __foo$0)))
 )
(assert
 (forall ((|Xbar:bar| bar) )(or (= |Xbar:bar| __bar$0)))
)
(check-sat)
