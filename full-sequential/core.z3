(set-option :produce-unsat-cores true)

(declare-const input Bool)
(declare-const output Bool)

(declare-const r Bool)
(declare-const r_ Bool)

(declare-const w1 Bool)
(declare-const w2 Bool)
(declare-const w3 Bool)

(assert (! (= w1 input)                   :named a))
(assert (! (= w3 (and w1 w2))             :named b))
(assert (! (= r_ w3)                      :named c))
(assert (! (= w2 r)                       :named d))
(assert (! (= output r)                   :named e))

(assert (! (= r false)                    :named f))
(assert (! (or (not (= r_ false)) output) :named g))

(check-sat)
(get-unsat-core)
