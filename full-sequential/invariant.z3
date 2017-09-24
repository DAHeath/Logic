(set-option :fixedpoint.engine "duality")

(declare-var r Bool)
(declare-var r_ Bool)

(declare-var input Bool)
(declare-var output Bool)

(declare-rel invariant (Bool))
(declare-rel phi (Bool Bool))
(declare-rel q ())

(define-fun circuit ((i Bool) (r Bool) (r_ Bool) (o Bool)) Bool
  (and
    (= o r)
    (= r_ (and i r))))

(rule (invariant false))

(rule (=>
  (and
    (invariant r)
    (circuit input r r_ output))
  (invariant r_)))

(rule (=> (not
  (=>
    (and
      (invariant r)
      (circuit input r r_ output))
    (not output)))
  q))

(query q :print-certificate true)
