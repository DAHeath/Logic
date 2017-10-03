(push)
;; linear

(declare-const x Int)
(declare-const y Int)
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)

(define-fun lin ((v1 Int) (v2 Int)) Bool
  (and
    (not (= a 0))
    (not (= b 0))
    (= (+ (* a v1) (* b v2)) c)))

(assert (forall ((x Int) (y Int))
  (and
    (=>
      (and (= x 1) (= y 2))
      (lin x y))
    (=>
      (and (= x 4) (= y 5))
      (lin x y)))))

(check-sat)
(get-model)

(pop)

(push)
;; modular

(declare-const x Int)
(declare-const a Int)
(declare-const b Int)

(define-fun modular ((v Int)) Bool
  (and
    (> a 1)
    (= (mod v a) b)))

(assert (forall ((x Int))
  (and
    (=>
      (and (= x 1))
      (modular x))
    (=>
      (and (= x 3))
      (modular x)))))

(check-sat)
(get-model)

(pop)
