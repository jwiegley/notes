(set-option :produce-models true)

(declare-const subnets Int)
(declare-fun nodes (Int) Int)

;; test 1

(assert (> subnets 2))

;; test 2

(assert (< subnets 100))

(minimize subnets)

(check-sat)
(get-model)
