(define make-counter () (do
    (def n 0)
    (lambda () (do
        (set n (+ n 1))
        n
        )
    )))

(def counter1 (make-counter))
(def counter2 (make-counter))

(print (counter1)) ; => 1
(print (counter1)) ; => 2
(print (counter2)) ; => 1
(print (counter1)) ; => 3
(print (counter2)) ; => 2
