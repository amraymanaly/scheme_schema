(define (square-larger-2 a b c) ; exercise 1.3
    (cond ((and (< a b) (< a c)) (+ (* b b) (* c c)))
    ((and (< b a) (< b c)) (+ (* a a) (* c c)))
    (else (+ (* a a) (* b b)))
    )
)

(define (factorial x) (if (< x 2) 1 (* (factorial (- x 1)) x)))
(define (power n x) (if (= n 0) 1 (* (power (- n 1) x) x)))
(define (sum result from to term) (if (> from to) result (sum (+ result (term from)) (+ from 1) to term)))

(define (nth-root n x) ; extended variant of exercise 1.8, covers newton's general method
    (define (term i y) (let ((f (factorial i)) (p (power i y))) (- (* f p) (/ (* f x) p))))
    (define initial-guess 1.0)
    (define (improve-guess g) (/ (sum (+ (/ x (power (- n 1) g)) (* (- n 1) g)) 2 (- n 2) (lambda(x) (term x g))) n))
    ; absolute
    (define (good-enough? g) (< (abs (- x (power n g))) 0.001))
    (define (iter-improve g) (if (good-enough? g) g (iter-improve (improve-guess g))))
    (iter-improve initial-guess)

    ; relative
    ; (define (good-enough? past present) (< (abs (- past present)) 0.001))
    ; (define (iter-improve past present) (if (good-enough? past present) present (iter-improve present (improve-guess present))))
    ; (iter-improve initial-guess (+ initial-guess 1))
)

(define (count-change amount)
    (define (denom kind)
        (cond
            ((= kind 1) 1)
            ((= kind 2) 5)
            ((= kind 3) 10)
            ((= kind 4) 25)
            ((= kind 5) 50)
        )
    )

    ; the number of ways to make a change for amount a with n kinds of coins =
    ; the number of ways to make a change for amount a with n-1 kinds of coins +
    ; the number of ways to make a change for amount a-d with n kinds of coins, where
    ; d is the denomination of the kind of coin detracted earlier

    (define (change-using-till amount kinds) ; if kinds is 3 we are allowed to use kind 1, 2, 3.
        (cond
            ((or (= kinds 0) (< amount 0)) 0)
            ((= amount 0) 1) ; finally!
            (else (+ (change-using-till amount (- kinds 1)) (change-using-till (- amount (denom kinds)) kinds)))
        )
    )
    (change-using-till amount 5)
)

; (define (count-change-iteratively amount)
;     (define (iter halves quarters tens fives ways) ; state variables
;         ; state "progress" is in the fact that we use up all biggest combinations first
;         ; so 2 ~ ~ ~ ~ indicates that all combinations with exactly one half have been counted
;         ; very clever!
;         (cond
;             ((> (* halves 50) amount) (iter (- halves 1) 1 0 0 ways))
;             ((> (+ (* halves 50) (* quarters 25)) amount) (iter halves))
;
;         )
;     )
; )

(define (sine a) ; exercise 1.15; sin (x) = 3 sin (x/3) - 4 sin^3 (x/3)
    (define (small-enough? x) (not (> (abs x) 0.01)))
    (define (iter x d) (if (small-enough? x) (done x d) (iter (/ x 3) (+ d 1))))
    (define (done sine d) (if (= d 0) sine (done (- (* 3 sine) (* 4 (power 3 sine))) (- d 1))))
    (iter a 0)
)

(define (fast-sth double halve apply-once a b initial-result)
    ; general procedure utilizing number parity to logarithmically optimize pure functions where the following invariant holds:
    ; f(a, b) = f(double(a), halve(b)) [notice the non-commutativity of this assumption, it is general]
    ; if b cannot be halved (odd), apply-once is invoked to manipulate initial-result, and b is decremented
    ; notice how this is the only way to manipulate initial-result to produce the final result throughout the procedure,
    ; as apply-once is the only agent of the specific operation to be fast-ed here, which is appropriate,
    ; since only it can manipulate the result.

    ; double: doubles a
    ; halve: halves b
    ; apply-once: takes a, b and initial-result and returns manipulated result. b is decremented next. crucial because
    ;   it makes b allows be to be decremented (and thus made even!) without losing something. notice how the transformation must
    ;   be linear in the sense that: (apply-once (apply-once x)) = (apply-once (double x)).
    ; a: left operand of apply-once. to be doubled
    ; b: right operand of apply-once. to be halved. conceptually, it is the order of the linear transformation, the number of its
    ;   applications. e.g, it is the exponent in exponentiation, the dividend in division, the multiplicator in multiplication, etc.
    ; intial-result: the result at b = 0, to be manipulated by apply-once (iff b > 0). in other words, the identity constant of
    ;   the operation. for example, 0 for addition, 1 for multiplication and exponentiation, etc.

    (define (iter a b result)
        (cond
            ((= b 0) result)
            ((odd? b) (iter a (- b 1) (apply-once a b result)))
            (else (iter (double a) (halve b) result))
        )
    )
    (iter a b initial-result)
)

; specific cases

; (define (fast-expt b n) ; exercise 1.16
;     (define (iter b n r)
;         (cond
;             ((= n 0) r)
;             ((odd? n) (iter b (- n 1) (* b r)))
;             (else (iter (* b b) (/ n 2) r))
;         )
;     )
;     (iter b n 1)
; )
;
; (define (fast-mult a b); exercise 1.17
;     (define (iter a b r)
;         (cond
;             ((= b 0) r)
;             ((odd? b) (iter a (- b 1) (+ r a)))
;             (else (iter (* a 2) (/ b 2) r))
;         )
;     )
;     ; (iter a b 0) ; naive, log b
;
;     ; better, making use of commutativity, log MIN(a,b)
;     (if (> a b) (iter a b 0) (iter b a 0))
; )

; utilizing fast-sth

(define (fast-expt b n)
    (fast-sth
        (lambda(x) (* x x)) ; double b
        (lambda(x) (/ x 2)) ; halve n
        (lambda(b n r) (* b r)) ; apply-once
        b n 1
    )
)

(define (fast-expt-mod b n m)
    (fast-sth
        (lambda(x) (* x x)) ; double b
        (lambda(x) (/ x 2)) ; halve n
        (lambda(b n r) (remainder (* b r) m)) ; apply-once
        b n 1
    )
)

(define (fast-mult a b)
    (fast-sth
        (lambda(x) (* x 2)) ; double b
        (lambda(x) (/ x 2)) ; halve n
        (lambda(a b r) (+ a r)) ; apply-once
        a b 0
    )
)

; these fast-* algorithms are obviously very useful templates for optimization techniques in algorithms
; you find some function g for which f(n) = f(g(n)), where g is a subset of f (using the cartesian definition of functions)
; and is dense in f (so it's a general "special" case), so you can focus on optimizing this g, or perhaps it is straightforward
; to think about or to implement or even readily available in hardware.
; evenness and oddness is a dense property in Z and a generally useful piece of information, so this motif is quite
; widespread for number manipulations.
; another example:
;   (define (square x)
;       (exp (double (log x)))
;       (define (double x) (+ x x))
;   )
; could be more efficient than the obvious implementation on a machine with logarithm tables available in hardware.

(define (fast-fib n)
    (define (double pq) (let ((p (car pq)) (q (cdr pq)))
        (let ((q2 (* q q))) (cons (+ (* p p) q2) (+ q2 (* 2 p q)) ))
    ))
    (define (apply-transform pq ab) (let ((a (car ab)) (b (cdr ab)) (p (car pq)) (q (cdr pq)))
        (cons (+ (* a (+ p q)) (* b q)) (+ (* b p) (* a q)))
    ))
    (car (fast-sth
        double ; compute the square transform of (p q)
        (lambda(n) (/ n 2)) ; halve n
        (lambda(pq n ab) (apply-transform pq ab)) ; apply-once
        (cons 0 1) n (cons 0 1)
    ))
) ; too awesome to be true, but it works!!

(define (prime? n)
    ; the fermat test and 37 divisibility tests to catch all masqueraders!
    (or (= n 2) (and (odd? n) (= (fast-expt-mod 2 (- n 1) n) 1) (or (< n (+ 1 (* 74 2))) (reallyprime? n 74))))
)

; tests for divisibility on ak + i, i = 1 odd through a-1
; intended only for odd numbers greater than 2a
; if #t then probably prime. O(1)

(define (reallyprime? n a)
    (define (iter m) (cond ((< m 2) #t) ((= 0 (remainder (- n m) a)) (list m #f)) (else (iter (- m 2)))))
    (iter (- a 1))
)

(define carmichaels (list
 561 1105 1729 2465 2821 6601 8911 10585 15841
 29341 41041 46657 52633 62745 63973 75361 101101
 115921 126217 162401 172081 188461 252601 278545
 294409 314821 334153 340561 399001 410041 449065
 488881 512461))

(define uneligible-carmichaels (map (lambda(n) (list n (let ((a (remainder n 5))) (and (not (= 2 a)) (not (= 3 a)))))) carmichaels))

; (define (tester nums a) (if (null? nums) (list) (append (list (reallyprime? (car nums) a)) (tester (cdr nums) a)))) ; just map, duh!
(define (allfalse? a) (cond ((null? a) #t) ((car a) #f) (else (allfalse? (cdr a)))))
(define (really-test-em n)
    (define (iter m) (cond ((< m 3) 0) ((allfalse? (map (lambda(x) (reallyprime? x m)) carmichaels)) m) (else (iter (- m 1)))))
    (iter n)
) ; 26 works for half of them 74 works for all!

(define (generate n)
    (define (iter lis m) (if (= m 0) lis (iter (append lis (list m)) (- m 1))))
    (iter (list) n)
)

(define (average-damp f) (lambda(x) (/ (+ (f x) x) 2))) ; damping to ease oscillations for fixed point searches

(define (fixed-point f initial-guess)
    (define damped-f (average-damp f)) ; damping to ease oscillations for fixed point searches
    (define (close-enough? a b) (< (abs (- a b)) 0.00001))
    (define (try guess) (let ((next (damped-f guess)))
        (display guess)
        (newline)
        (if (close-enough? guess next) next (try next))
    ))
    (newline)
    (display "*** search commenced ***")
    (newline)
    (try initial-guess)
    (display "*** search terminated ***")
)

(define dx 0.00001)
(define (deriv f) (lambda(x) (/ (- (f (+ x dx)) (f x)) dx)))

(define (root-by-newton f) ; the root of g(x) is the fixed point of (x - g(x)/Dg(x))
    (fixed-point (lambda(x) (- x (/ (f x) ((deriv f) x)))) 2.0)
)

(define (iterative-improve improve good-enuf? guess) ; exercise 1.46
    (if (good-enuf? guess) guess (iterative-improve improve good-enuf? (improve guess)))
)

(define (mysqrt y)
    (iterative-improve
        (average-damp (lambda(x) (/ (+ x (/ y x)) 2)))
        (lambda(x) (< (abs (- y (* x x))) 0.001))
        1.0
    )
)

(define (fib-calc n) (+ (* 0.723 (fast-expt 1.618 n)) (* 0.276 (fast-expt (- 0.618) n))))
