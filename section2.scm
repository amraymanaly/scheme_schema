; exercise 2.2
(define make-point cons)
(define x-point car)
(define y-point cdr)
(define make-segment cons)
(define start-segment car)
(define end-segment cdr)
(define (print-point p)
    (display "(")
    (display (x-point p))
    (display ",")
    (display (y-point p))
    (display ")")
    (newline )
)

(define (add-points p1 p2)
    (make-point (+ (x-point p1) (x-point p2)) (+ (y-point p1) (y-point p2)))
)

(define (mult-points p1 p2)
    (make-point (* (x-point p1) (x-point p2)) (* (y-point p1) (y-point p2)))
)

(define (midpoint-segment seg)
    (mult-points
        (add-points (start-segment seg) (end-segment seg))
        (make-point 0.5 0.5)
    )
)

(define (last-pair lis)
    (list-ref lis (- (length lis) 1))
)

; (define (revers lis)
;     (define (iter l n)
;         (if (= n (length lis)) l (iter (cons (list-ref lis n) l) (+ n 1)))
;     )
;     (iter '() 0)
; ) ; too conceited

(define (revers lis)
    (define (iter l ans)
        (if (null? l) ans (iter (cdr l) (cons (car l) ans)))
        ; to not reverse: (append ans (list (car l)))
        ; which is why left folds are much more efficient than right folds
    )
    (iter lis '())
) ; much more straightforward, and much more efficient

(define (cut items n)
    (define (iter l a)
        (if (= a n) l (iter (cons (list-ref items (- n a 1)) l) (+ a 1)))
    )
    (iter '() 0)
)

(define (revers-recursiv lis) (let ((dec (- (length lis) 1)))
    (if (null? lis) lis
        (cons (list-ref lis dec) (revers-recursiv (cut lis dec))))
))

(define us-coins (list 50 25 10 5 1))
(define uk-coins (list 100 50 20 10 5 2 1 0.5))

(define (count-change amount denoms) ; exercise 2.20; yes, order is a factor
    (define (denom kind)
        (list-ref denoms (- kind 1))
    )

    (define (change-using-till amount kinds) ; if kinds is 3 we are allowed to use kind 1, 2, 3. etc.
        (cond
            ((or (= kinds 0) (< amount 0)) 0)
            ((= amount 0) 1) ; finally!
            (else (+ (change-using-till amount (- kinds 1)) (change-using-till (- amount (denom kinds)) kinds)))
        )
    )
    (change-using-till amount 5)
)

(define (same-parity a . x)
    (define parity? (if (even? a) even? odd? ))
    (define (iter tmp fin)
        (if (null? tmp) fin
        (let ((item (car tmp)))
            (iter (cdr tmp) (append fin (if (parity? item) (list item) '())))
    )))
    (iter x (list a))
)

(define (same-parity-filter a . x)
    (define parity? (if (even? a) even? odd? ))
    (cons a (filter parity? x))
)

(define (same-parity-recursiv a . x)
    (define parity? (if (even? a) even? odd? ))
    (define (recur k)
        (if
            (null? k) k
            (let ((item (car k)) (done (recur (cdr k))))
            (if (parity? item) (cons item done) done)
        ))
    )
    (cons a (recur x))
) ; pretty aint it ;)

(define (deep-revers lis) ; exercise 2.27
    (define (iter l ans)
        (if (null? l) ans (iter (cdr l) (cons (deep-revers (car l)) ans)))
    )
    (if (pair? lis) (iter lis '()) lis)
)

(define (fringe tree) ; exercise 2.28
    (if (pair? tree)
        (let ((head (car tree)) (tail (cdr tree)))
            (if (pair? head) (fringe (append head tail))
                (cons head (fringe tail))))
        tree)
)

; exercise 2.29

(define make-mobile list) ; (list left right)
(define make-branch list) ; (list length structure)

(define the-mobile (make-mobile (make-branch 6 7)
    (make-branch 5 (make-mobile (make-branch 10 8) (make-branch 11 9)))))

(define left-branch car)
(define right-branch cadr)

(define branch-length car)
(define branch-structure cadr)
(define mobile? pair?)

(define (sum-list lis)
    (define (iter items acc)
        (if (null? items) acc (iter (cdr items) (+ acc (car items))))
    )
    (iter lis 0)
)

(define (weights mobile)
    (let    ((sleft (branch-structure (left-branch mobile)))
            (sright (branch-structure (right-branch mobile))))
    (cond
        ((and (mobile? sleft) (mobile? sright)) (append (weights sleft) (weights sright)))
        ((mobile? sleft) (append (weights sleft) (list sright)))
        ((mobile? sright) (cons sleft (weights sright)))
        (else (list sleft sright))
    ))
)

(define (weights-map mobile) ; weights - using map and filter
    (define (do-once mob) ; just for recursion
        (map (lambda(branch)
            (let ((w (branch-structure branch)))
            (if (mobile? w) (cons 0 (do-once w)) (list 0 w))
        )) mob)
    )
    (filter (lambda(w) (not (= w 0))) (fringe (do-once mobile)))
)

(define (total-weight mobile) (sum-list (weights mobile)))

(define (square-tree lis) ; exercise 2.30
    (if (null? lis) lis
    (let ((head (car lis)) (tail (cdr lis)))
    (if (pair? head)
        (cons (square-tree head) (square-tree tail))
        (cons (* head head) (square-tree tail))
    )
)))

; (define (tree-map f tree) ; exercise 2.31
;     (if (null? tree) tree
;     (let ((head (car tree)) (tail (cdr tree)))
;     (if (pair? head)
;         (cons (tree-map f head) (tree-map f tail))
;         (cons (f head) (tree-map f tail))
;     )
; ))) ; not high level enough, re-implements map's element by element access

(define (tree-map f tree)
    (map (lambda(branch)
        (if (pair? branch) (tree-map f branch) (f branch))
    ) tree)
) ; it's almost a reverse substitution of the definition of map

(define (subsets s)
    (if (null? s)
        (list s)
        (let ((rest (subsets (cdr s))))
        (append rest (map (lambda (x) (cons (car s) x)) rest))
    ))
)
