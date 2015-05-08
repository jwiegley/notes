;(include-book "acl2s/cgen/top" :dir :system :ttags :all)

(acl2s-defaults :set testing-enabled nil)

(defun move (a b)
  (list 'move a 'to b))

(defun upto (n)
  (if (zp n)
      nil
      (append (upto (1- n)) (list n))))

(defthm upto-length
  (implies (natp n)
           (equal (length (upto n)) n)))

(defun hanoi (a b c n)
  (cond ((zp n)
         nil)
        ((equal n 1)
         (list (move a c)))
        (t
         (append (hanoi a c b (1- n))
                 (cons (move a c)
                       (hanoi b a c (1- n)))))))

(defthm hanoi-moves-required
  (implies (and (natp n))
           (equal (len (hanoi a b c n))
                  (1- (expt 2 n)))))

(defun run-hanoi (a b c moves)
  (if (endp moves)
      (list a b c)
      (let* ((res (run-hanoi a b c (cdr moves)))
             (aa (nth 0 res))
             (bb (nth 1 res))
             (cc (nth 2 res))
             (x (car moves)))
         (cond ((equal x '(move a to b)) (list (cdr aa) (cons (car aa) bb) cc))
               ((equal x '(move a to c)) (list (cdr aa) bb (cons (car aa) cc)))
               ((equal x '(move b to a)) (list (cons (car bb) aa) (cdr bb) cc))
               ((equal x '(move b to c)) (list aa (cdr bb) (cons (car bb) cc)))
               ((equal x '(move c to a)) (list (cons (car cc) aa) bb (cdr cc)))
               ((equal x '(move c to b)) (list aa (cons (car cc) bb) (cdr cc)))
               (t (list aa bb cc))))))

(defthm hanoi-one-step
  (implies (and (natp n) (< 0 n))
           (equal (append (hanoi 'a 'c 'b (+ -1 n))
                          (cons '(move a to c)
                                (hanoi 'b 'a 'c (+ -1 n))))
                  (hanoi 'a 'b 'c n))))

(defthm append-plus
  (implies (and (natp n) (< 0 n)) 
           (equal (append (upto (+ -1 n)) (list n))
                  (upto n))))

(defthm hanoi-moves-correct
  (implies (and (natp n) (< 0 n))
           (equal (run-hanoi (upto n) nil nil (hanoi 'a 'b 'c n))
                  (list nil nil (upto n)))))
