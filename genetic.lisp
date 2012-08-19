#!/usr/bin/env sbcl --script

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; A.Clarke 2010
;;;
;;; example of using genetic programming to determine the quadratic function
;;; that most closely matches sin(x) in range [0,3.14]
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(DECLAIM (OPTIMIZE (SPEED 3) (SAFETY 0)))

(defun safediv (x y)
  (declare (single-float x y))
  (if (= y 0)
      1.0
      (/ x y)))

(defstruct function-info symbol function arity)
(defstruct terminal-info symbol value)

(defmacro make-float-terminal-info (x)
  `(make-terminal-info :symbol ',x  :value ,x))

(defmacro make-symbol-function-info (sym arity)
  `(make-function-info :symbol ,sym 
                       :function (symbol-function ,sym) 
                       :arity ,arity))

(defparameter *functions*
  (list (make-symbol-function-info '+ 2)
        (make-symbol-function-info '- 2) 
        (make-symbol-function-info '* 2) 
        (make-symbol-function-info 'safediv 2)))

(defparameter *terminals*
  (list (make-float-terminal-info -1.0)
        (make-float-terminal-info 0.0)
        (make-float-terminal-info 1.0)
        (make-float-terminal-info 2.0)
        (make-float-terminal-info 3.0)
        (make-float-terminal-info 0.1)
        (make-terminal-info :symbol 'x :value (lambda (args) (nth 0 args)))))

(defparameter *max-depth* 6)
(defparameter *num-generations* 10)
(defparameter *generation-size* 10000)
(defparameter *crossover-probability* 90)
(defparameter *mutation-probability* 5)
(defparameter *reproduction-probability* 5)
(defparameter *my-random-state* (sb-ext:seed-random-state 0))
(defparameter *output-func* (lambda (x) x))

(defun eval-terminal (term args)
  (let ((term-value (terminal-info-value term)))
    (if (functionp term-value)
        (funcall term-value args)
        term-value)))

(defun random-list-item (arglist)
  (let ((index (random (list-length arglist) *my-random-state*)))
    (nth index arglist)))

(defun repeatedly (func n)
  (let ((answer '()))
    (dotimes (i (truncate n))
      (push (funcall func) answer))
    answer))

(defun gen-grow-tree (terminals functions max-depth 
                      &optional (func-chance 50) (depth 0))
  (flet ((random-terminal () (random-list-item terminals)))
    (if (>= depth max-depth)
        (random-terminal)
        (if (< (random 100 *my-random-state*) func-chance)
            (flet ((recurse () 
                     (gen-grow-tree terminals 
                                    functions 
                                    max-depth 
                                    func-chance 
                                    (+ depth 1))))
              (let* ((func-info (random-list-item functions))
                     (arity (function-info-arity func-info))
                     (args (repeatedly #'recurse arity)))
                (cons func-info args)))
            (random-terminal)))))

(defun gen-full-tree (terminals functions max-depth)
  (gen-grow-tree terminals functions max-depth 100))

(defun scrape-tree (tree terminal-scraper)
  (flet ((mapper (x) (scrape-tree x terminal-scraper)))
    (if (listp tree)
        (let* ((func (function-info-symbol (car tree)))
               (args (cdr tree))
               (arg-evals (mapcar #'mapper args)))
          (cons func arg-evals))
        (funcall terminal-scraper tree))))

(defun calc-print-tree (tree)
  (flet ((terminal-scraper (x) (terminal-info-symbol x)))
    (scrape-tree tree #'terminal-scraper)))

(defun eval-tree (tree term-args)
  (flet ((evaluator (x) (eval-tree x term-args)))
    (if (listp tree)
        (let* ((func (function-info-function (car tree)))
               (func-args (cdr tree))
               (func-arg-evals (mapcar #'evaluator func-args)))
          (apply func func-arg-evals))
        (eval-terminal tree term-args))))

(defun gen-original-population (size terminals functions max-depth)
  (flet ((grow-generator () (gen-grow-tree terminals functions max-depth))
         (full-generator () (gen-full-tree terminals functions max-depth)))
    (let* ((grow-size (/ size 2.0))
           (full-size (- size grow-size)))
      (union (repeatedly #'grow-generator grow-size)
             (repeatedly #'full-generator full-size)))))

(defun calc-depth (tree &optional (depth 0))
  (flet ((mapper (x) (calc-depth x (+ depth 1))))
    (if (listp tree)
        (let* ((args (cdr tree))
               (arg-evals (mapcar #'mapper args)))
          (apply 'max arg-evals))
        depth)))

(defun fitness-func (tree)
  (let ((answer 0.0)
        (delta (/ 3.14 10)))
    (loop for i from 0.0 below 3.2 by delta do
         (setf answer (+ answer (abs (- (sin i) (eval-tree tree (list i)))))))
    (let ((depth (calc-depth tree)))
      (when (> depth 4)
        (setf answer (+ answer (* (- depth 4) 0.1)))))
    answer))

(defun calc-fittest (func population)
  (let* ((fitness-pairs (mapcar (lambda (x) (list (funcall func x) x)) population))
         (sorted-fitness-pairs 
          (sort fitness-pairs (lambda (x y) (< (car x) (car y))))))
    (list (car sorted-fitness-pairs) (cadr sorted-fitness-pairs))))

(defun grab-random-function (code)
  (let ((answer '())
        (stack (list code))
        (func-count 0))
    (loop while (not (equalp stack '())) do
         (let ((top (pop stack)))
           (when (listp top)
             (setf func-count (+ func-count 1))
             (when (= (random func-count *my-random-state*) 0)
               (setf answer top))
             (loop for arg in (cdr top) do
                  (push arg stack)))))
    answer))

(defun replace-location (modded mod-pos modder)
  (if (equalp modded mod-pos)
      modder
      (if (listp modded)
          (let ((args (mapcar (lambda (x) (replace-location x mod-pos modder))
                              (cdr modded))))
            (cons (car modded) args))
          modded)))
         
(defun gen-crossover (father mother) 
  (let* ((father-point (grab-random-function father))
         (mother-point (grab-random-function mother)))
    (replace-location father father-point mother-point)))

(defun gen-mutation (father max-depth terminals functions) 
  (let ((mutant-mom (gen-full-tree terminals functions max-depth)))
    (gen-crossover father mutant-mom)))

(defun gen-reproduction (father mother) 
  (if (= (random 2 *my-random-state*) 0)
      father
      mother))

(defun gen-offspring (father mother terminals functions max-depth) 
  (let ((selector (random 100 *my-random-state*)))
    (cond ((< selector *crossover-probability*)
           (gen-crossover father mother))
          ((< (- selector *crossover-probability*) *mutation-probability*)
           (gen-mutation father max-depth terminals functions))
          (t (gen-reproduction father mother)))))

(defun gen-next-generation (fittest size terminals functions max-depth)
  (let ((father (first fittest))
        (mother (second fittest)))
    (flet ((offspring-maker () (gen-offspring father 
                                              mother 
                                              terminals 
                                              functions
                                              max-depth)))
      (repeatedly #'offspring-maker size))))

(defun run-genetics ()
  (let* ((population (gen-original-population *generation-size* 
                                              *terminals* 
                                              *functions* 
                                              *max-depth*))
         (fittest nil))
    (setf *random-state* (sb-ext:seed-random-state 0))
    (dotimes (gen-count *num-generations*)
      (let ((two-fittest (calc-fittest #'fitness-func population)))
        (format t "gen: ~a fittest: ~a~%" gen-count (caar two-fittest))
        (finish-output)
        (setf fittest (mapcar (lambda (x) (second x)) two-fittest))
        (setf population (gen-next-generation fittest
                                              *generation-size* 
                                              *terminals* 
                                              *functions*
                                              *max-depth*))))
    (let ((code (calc-print-tree (car fittest))))
      (format t "result: ~a~%" code)
      (let ((compiled-func (coerce `(lambda (x) ,code) 'function)))
        (setf *output-func* compiled-func)))))
    
(defun output-func (x) (funcall *output-func* x))

(run-genetics)
