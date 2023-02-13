(defun wave-cycles (freq)
  "If on cycle 0 the wave peak occurs at an integer, then cycle (wave-cycles freq) is the earliest
    next wave peak that occurs at an integer."
  (check-type freq rational)
  (numerator freq))

(defun wave-peaks (freq)
  (check-type freq rational)
  (loop for i from 0 below (wave-cycles freq)
        collect (* i (/ freq))))

(defun wave-peak-ones (freq &optional (offset 0) len)
  (check-type freq rational)
  (let* ((len (or len (denominator freq)))
         (result (make-list len :initial-element 0)))
    (loop for i from (mod offset (/ freq)) by (/ freq)
          while (< i len)
          do (incf (nth (floor i) result)))
    result))

(defun vector-add (&rest vs)
  (apply #'mapcar #'+ vs))

(defparameter *waves*
  (list* (wave-peak-ones 1/4 3 56) (loop for i from 0 below 7 collect (wave-peak-ones 22/56 (* i 11/30) 56))))

(defparameter *everybody* '(zander armand ben bruno calvin jason mark trent))
(defparameter *almost-everybody* (remove 'zander *everybody*))

(defparameter *chore-people* `((cleaning ,@*everybody*)
                               (dishes ,@*almost-everybody*)
                               (garbage ,@*everybody*)))

(defparameter *people-days* (mapcar #'cons *everybody* *waves*))

(defparameter *distinguished-days* `((garbage . ,(loop for day from 0 below 56 by 7
                                                       append (if (< (1+ day) 56)
                                                                  (list day (1+ day))
                                                                  (list day))))))

