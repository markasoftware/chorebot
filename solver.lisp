(ql:quickload '(:alexandria :cl-smt-lib :cl-sat :anaphora))
(use-package '(:alexandria :cl-smt-lib :anaphora))

(defvar *smt-symbol-counter* 0)

;; (defun map-combs (fn k list &optional so-far)
;;   (cond
;;     ((= k 0)
;;      (funcall fn so-far))
;;     ((null list))
;;     (t
;;      (loop for tail on list
;;            do (map-picks fn (1- k) (cdr tail) (cons (car tail) so-far))))))


;; we want to know:
;; + Number of times each person much perform each chore, indexed by person

;; we want to specify:
;; + List of people for each chore

;; (defun invert-alist (alist)
;;   "Given an alist from x to list of ys, come up with alist from y to list of xs. Operates naively,
;; so n^2 time I think?"
;;   (let ((all-ys (remove-duplicates (apply #'concatenate 'list (mapcar #'cdr alist)))))
;;     (mapcar (lambda (y) (cons y (mapcar #'car (remove-if-not (curry #'member y) alist :key #'cdr)))) all-ys)))
;; CoMbInAtOrS aRe EaSiEr To ReAd

(defun step-2 (people-days chore-people distinguished-days &optional reduce-boredom)
  "People-days is an alist from people to a list of how many chores they should perform every
  day. Chore-people is at alist from chore names to the people assigned to that chore.
  Distinguished-days is an alist (with duplicate keys allowed and meaningful) from chore names to a
  list of days (integers) which should be divided evenly among people assigned to that chore."
  (assert people-days)
  (let ((all-people (mapcar #'car people-days))
        (all-days (iota (length (cdar people-days))))
        (all-chores (mapcar #'car chore-people))
        (pdc-symbols (make-hash-table :test #'equal)))
    (flet ((pdc-symbol (person day chore)
             (or (gethash (list person day chore) pdc-symbols)
                 (setf (gethash (list person day chore) pdc-symbols)
                       (intern (format nil "~a-~a-~a-~a" person day chore (incf *smt-symbol-counter*)))))))
      (let* ((all-pdc-symbols
               (loop for person in all-people
                     append (loop for day in all-days
                                  append (loop for chore in all-chores
                                               collect (pdc-symbol person day chore)))))
             (smt-input 
               `((|set-logic| QF_LIA)
                 
                 ;; Declare variables: One for each task/chore/person combination
                 ,@(loop for pdc-symbol in all-pdc-symbols
                         ;; Readtable mode :invert only inverts symbol names that are all of one
                         ;; case -- names with multiple cases are left as-is.
                         collect `(|declare-const| ,pdc-symbol |Int|)
                         collect `(|assert| (|or| (= 0 ,pdc-symbol) (= 1 ,pdc-symbol))))

                 ;; Constraint 1: Each chore must be completed once per day
                 ,@(loop for day in all-days
                         append (loop for chore in all-chores
                                      for people-syms = (loop for person in all-people
                                                              collect (pdc-symbol person day chore))
                                      collect `(|assert| (= 1 (+ ,@people-syms)))))

                 ;; Constraint 2: Each person must complete the set number of chores each day
                 ,@(loop for (person . chores-per-day) in people-days
                         append (loop for chores-today in chores-per-day
                                      for day from 0
                                      for chore-syms = (loop for chore in all-chores
                                                             collect (pdc-symbol person day chore))
                                      collect `(|assert| (= ,chores-today (+ ,@chore-syms)))))

                 ;; Constraint 3: Each person must complete the correct number of chores over the whole
                 ;; schedule.
                 ,@(loop for person in all-people
                         append (loop for (chore . people-for-chore) in chore-people
                                      for person-chore-instances = (/ (length all-days) (length people-for-chore))
                                      for day-syms = (loop for day in all-days
                                                           collect (pdc-symbol person day chore))
                                      when (member person people-for-chore)
                                        collect `(|assert| (= ,person-chore-instances (+ ,@day-syms)))
                                      ))

                 ;; Constraint 4 (Optional): Don't do the same task twice in a row
                 ,@(when reduce-boredom
                     (flet ((not-bored (person day1 day2)
                              (loop for chore in all-chores
                                    collect `(|assert| (>= 1 (+ ,(pdc-symbol person day2 chore)
                                                                ,(pdc-symbol person day1 chore)))))))
                      (loop ;; TODO: limit to people with multiple chores assigned
                        for (person . chores-per-day) in people-days
                            for days-involving-chores = (loop for day from 0
                                                              for chores-per-today in chores-per-day
                                                              do (assert (>= 1 chores-per-today) () "Boredom not well-defined")
                                                              when (= 1 chores-per-today)
                                                                collect day)
                            ;; if only one day with chore, nothing to do
                            when (cdr days-involving-chores)
                              append (append
                                      (not-bored person (car days-involving-chores) (lastcar days-involving-chores)) ;; circular condition
                                      (loop for days on days-involving-chores
                                            while (cadr days)
                                            append (not-bored person (car days) (cadr days)))))))

                 ;; Constraint 5: Distinguished days.
                 ,@(loop for (chore . days) in distinguished-days
                         for people = (assoc-value chore-people chore)
                         for (days-per-person remainder) = (multiple-value-list (floor (length days) (length people)))
                         do (assert (= 0 remainder))

                         append (loop for person in people
                                      for day-syms = (loop for day in days
                                                           collect (pdc-symbol person day chore))
                                      collect `(|assert| (= ,days-per-person (+ ,@day-syms)))))

                 (|check-sat|)
                 (|get-value| ,all-pdc-symbols)))
             ;; doesn't seem to use parallel, but let's enable it anyway.
             (smt (make-smt "z3" "parallel.enable=true" "-in" "-smt2")))

        (write-to-smt smt smt-input)
        (ecase (read smt)
          (unsat) ; return nil
          (sat
           (let ((sat-alist (read smt)))
             (loop for day in all-days
                   collect (loop for chore in all-chores
                                 append (list chore (loop for person in all-people
                                                          when (= 1 (cadr (assoc (pdc-symbol person day chore) sat-alist)))
                                                            do (return person)
                                                          finally (assert nil))))))))))))

(defun print-csv-row (l stream)
  ;; too lazy to lookup format iteration stuff again
  (when l
    (format stream "~a" (car l))
    (dolist (el (cdr l))
      (format stream ",~a" el))
    (format stream "~%")))

(defun to-csv (step-2-output &optional (stream t))
  (let* ((chore-names (loop for sym in (car step-2-output) by #'cddr collect sym))
         (chore-name-getters (mapcar (curry #'rcurry #'getf) chore-names)))
    (print-csv-row chore-names stream)
    (loop for row in step-2-output
          do (print-csv-row (mapcar (rcurry #'funcall row) chore-name-getters) stream))))

;; EARLIER ATTEMPT TO USE A SAT SOLVER INSTEAD OF Z3
;; Of course, it is possible, but I went down the wrong track by using the really inefficient way of formulating "exactly N out of M variables shall be true". And z3 is pretty fast anyway.

;; SAT stuff we probably won't use:

;; (defmacro docombinations (k list var &body body)
;;   `(map-combinations (lambda (,var) ,@body) ,list :length ,k))

;; (defun not-more-than-n (n list)
;;   (let ((result)
;;         (len (length list))
;;         (negated-list (mapcar (curry #'list 'not) list)))
;;     (when (< n len)
;;       (docombinations (1+ n) negated-list cur-combination
;;         (push (cons 'or cur-combination) result))
;;       result)))

;; (defun exactly-n (n list)
;;   "Return a boolean expression that exactly n of list is true. Strategy: It's easy to assert than
;; not more than n of the list is true, by requiring that at least one out of every (n+1) subset is NOT
;; true. We combine this twice: Ensure than not more than n of the list is true, and not more
;; than (m-n) is NOT true, thereby ensuring that exactly n is true."
;;   (let ((negated-list (mapcar (curry #'list 'not) list)))
;;     (append (not-more-than-n n list) (not-more-than-n (- (length list) n) negated-list))))

;; (defmacro push-all (values place)
;;   ;; not dealing with setf expansion right now
;;   `(setf ,place (append ,values ,place)))

;; (defun step-2-sat (people-days chore-people &optional reduce-boredom)
;;   "People-days is an alist from people to a list of how many chores they should perform every
;;   day. Chores is at alist from chore names to the people assigned to that chore."
;;   (assert people-days)
;;   (let ((all-people (mapcar #'car people-days))
;;         (all-days (iota (length (cdar people-days))))
;;         (all-chores (mapcar #'car chore-people))
;;         (pdc-symbols (make-hash-table :test #'equal)))
;;     (flet ((pdc-symbol (person day chore)
;;              (or (gethash (list person day chore) pdc-symbols)
;;                  (setf (gethash (list person day chore) pdc-symbols)
;;                        (intern (format nil "~a-~a-~a-~a" person day chore (incf *smt-symbol-counter*)))))))
;;       (let* ((all-pdc-symbols
;;                (loop for person in all-people
;;                      append (loop for day in all-days
;;                                   append (loop for chore in all-chores
;;                                                collect (pdc-symbol person day chore)))))
;;              (sat-clauses))

;;         ;; Constraint 1: Each chore completed once per day
;;         (loop for day in all-days
;;               do (loop for chore in all-chores
;;                        do (push-all (exactly-n 1 (loop for person in all-people
;;                                                        collect (pdc-symbol person day chore)))
;;                                     sat-clauses)))

;;         ;; Constraint 2: Each person must complete the set number of chores each day
;;         (loop for (person . chores-per-day) in people-days
;;               do (loop for chores-today in chores-per-day
;;                        for day from 0
;;                        for chore-syms = (loop for chore in all-chores
;;                                               collect (pdc-symbol person day chore))
;;                        do (push-all (exactly-n chores-today chore-syms) sat-clauses)))

;;         ;; Constraint 3: Fairness
;;         (loop for person in all-people
;;               do (loop for (chore . people-for-chore) in chore-people
;;                        for person-chore-instances = (/ (length all-days) (length people-for-chore))
;;                        for day-syms = (loop for day in all-days
;;                                             collect (pdc-symbol person day chore))
;;                        when (member person people-for-chore)
;;                          do (push-all (exactly-n person-chore-instances day-syms) sat-clauses)))
        

;;         (sat:solve (list* 'and sat-clauses) :minisat :converter #'identity)
;;         ;; (ecase (read smt)
;;         ;;   (unsat) ; return nil
;;         ;;   (sat
;;         ;;    (let ((sat-alist (read smt)))
;;         ;;      (loop for day in all-days
;;         ;;            collect (loop for chore in all-chores
;;         ;;                          append (list chore (loop for person in all-people
;;         ;;                                                   when (= 1 (cadr (assoc (pdc-symbol person day chore) sat-alist)))
;;         ;;                                                     do (return person)
;;         ;;                                                   finally (assert nil))))))))
;;         ))))
