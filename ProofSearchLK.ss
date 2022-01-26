#lang racket

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; fonctions de base

(define (neg? F) (eq? F '!))
(define (and? F) (eq? F '^))
(define (or? F) (eq? F 'v))
(define (imp? F) (eq? F '->))
(define (equ? F) (eq? F '<->))
(define (top? F) (and (integer? F) (= F 1)))
(define (bot? F) (and (integer? F) (= F 0)))
(define (tob? F) (or (top? F) (bot? F)))
(define (symbLog? F) (or (top? F) (bot? F) (and? F) (or? F) (neg? F) (imp? F) (equ? F)))
(define (conBin? F) (or (and? F) (or? F) (imp? F) (equ? F)))
(define (symbProp? F) (and (symbol? F) (not (symbLog? F))))
(define (atomicFbf? F) (or (symbProp? F) (top? F) (bot? F)))

(define (fbf? F)
  (cond ((atomicFbf? F) #t)
        ((list? F) (cond ((and (= (length F) 2) (neg? (car F))) (fbf? (cadr F)))
                         ((and (= (length F) 3) (conBin? (car F))) (and (fbf? (cadr F)) (fbf? (caddr F))))
                         (else #f)))
        (else #f)))

(define (conRac F) (car F))
(define (fils F) (cadr F))
(define (filsG F) (cadr F))
(define (filsD F) (caddr F))
(define (negFbf? F) (and (not (atomicFbf? F)) (neg? (conRac F))))
(define (conjFbf? F) (and (not (atomicFbf? F)) (and? (conRac F))))
(define (disjFbf? F) (and (not (atomicFbf? F)) (or? (conRac F))))
(define (implFbf? F) (and (not (atomicFbf? F)) (imp? (conRac F))))
(define (equiFbf? F) (and (not (atomicFbf? F)) (equ? (conRac F))))
(define (andFbf? f) (and (not (atomicFbf? f)) (and? (conRac f))))
(define (orFbf? f) (and (not (atomicFbf? f)) (or? (conRac f))))

(define (ensSP f)
  (cond ((atomicFbf? f) (if (symbProp? f) (list f) '()))
        ((negFbf? f) (ensSP (fils f)))
        (else (set-union (ensSP (filsG f)) (ensSP (filsD f))))))

(define (symbV s i)
  (cond ((null? i) s)
        ((eq? s (caar i)) (cdar i))
        (else (symbV s (cdr i)))))

(define (negV b)
  (if (tob? b) (- 1 b) (list '! b)))

(define (andV a b)
  (let ((toba? (tob? a)) (tobb? (tob? b)))
    (cond ((and toba? tobb?) (* a b))
          ((and toba? (not tobb?)) (if (= a 0) 0 b))
          ((and (not toba?) tobb?) (if (= b 0) 0 a))
          (else (list '^ a b)))))

(define (orV a b)
  (let ((toba? (tob? a)) (tobb? (tob? b)))
    (cond ((and toba? tobb?) (if (= (+ a b) 0) 0 1))
          ((and toba? (not tobb?)) (if (= a 0) b 1))
          ((and (not toba?) tobb?) (if (= b 0) a 1))
          (else (list 'v a b)))))

(define (impV a b)
  (let ((toba? (tob? a)) (tobb? (tob? b)))
    (cond (toba? (if (= a 0) 1 b))
          (tobb? (if (= b 0) (list '! a) 1))
          (else (list '-> a b)))))

(define (equV a b)
  (let ((toba? (tob? a)) (tobb? (tob? b)))
    (cond ((and toba? tobb?) (= a b))
          ((and toba? (not tobb?)) (if (= a 0) (list '! b) b))
          ((and (not toba?) tobb?) (if (= b 0) (list '! a) a))
          (else (if (eq? a b) 1 (list '<-> a b))))))

(define (valV f i)
  (cond
    ((tob? f) f)
    ((symbProp? f) (symbV f i))
    ((neg? (conRac f)) (negV (valV (fils f) i)))
    ((and? (conRac f)) (andV (valV (filsG f) i) (valV (filsD f) i)))
    ((or? (conRac f)) (orV (valV (filsG f) i) (valV (filsD f) i)))
    ((imp? (conRac f)) (impV (valV (filsG f) i) (valV (filsD f) i)))
    (else (equV (valV (filsG f) i) (valV (filsD f) i)))))

(define (opAll l op)
  (cond ((null? l) '())
        ((null? (cdr l)) (car l))
        (else (list op (car l) (opAll (cdr l) op)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; programme de dpll

(define (dpll t1 t2)
  (let* ((negC (list '! (opAll t2 'v)))
         (S (opAll (cons negC t1) '^))
         (LS (ensSP S)))
    (let loop ((S S) (LS LS) (I '()))
      (if (null? LS)
          I
          (let* ((I0 (list (cons (car LS) 0))) (V0 (valV S I0))
                 (I1 (list (cons (car LS) 1))) (V1 (valV S I1)))
            (cond ((and (bot? V0) (bot? V1)) '())
                  ((bot? V0) (loop V1 (cdr LS) (append I I1)))
                  (else (let ((N (loop V0 (cdr LS) (append I I0))))
                          (if (or (bot? V1) (> (length N) 0))
                              N
                              (loop V1 (cdr LS) (append I I1)))))))))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; projet recherche de preuve

(define (allSymbol? t)
  (if (null? t)
      #f
      (let ((r (symbProp? (car t))))
        (if (not r)
            #f
            (if (null? (cdr t))
                r
                (allSymbol? (cdr t)))))))

(define (axiom? t1 t2)
  (if (not (and (allSymbol? t1) (allSymbol? t2)))
      #f
      (if (member (car t1) t2)
          #t
          (axiom? (cdr t1) t2))))

(define (firstOp t)
  (if (null? t)
      '()
      (if (list? (car t))
          (caar t)
          (firstOp (cdr t)))))

(define (splitOp t op?)
  (let loop ((t t) (a '()) (b '()))
    (if (null? t)
        (cons a b)
        (if (op? (car t))
            (loop '() (car t) (append b (cdr t)))
            (loop (cdr t) a (append b (list (car t))))))))

(define (negLeft t1 t2)
  (let ((c (splitOp t1 negFbf?)))
    (cons (cons (cdr c) (cons (cadar c) t2)) '())))

(define (negRight t1 t2)
  (let ((c (splitOp t2 negFbf?)))
    (cons (cons (cons (cadar c) t1) (cdr c)) '())))



(define (andLeft t1 t2)
  (let ((c (splitOp t1 andFbf?)))
    (cons (append (cdar c) (cdr c)) t2)))

(define (andRight t1 t2)
  (let ((c (splitOp t2 andFbf?)))
    (cons (cons t1 (cons (cadar c) (cdr c)))
          (cons t1 (cons (caddar c) (cdr c))))))

(define (orLeft t1 t2)
  (let ((c (splitOp t1 orFbf?)))
    (cons (cons (cons (cadar c) (cdr c)) t2)
          (cons (cons (caddar c) (cdr c)) t2))))


(define (orRight t1 t2)
  (let ((c (splitOp t2 orFbf?)))
    (cons t1 (append (cdar c) (cdr c)))))

(define (impLeft t1 t2)
  (let ((c (splitOp t1 implFbf?)))
    (cons (cons (cdr c) (cons (cadar c) t2))
          (cons (cons (caddar c) (cdr c)) t2))))

(define (impRight t1 t2)
  (let ((c (splitOp t2 implFbf?)))
    (cons (cons (cons (cadar c) t1) (cons (caddar c) (cdr c))) '())))

(define (allAX arbre)
  (if (null? arbre)
      #f
      (let ((rule (caddr arbre))
            (l (cadddr arbre))
            (r (cadr (cdddr arbre))))
        (if (and (null? l) (null? r))
            (eq? rule 'AX)
            (if (null? l)
                (allAX r)
                (if (null? r)
                    (allAX l)
                    (and (allAX l) (allAX r))))))))

(define (inference t1 t2)
  (cond ((axiom? t1 t2)
         (list t1 t2 'AX '() '()))
        ((not (or (null? t1) (allSymbol? t1)))
         (let ((op (firstOp t1)))
           (cond ((neg? op)
                  (let* ((c (negLeft t1 t2))
                         (l (inference (caar c) (cdar c))))
                    (list t1 t2 '¬G l '())))
                 ((and? op)
                  (let* ((c (andLeft t1 t2))
                         (l (inference (car c) (cdr c))))
                    (list t1 t2 '∧G l '())))
                        
                 ((or? op)
                  (let* ((c (orLeft t1 t2))
                         (l (inference (caar c) (cdar c)))
                         (r (inference (cadr c) (cddr c))))
                    (list t1 t2 '∨G l r)))
                 (else
                  (let* ((c (impLeft t1 t2))
                         (l (inference (caar c) (cdar c)))
                         (r (inference (cadr c) (cddr c))))
                    (list t1 t2 '->G l r))))))
        ((not (or (null? t2) (allSymbol? t2)))
         (let ((op (firstOp t2)))
           (cond ((neg? op)
                  (let* ((c (negRight t1 t2))
                         (l (inference (caar c) (cdar c))))
                    (list t1 t2 '¬D l '())))
                 ((and? op)
                  (let* ((c (andRight t1 t2))
                         (l (inference (caar c) (cdar c)))
                         (r (inference (cadr c) (cddr c))))
                    (list t1 t2 '∧D l r)))
                 ((or? op)
                  (let* ((c (orRight t1 t2))
                         (l (inference (car c) (cdr c))))
                    (list t1 t2 '∨D l '())))
                
                 (else
                  (let* ((c (impRight t1 t2))
                         (l (inference (caar c) (cdar c))))
                    (list t1 t2 '->D l '()))))))
        (else (list t1 t2 'NO '() '()))))


(define (printIndents prof tmp)
  (let loop ((n 0))
    (if (>= n prof)
        (begin (display "│      "))
        (begin
          (if (member n tmp)
              (display "│      ")
              (display "       "))
          (loop (+ n 1))))))

(define (printBranchIndents prof tmp)
  (let loop ((n 0))
    (if (>= n prof)
        (begin (display "├──────"))
        (begin
          (if (member n tmp)
              (display "│      ")
              (display "       "))
          (loop (+ n 1))))))

(define (printLastBranchIndents prof tmp)
  (let loop ((n 0))
    (if (>= n prof)
        (begin (display "└──────"))
        (begin
          (if (member n tmp)
              (display "│      ")
              (display "       "))
          (loop (+ n 1))))))

(define (printSearchTree arbre prof tmp)
  (if (null? arbre)
      (begin (display ""))
      (let ((l (car (cdddr arbre))) (r (cadr (cdddr arbre))))
        (begin
          (display (car arbre))
          (display " ⊢ ")
          (display (cadr arbre))
          (display " Règle: ")
          (display (caddr arbre))
          (newline)
          (if (or (not (null? l)) (not (null? r)))
              (begin
                (begin
                  (printIndents prof tmp)
                  (newline))
                (cond ((null? l)
                       (begin
                         (printLastBranchIndents prof tmp)
                         (printSearchTree r (+ prof 1) tmp)))
                      ((null? r)
                       (begin
                         (printLastBranchIndents prof tmp)
                         (printSearchTree l (+ prof 1) tmp)))
                      (else
                       (begin
                         (printBranchIndents prof tmp)
                         (printSearchTree l (+ prof 1) (cons prof tmp))
                         (printIndents prof tmp)
                         (newline)
                         (printLastBranchIndents prof tmp)
                         (printSearchTree r (+ prof 1) tmp)))))
              (begin (display "")))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; prove code


(define (prove hypotheses conclusions)
  (let ((a (dpll hypotheses conclusions)))
    (let ((t (inference hypotheses conclusions)))
          (printSearchTree t 0 '())
          a
          )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;Exemples


(prove '((^ A B)) '(B)) (newline)
(prove '(B) '((v A B))) (newline)
(prove '((-> A (v N Q)) (! (v N (! A)))) '((-> A Q))) (newline)
(prove '((-> A B) (! A)) '((! B))) (newline)
(prove '((-> A B) (-> A C)) '((-> B C))) (newline)
(prove '((-> A B) (-> A C)) '((-> B C) (-> A C))) (newline)
(prove '((-> J (! (! I))) (-> (v H G) J) (-> F H) (^ G F)) '(I)) (newline)
(prove '((^ (v A B) C)) '((-> C A))) (newline)
(prove '((^ (^ A B) (! E))) '((v (^ A B) E))) (newline) (newline)
(prove '(A (-> (^ B E) A) B E) '((^ (-> (^ A B) B) E))) (newline) 
(prove '((-> S (v B T))(-> (v B A)(^ R M)) (! R)) '((-> S T)))

