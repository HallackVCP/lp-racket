#lang racket

(require (for-syntax "ast.rkt"))

(provide eval-query)

;; -----------------------------------------------------------------------------
;; Substitution Management
;; A substitution is an association list: '((var . term) ...)
;; -----------------------------------------------------------------------------

; Applies a substitution to a term, resolving variables to their values.
(define (apply-substitution sub term)
  (cond
    [(var? term)
     (let ([binding (assoc (var-name term) sub)])
       (if binding
           ; Recursively apply substitution in case a var maps to another var
           (apply-substitution sub (cdr binding))
           term))]
    [(functor? term)
     (ast:functor (functor-name term)
                  (map (lambda (arg) (apply-substitution sub arg))
                       (functor-args term)))]
    [else term]))

; Composes two substitutions.
(define (compose-substitutions sub1 sub2)
  (define new-sub2 (map (lambda (pair) (cons (car pair) (apply-substitution sub1 (cdr pair)))) sub2))
  (append new-sub2 (filter (lambda (p1) (not (assoc (car p1) new-sub2))) sub1)))

;; -----------------------------------------------------------------------------
;; Unification
;; -----------------------------------------------------------------------------

; Checks if a variable occurs within a term (the "occurs check").
(define (occurs-in? var-name term sub)
  (let ([resolved-term (apply-substitution sub term)])
    (cond
      [(var? resolved-term) (equal? (var-name var-name) (var-name resolved-term))]
      [(functor? resolved-term)
       (ormap (lambda (arg) (occurs-in? var-name arg sub)) (functor-args resolved-term))]
      [else #f])))

; Unifies two terms with a given substitution. Returns a new substitution or #f for failure.
(define (unify term1 term2 sub)
  (let ([t1 (apply-substitution sub term1)]
        [t2 (apply-substitution sub term2)])
    (cond
      [(equal? t1 t2) sub]
      [(var? t1)
       (if (occurs-in? t1 t2 sub) #f (cons `(,(var-name t1) . ,t2) sub))]
      [(var? t2)
       (if (occurs-in? t2 t1 sub) #f (cons `(,(var-name t2) . ,t1) sub))]
      [(and (functor? t1) (functor? t2))
       (if (and (equal? (functor-name t1) (functor-name t2))
                (= (length (functor-args t1)) (length (functor-args t2))))
           (let/ec return
             (foldl (lambda (arg1 arg2 current-sub)
                      (let ([new-sub (unify arg1 arg2 current-sub)])
                        (if new-sub new-sub (return #f))))
                    sub
                    (functor-args t1)
                    (functor-args t2)))
           #f)]
      [else #f])))

;; -----------------------------------------------------------------------------
;; SLD Resolution Engine
;; -----------------------------------------------------------------------------

; Renames variables in a term/clause to make them unique.
(define *var-counter* (box 0))
(define (standardize-apart term)
  (let ([mapping '()])
    (define (rename-term t)
      (cond
        [(var? t)
         (let ([original-name (var-name t)])
           (cond
             [(assoc original-name mapping) => cdr]
             [else
              (let ([new-name (string->symbol (format "_G~a" (unbox *var-counter*)))])
                (set-box! *var-counter* (+ 1 (unbox *var-counter*)))
                (set! mapping (cons `(,original-name . ,(ast:var new-name)) mapping))
                (ast:var new-name))]))]
        [(functor? t)
         (ast:functor (functor-name t) (map rename-term (functor-args t)))]
        [(clause? t)
         (ast:clause (rename-term (clause-head t)) (map rename-term (clause-body t)))]
        [else t]))
    (rename-term term)))

; The core recursive solver. Returns a list of successful substitutions.
(define (solve goals sub program)
  (if (null? goals)
      (list sub)
      (let ([current-goal (car goals)]
            [remaining-goals (cdr goals)])
        (append-map
         (lambda (rule)
           (let* ([fresh-rule (standardize-apart rule)]
                  [new-sub (unify current-goal (clause-head fresh-rule) sub)])
             (if new-sub
                 (let* ([new-goals (append (clause-body fresh-rule) remaining-goals)]
                        [resolved-goals (map (lambda (g) (apply-substitution new-sub g)) new-goals)])
                   (solve resolved-goals new-sub program))
                 '())))
         program))))


;; -----------------------------------------------------------------------------
;; Main Entry Point and Result Formatting
;; -----------------------------------------------------------------------------

; Extracts the variables mentioned in the original query.
(define (get-query-vars query-ast)
  (remove-duplicates
   (let loop ([terms query-ast])
     (cond
       [(null? terms) '()]
       [(var? (car terms)) (cons (var-name (car terms)) (loop (cdr terms)))]
       [(functor? (car terms)) (append (loop (functor-args (car terms))) (loop (cdr terms)))]
       [else (loop (cdr terms))]))))


; Formats a single solution for printing.
(define (format-solution query-vars sub)
  (let ([bindings (filter-map (lambda (v)
                                (let ([binding (assoc v sub)])
                                  (if binding
                                      (format "~a = ~a" v (ast->string (cdr binding)))
                                      #f)))
                              query-vars)])
    (if (null? bindings)
        "true."
        (string-join bindings ", "))))

; Converts an AST node back to a string for printing.
(define (ast->string term)
  (cond
    [(atom? term) (atom-name term)]
    [(var? term) (var-name term)]
    [(unknow-var? term) "_"]
    [(functor? term)
     (format "~a(~a)"
             (functor-name term)
             (string-join (map ast->string (functor-args term)) ", "))]
    [else (format "~a" term)]))


; The main eval-query function as specified by the assignment.
(define (eval-query prog query)
  (set-box! *var-counter* 0) ; Reset counter for each query
  (let* ([original-query-vars (get-query-vars query)]
         [solutions (solve query '() prog)])
    (cond
      [(null? solutions) (printf "false.~n")]
      [else
       (for-each (lambda (sol)
                   (printf "~a~n" (format-solution original-query-vars sol)))
                 solutions)])
    (void)))