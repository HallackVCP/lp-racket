#lang racket

(require dcc019/exercise/logic/ast)

(provide eval-query)




;; Utilidades para manipulação de AST

(define (is-fact? clause)
  (null? (ast:clause-body clause)))


(define (is-rule? clause)
  (not (null? (ast:clause-body clause))))

;; Indexa o programa por predicado (nome do head)
(define (index-program prog)
  (define table (make-hash))
  (for ([clause prog])
  (define head (ast:clause-head clause))
    (define pred-name
      (cond
        [(ast:atom? head) (ast:atom-name head)]
        [(ast:functor? head) (ast:functor-name head)]
        [else #f]))
    (when pred-name
      (hash-update! table pred-name (λ (lst) (cons clause lst)) '())))
  table)

;; Unificação simples (apenas para átomos e variáveis)

(define (ensure-list x)
  (cond
    [(null? x) '()]
    [(list? x) x]
    [(pair? x) (cons (car x) (ensure-list (cdr x)))]
    [else (list x)]))

(define (unify t1 t2 subst)
  (cond
    [(equal? t1 t2) subst]
    [(ast:var? t1) (extend-subst t1 t2 subst)]
    [(ast:var? t2) (extend-subst t2 t1 subst)]
    [(and (ast:functor? t1) (ast:functor? t2)
          (equal? (ast:functor-name t1) (ast:functor-name t2))
          (= (length (ensure-list (ast:functor-args t1))) (length (ensure-list (ast:functor-args t2)))))
     (unify-args (ensure-list (ast:functor-args t1)) (ensure-list (ast:functor-args t2)) subst)]
    [else #f]))


(define (unify-args args1 args2 subst)
  (let ([l1 (ensure-list args1)]
        [l2 (ensure-list args2)])
    (if (null? l1)
        subst
        (let ([s1 (unify (car l1) (car l2) subst)])
          (and s1 (unify-args (cdr l1) (cdr l2) s1))))))

(define (extend-subst var val subst)
  (cond
    [(assoc var subst) (if (equal? (cdr (assoc var subst)) val) subst #f)]
    [else (cons (cons var val) subst)]))

;; Resolução SLD (simplificada)
(define (sld-resolve goals prog-table subst)
  (cond
    [(null? goals) (list subst)]
    [else
     (let* ([goal (car goals)]
            [pred-name (cond
                         [(ast:atom? goal) (ast:atom-name goal)]
                         [(ast:functor? goal) (ast:functor-name goal)]
                         [else #f])]
      [clauses (if pred-name (hash-ref prog-table pred-name '()) '())])
    (apply append
        (for/list ([clause clauses])
       (let* ([clause-head (ast:clause-head clause)]
           [clause-body (ast:clause-body clause)]
           [new-subst (unify goal clause-head subst)])
         (if new-subst
          (sld-resolve (append (ensure-list clause-body) (cdr goals)) prog-table new-subst)
          '())))))]))

;; Função principal


(define (subst->string subst)
  (if (null? subst)
      "sim"
      (string-join
        (for/list ([s subst])
          (string-join
            (for/list ([pair s])
              (format "~a = ~a" (ast:var-name (car pair)) (cdr pair)))
            ", "))
        "\n")))


(define (eval-query prog query)
  (define prog-table (index-program prog))
  (define goals (if (list? query) query (list query)))
  (define results (sld-resolve goals prog-table '()))

  ; 1. Imprime o resultado da consulta para o usuário (ação de efeito colateral)
  (cond
    [(null? results) (displayln "não")]
    [(and (= (length results) 1) (null? (car results))) (displayln "sim")]
    [else (displayln (subst->string results))])

  ; 2. Retorna um objeto de sintaxe vazio para satisfazer o contrato do REPL
  #'(void))

