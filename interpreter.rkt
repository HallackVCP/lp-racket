#lang racket

(require dcc019/exercise/logic/ast
         racket/hash
         racket/match
         racket/list)

(provide eval-query)

;; --- Funções Utilitárias ---

;; Converte uma estrutura cons em uma lista padrão.
(define (cons->list lst)
  (cond
    [(null? lst) '()]
    [(pair? lst) (cons (car lst) (cons->list (cdr lst)))]
    [else (list lst)]))

;; --- Manipulação de Substituições ---

;; Uma substituição é uma lista de pares (cons variável valor).
(define (lookup-subst subst var)
  (assoc var subst))

(define (extend-subst var val subst)
  (cons (cons var val) subst))

(define (var? term)
  (match term
    [(ast:var _) #t]
    [_ #f]))

(define (functor? term)
  (match term
    [(ast:functor _ _) #t]
    [_ #f]))

;; Aplica uma substituição a um termo.
(define (apply-subst term subst)
  (match term
    [(ast:var name)
     (let ([val-pair (lookup-subst subst term)])
       (if val-pair
           (apply-subst (cdr val-pair) subst) ; Aplica recursivamente para resolver a variável.
           term))]
    [(ast:functor name args)
     (ast:functor name (map (lambda (arg) (apply-subst arg subst)) (cons->list args)))]
    [(cons head tail)
     (cons (apply-subst head subst) (apply-subst tail subst))]
    ['() '()]
    [_ term]))

;; --- Unificação com "Occurs Check" ---

;; Verifica se uma variável ocorre dentro de um termo para evitar unificações infinitas.
(define (occurs-in? var term)
  (match term
    [(ast:var _) (equal? var term)]
    [(ast:functor _ args)
     (ormap (lambda (arg) (occurs-in? var arg)) (cons->list args))]
    [(cons h t) (or (occurs-in? var h) (occurs-in? var t))]
    [_ #f]))

;; Função de unificação aprimorada que lida com variáveis, functores e o "occurs check".
(define (unify t1 t2 subst)
  (let ([s1 (apply-subst t1 subst)]
        [s2 (apply-subst t2 subst)])
    (cond
      [(equal? s1 s2) subst]
      [(var? s1)
       (if (occurs-in? s1 s2) #f (extend-subst s1 s2 subst))]
      [(var? s2)
       (if (occurs-in? s2 s1) #f (extend-subst s2 s1 subst))]
      [(and (functor? s1) (functor? s2))
       (match* (s1 s2)
         [((ast:functor name1 args1) (ast:functor name2 args2))
          (let ([args1* (cons->list args1)]
                [args2* (cons->list args2)])
            (if (and (equal? name1 name2) (= (length args1*) (length args2*)))
                (foldl
                 (lambda (pair acc)
                   (if acc
                       (unify (car pair) (cdr pair) acc)
                       #f))
                 subst
                 (map cons args1* args2*))
                #f))]
         [(_ _) #f])]
      [(and (pair? s1) (pair? s2))
       (let ([new-subst (unify (car s1) (car s2) subst)])
         (if new-subst
             (unify (cdr s1) (cdr s2) new-subst)
             #f))]
      [else #f])))

;; --- Renomeação de Variáveis ---

;; Gera nomes de variáveis novos e únicos para evitar colisões.
(define counter 0)
(define (fresh-var)
  (set! counter (+ counter 1))
  (ast:var (string->symbol (format "_G~a" counter))))

;; Renomeia as variáveis em um termo de forma recursiva.
(define (rename-term term env)
  (match term
    ;; *********************** INÍCIO DA CORREÇÃO ***********************
    ;; Ao encontrar uma variável anônima, simplesmente a substituímos por
    ;; uma variável nova e única, garantindo o comportamento correto.
    [(ast:unknow-var)
     (values (fresh-var) env)]
    ;; ************************ FIM DA CORREÇÃO *************************

    ;; *********************** INÍCIO DA CORREÇÃO FINAL ***********************
    ;; Adicionamos casos para eq e neq, para garantir que as variáveis
    ;; dentro deles também sejam renomeadas corretamente.
    [(ast:eq t1 t2)
     (let-values ([(new-t1 env*) (rename-term t1 env)])
       (let-values ([(new-t2 env**) (rename-term t2 env*)])
         (values (ast:eq new-t1 new-t2) env**)))]
    [(ast:neq t1 t2)
     (let-values ([(new-t1 env*) (rename-term t1 env)])
       (let-values ([(new-t2 env**) (rename-term t2 env*)])
         (values (ast:neq new-t1 new-t2) env**)))]
    ;; ************************ FIM DA CORREÇÃO FINAL *************************

    [(ast:var name)
     (cond [(assoc term env) => (lambda (pair) (values (cdr pair) env))]
           [else
            (let ([new (fresh-var)])
              (values new (cons (cons term new) env)))])]
    ;; CORREÇÃO: Substituído map-accum por um loop explícito.
    [(ast:functor name args)
     (let loop ([args-list (cons->list args)]
                [acc-args '()]
                [acc-env env])
       (if (null? args-list)
           (values (ast:functor name (reverse acc-args)) acc-env)
           (let-values ([(arg* env*) (rename-term (car args-list) acc-env)])
             (loop (cdr args-list)
                   (cons arg* acc-args)
                   env*))))]
    [(cons head tail)
     (let-values ([(new-head env*) (rename-term head env)])
       (let-values ([(new-tail env**) (rename-term tail env*)])
         (values (cons new-head new-tail) env**)))]
    ['() (values '() env)]
    [_ (values term env)]))

;; Renomeia todas as variáveis em uma cláusula.
(define (rename-clause clause)
  (match clause
    [(ast:clause head body)
     (let-values ([(new-head env) (rename-term head '())])
       ;; CORREÇÃO: Substituído map-accum por um loop explícito.
       (let loop ([body-list (cons->list body)]
                  [acc-body '()]
                  [acc-env env])
         (if (null? body-list)
             (ast:clause new-head (reverse acc-body))
             (let-values ([(b* env*) (rename-term (car body-list) acc-env)])
               (loop (cdr body-list)
                     (cons b* acc-body)
                     env*)))))]))

;; --- Resolução SLD ---

;; Função auxiliar para aplicar substituições no corpo de uma cláusula
(define (apply-subst-body body subst)
  (map (lambda (term) (apply-subst term subst)) body))

;; *********************** INÍCIO DO TRATAMENTO DE RECURSÃO ***********************
;; Obtém o nome e a aridade de um predicado para identificação única
(define (get-predicate-info term)
  (cond
    [(ast:functor? term)
     (list (ast:functor-name term) (length (cons->list (ast:functor-args term))))]
    [(ast:atom? term)
     (list (ast:atom-name term) 0)]
    [else #f]))

;; Testa se todos os argumentos de um termo são variáveis
(define (all-args-are-vars? term)
  (cond
    [(ast:atom? term) #t]
    [(ast:functor? term)
     (let ([args (cons->list (ast:functor-args term))])
       (andmap ast:var? args))]
    [else #f]))

;; Identifica cláusulas que são reflexos diretos (tautologias perigosas)
;; Exemplo: above(X, Y) :- above(X, Y).
(define (is-dangerous-self-reference? clause)
  (let ([head (ast:clause-head clause)]
        [body (cons->list (ast:clause-body clause))])
    (and (= 1 (length body))
         (let ([body-goal (first body)])
           (and (equal? (get-predicate-info head) (get-predicate-info body-goal))
                (all-args-are-vars? head)
                (all-args-are-vars? body-goal))))))
;; ************************ FIM DO TRATAMENTO DE RECURSÃO *************************

;; Função principal de resolução que processa uma lista de objetivos.
(define (resolve goals prog subst)
  (cond
    [(null? goals) (list subst)]
    [else
     (let* ([goal (car goals)]
            [rest-goals (cdr goals)]
            [goal-substituted (apply-subst goal subst)])
       (match goal-substituted
         [(ast:eq t1 t2)
          (let ([new-subst (unify t1 t2 subst)])
            (if new-subst
                (resolve rest-goals prog new-subst)
                '()))]
         [(ast:neq t1 t2)
          ;; A versão anterior era suscetível a um bug.
          ;; Esta versão é mais robusta e garante que a comparação
          ;; seja feita nos valores FINAIS das variáveis.
          (let ([s1 (apply-subst t1 subst)]
                [s2 (apply-subst t2 subst)])
            (if (unify s1 s2 '())
                '() ; Se os valores FINAIS podem ser unificados, eles NÃO são desiguais -> Falha.
                (resolve rest-goals prog subst)))] ; Se não podem, eles são desiguais -> Sucesso.
         [(ast:functor name args)
          (let ([clauses (hash-ref prog name '())])
            ;; *********************** FILTRO DE TAUTOLOGIAS PROBLEMÁTICAS ***********************
            ;; Remove cláusulas que são autoreferências perigosas para prevenir loops infinitos
            (let ([safe-clauses 
                   (filter (lambda (clause) 
                             (not (is-dangerous-self-reference? clause))) 
                           clauses)])
              ;; ************************ FIM DO FILTRO *************************
              (apply append
                     (for/list ([clause safe-clauses])
                       (let* ([renamed-clause (rename-clause clause)]
                              [new-head (ast:clause-head renamed-clause)]
                              [new-body (ast:clause-body renamed-clause)])
                         (let ([new-subst (unify goal-substituted new-head subst)])
                           (if new-subst
                               (let ([new-body-list (cons->list new-body)])
                                 (resolve (append new-body-list rest-goals) prog new-subst))
                               '())))))))]
         [_ '()]))]))

;; --- Formatação da Saída ---

;; Extrai todas as variáveis de uma consulta.
(define (get-vars-from-query term)
  (remove-duplicates
   (let loop ([t term])
     (match t
       [(ast:var _) (list t)]
       [(ast:functor _ args)
        (apply append (map loop (cons->list args)))]
       [(cons h tl)
        (append (loop h) (loop tl))]
       [_ '()]))))

;; Converte um termo em uma string legível.
(define (pretty-print-term term)
  (match term
    [(ast:var name) (format "~a" name)]
    [(ast:atom name) (format "~a" name)]
    [(ast:functor name args)
     (format "~a(~a)"
             name
             (string-join (map pretty-print-term (cons->list args)) ", "))]
    [_ (format "~a" term)]))

;; --- Função Principal ---

(define (eval-query prog query)
  ;; Indexa as cláusulas do programa pelo nome do predicado para acesso rápido.
  (define prog-db
    (foldl
     (lambda (clause db)
       (match clause
         [(ast:clause (ast:functor name args) body)
          (let* ([args-list (cons->list args)]
                 [body-list (if (list? body) body (cons->list body))]
                 [fixed-clause (ast:clause (ast:functor name args-list) body-list)])
            (hash-update db name (lambda (cs) (cons fixed-clause cs)) '()))]
         [_ db]))
     (hash)
     prog))

  (let* ([query-list (cons->list query)]
         [query-vars (get-vars-from-query query-list)]
         [results (resolve query-list prog-db '())])

    (cond
      [(null? results) (printf "não\n")]
      [(null? query-vars) (printf "sim\n")]
      [else
       (for-each
        (lambda (subst)
          (printf "  ~a\n"
                  (string-join
                   (map (lambda (q-var)
                          (format "~a = ~a"
                                  (ast:var-name q-var)
                                  (pretty-print-term (apply-subst q-var subst))))
                        query-vars)
                   ", ")))
        results)]))
  
  ; ADICIONE ESTA LINHA DE VOLTA NO FINAL
  #'(void))