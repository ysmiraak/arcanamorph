(ns user)




int?
ratio?
float?
boolean?
nil?
string?
keyword?
symbol?




inc
(inc 0)
(quote inc)
'inc
(type 'inc)
(eval 'inc)
'(inc 0)
(eval '(inc 0))
(eval (eval '(inc 0)))




(+ 1 2)
(+ 1 2 3)
(+ 1)
(+)
(*)




;;;;;;;;;;
;; list ;;
;;;;;;;;;;




()
(list 1 2 3)
(cons 1 ())
(def a (cons 2 (cons 1 ())))
(def b (cons 3 a))
(def c (cons 4 a))
'(4 2 1)

(next b)
(= a (next b))
(identical? a (next b))

(first c)
(last c)

(range)
(take 5 (range))
(drop 5 (range))

(map inc (range))
(filter odd? (range))
(remove even? (range))
(filter (complement odd?) (range))
(filter (comp not odd?) (range))

(reduce + 0 c)
(reduce * 1 c)
(reductions + 0 c)
(reductions + 0 (range))




;;;;;;;;;;;;
;; vector ;;
;;;;;;;;;;;;




[]
[0 1 2]
(vec (range 4))

(def v [:a :b :c :d])
(conj v 4)
(peek v)
(pop v)
(subvec v 1 3)

(v 1)
(map v [2 0 1 0 2])
(mapv v [2 0 1 0 2])




;;;;;;;;;;;;;
;; hashmap ;;
;;;;;;;;;;;;;




{}
{:a 1 :b 2}
(def m {:name "kuan" :age 26 :type :lisper})

(conj m [:id "yk"])
(assoc m :id "yk")
(assoc m :id "yk" :type :clojurite)
(dissoc m :age)
(update m :age inc)

(def m2 {:type :clojurite :name "khuanuiel"})
(merge m m2)
(merge-with vector m m2)

(m :name)
(:name m)

(zipmap v (range))
(def i (zipmap "abcd" (range)))
(map i "baadac")




#{}
(def s #{0 1})
(conj s 2)
(conj s 0)
(s 1)
(s 3)
(filter s [2 1 0 2 1 2 0])




;;;;;;;;;;;;;;;;
;; collection ;;
;;;;;;;;;;;;;;;;




seq
count

(into v c)
(into c v)

(into m m2)
(merge m m2)
(reduce conj m m2)

(= c (vec c))




;;;;;;;;;;;;;;;;;;;
;; destructuring ;;
;;;;;;;;;;;;;;;;;;;




(let [a 1
      b (inc a)
      c (+ a b)]
  (+ a b c))

(let [[_ x] v]
  x)

(let [[_ & x] v]
  x)

(let [{x :name} m]
  x)




;;;;;;;;;;;;;;;;;;;;;
;; lambda calculus ;;
;;;;;;;;;;;;;;;;;;;;;




(* 2 2)

(let [x 2]
  (* x x))

;; lambda
(fn [x] (* x x))

;; beta
((fn [x] (* x x)) 2)

;; alpha
(fn [x] (* x x))
(fn [y] (* y y))

;; eta
(fn [x] (inc x))
inc




;;;;;;;;;;;;;
;; closure ;;
;;;;;;;;;;;;;




(let [v [1 2 3]]
  (def foo (fn [x] (conj v x))))

(foo 4)
(foo :a)




;;;;;;;;;;;;;;;;;
;; conditional ;;
;;;;;;;;;;;;;;;;;




if
or
and
cond




;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; functional programming ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;




(def square
  (fn [x]
    (* x x)))

(defn square [x]
  (* x x))

;; point-free style
((comp dec inc) 0)
((comp square inc inc) 0)
((juxt + * - /) 2 3)




(def sum (partial reduce + 0))
(def prod (partial reduce * 1))
(sum c)
(prod c)




(def contract
  (fn [f]
    (fn [x]
      (f x x))))

(map (contract *) (range))
(map (contract +) (range))




(def flip
  (fn [f]
    (fn [& args]
      (apply f (reverse args)))))

((flip /) 2 3)
((flip vector) 1 2 3)




(iterate inc 0)

(repeat 1)
(repeat 3 1)
(map (contract repeat) (range))

(square (square (square 2)))
((comp square square square) 2)
((apply comp (repeat 3 square)) 2)
(def pow (comp (partial apply comp) repeat))
((pow 3 square) 2)

(partition 2 v)
(partition 2 1 v)
(partition 3 1 v)

(partition-by (fn [n] (zero? (rem n 4))) (range))
(partition-by (comp zero? (partial (flip rem) 4)) (range))
(def div? (comp zero? (flip rem)))
(partition-by (partial div? 4) (range))

(group-by even? (range 10))




(map vector v (range))
(into {} (map vector v (range)))
(zipmap v (range))

(def mat (mapv vec (take 4 (partition 3 (range)))))
(apply mapv vector mat)
(def transpose (partial apply mapv vector))

;; create identity matrices

(let [n 4]
  (mapv (fn [row idx] (update row idx inc))
        (repeat n (vec (repeat n 0)))
        (range)))

(def eye
  (fn [n & {m :rows k :offset
            :keys [one zero]
            :or {one 1 zero 0 m n k 0}}]
    (mapv (fn [row i]
            (if (< -1 i n)
              (update row i (constantly one))
              row))
          (repeat m (vec (repeat n zero)))
          (range (- k) (- m k)))))

(transpose (eye 8))




(def xs [5 3 1 0 2 4])
(sort xs)
(sort > xs)
(sort-by (juxt odd? identity) xs)
(map peek (sort (map (juxt odd? identity) xs)))

;; (argsort xs) = [3 2 4 1 5 0]
(map xs [3 2 4 1 5 0])
(mapv first (sort-by peek (map vector (range) xs)))
(mapv first (sort-by peek (map-indexed vector xs)))

(->> xs
     (map-indexed vector)
     (sort-by peek)
     (mapv first))

((comp (partial mapv first)
       (partial sort-by peek)
       (partial map-indexed vector))
 xs)

(def argsort
  (comp (partial mapv first)
        (partial sort-by peek)
        (partial map-indexed vector)))

(argsort (argsort xs))
(argsort (argsort (map dec xs)))
(def rank (pow 2 argsort))




;;;;;;;;;;;;;;;
;; recursion ;;
;;;;;;;;;;;;;;;




(def fac
  (fn [n]
    (if (zero? n)
      1
      (* n (fac (dec n))))))

(map fac (range))

(fac 3)




;;;;;;;;;;;;;;;;;;
;; continuation ;;
;;;;;;;;;;;;;;;;;;




;; accumulator passing

(def fac-a
  (fn [n a]
    (if (zero? n)
      a
      (recur (dec n) (* n a)))))

(fac-a 3 1)




;; continuation passing

(def fac-k
  (fn [n k]
    (if (zero? n)
      (k 1)
      (recur (dec n) (fn [m] (k (* n m)))))))

(fac-k 3 identity)




;;;;;;;;;;;;;;
;; fixpoint ;;
;;;;;;;;;;;;;;




(def fac
  (fn [n]
    (if (zero? n)
      1
      (* n (fac (dec n))))))

(def fac-r
  (fn [fac-r]
    (fn [n]
      (if (zero? n)
        1
        (* n ((fac-r fac-r) (dec n)))))))

(map (fac-r fac-r) (range))

;; (fac-r fac-r) = fac-r ^ 2 = fac

(def fac'
  (fn [fac]
    (fn [n]
      (if (zero? n)
        1
        (* n (fac (dec n)))))))

(map (fac' fac) (range))
(map ((pow 6 fac') identity) (range))

;; (fix f) = (f (f (f ...))) = (pow inf f)

;; fac = (fac' fac)
;;     = (fix fac')
;;     = (fac' (fix fac'))

;; (fix f) = (f (fix f))

;; fix = (λ f (f (fix f)))

(def fix
  (fn [f]
    (f (fix f))))

(fix fac')

(def fix
  (fn [f]
    (f (fn [x]
         ((fix f) x)))))

(map (fix fac') (range))

;; the fixed-point combinator
;; (λ f ((λ x (x x))
;;       (λ x (f (x x)))))

;; the y combinator
;; (λ f ((λ x (f (x x)))
;;       (λ x (f (x x)))))

;; the z combinator
;; (λ f ((λ x (f (λ v ((x x) v))))
;;       (λ x (f (λ v ((x x) v))))))

(def z
  (fn [f]
    ((fn [x]
       (f (fn [v] ((x x) v))))
     (fn [x]
       (f (fn [v] ((x x) v)))))))

(map (z fac') (range))




;;;;;;;;;;;;;;;;;
;; corecursion ;;
;;;;;;;;;;;;;;;;;




;; catamorphism
(->> 5
     (range)
     (map inc)
     (reduce * 1))

(def fac
  (comp (partial reduce * 1)
        (partial map inc)
        range))

;; anamorphism
(->> [0 1]
     (iterate (fn [[n a]] [(inc n) (* (inc n) a)]))
     (map peek))

(->> 1
     (iterate inc)
     (reductions * 1))

;; endofunctor        f: C -> C
;; carrier obj        x: C
;; algebra          alg: f x -> x
;; coalgebra        coa: x -> f x
;; fixpoint           a: f a = a
;; initial algebra    i: f a -> a
;; terminal coalgebra j: a -> f a
;; catamorphism          i -> alg
;; anamorphism           coa -> j




;; hylomorphism
(def fib
  (fn [^long n]
    (case n
      0 0
      1 1
      (+ (fib (dec (dec n)))
         (fib (dec n))))))

(map fib (range))

(->> [0 1]
     (iterate (fn [[n m]] [m (+ n m)]))
     (map first))

(def fib (cons 0 (cons 1 (lazy-seq (map + fib (next fib))))))




(->> 2
     (iterate inc)
     (iterate (fn [[p & ns]] (remove (partial div? p) ns)))
     (map first)
     (def prime))




;; 1991 meijer fokkinga paterson
;; functional programming with bananas, lenses, envelopes and barbed wire




;;;;;;;;;;;;;;;;;;;;;;
;; meta-programming ;;
;;;;;;;;;;;;;;;;;;;;;;




(defn infix [expr]
  (if (list? expr)
    (let [[x op y] expr]
      (list op (infix x) (infix y)))
    expr))

(->> ((1 + 2) * (3 + 4))
     quote
     infix
     eval)

(defmacro ifx [expr]
  (infix expr))

(ifx ((1 + 2) * (3 + 4)))
(ifx ((true or false) and (0 < 1)))




(defmacro λ [var expr]
  `(fn [~var] ~expr))

(def z
  (λ f ((λ x (f (λ v ((x x) v))))
        (λ x (f (λ v ((x x) v)))))))

(map (z fac') (range))

((λ [a b] (+ a b)) [2 3])
((λ {x :name} x) m)




;; http://www.gigamonkeys.com/book/macros-standard-control-constructs.html
;; golang, goroutine, core.async




;; data <- (program data) <- (program (program data)) <- ...
;; data ~ text ~ lang
;; (fix program) = (program (fix program))
;; lisp = (program lisp)




;; https://en.wikipedia.org/wiki/Greenspun%27s_tenth_rule
;; http://www.paulgraham.com/quotes.html




;;;;;;;;;;;;;;;;;;;;;;;;;
;; propositional logic ;;
;;;;;;;;;;;;;;;;;;;;;;;;;




;; expr = symbol
;;      | (symbol -> symbol)
;;      | (symbol && symbol)
;;      | (symbol || symbol)
;;      | 0
;;      | 1

(defn check
  ([expr] (check expr {0 false 1 true}))
  ([expr env]
   (cond (find env expr) (list env)
         (symbol? expr)  (list (assoc env expr true) (assoc env expr false))
         :else (let [[x op y] expr]
                 (for [env (check x env)
                       env (check y env)]
                   (assoc env expr
                          (condp = op
                            '&& (and (env x) (env y))
                            '|| (or (env x) (env y))
                            '-> (or (not (env x)) (env y)))))))))

(defn truth? [expr]
  (every? #(% expr) (check expr)))

(truth? '(a || (a -> 0)))
(truth? '((1 -> 0) -> 0))




;; vector first second reverse

;; comp partial juxt flip contract

;; cps : (a -> b) -> ((a , (a -> b)) -> b)
