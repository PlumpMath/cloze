(ns cloze.cloze
  (:require [clojure.zip :as zip]
            [clojure.test :as t]
            [cloze.zip-utils :as zu]))

;; ============================================================
;; clozeur

;; no attempt to define polymorphic interface for now, but room to in
;; the future if that seems like a coolthing

(declare collapse-walk expr-zip clozeur?)

(defrecord Clozeur [variables bindings expression])

(defn collapse [expr]
  (collapse-walk-1 expr))

 ;; sloppy for now
(defn collapse-all [expr] ;; need not be clozeur
  (zip/root
    (zu/zip-prewalk (expr-zip expr)
      #(if (clozeur? %) (collapse %) %))))

;; keeping static type stuff internal to fns for now, out of deference
;; to potential future polymorphism
(defn bindings [clz]
  (let [^Clozeur clz clz]
    (.bindings clz)))

(defn variables [clz]
  (let [^Clozeur clz clz]
    (.variables clz)))

(defn expression [clz]
  (let [^Clozeur clz clz]
    (.expression clz)))

(defn put-bindings [clz bndgs]
  (assert ;; perhaps this should not be enforced
    (every? (variables clz) (keys bndgs))
    (str "variables " (remove (variables clz) (keys bndgs)) " not in clozeur"))
  (assoc clz :bindings bndgs))

(defn put-variables [clz vs]
  (assoc clz :variables vs))

(defn put-expression [clz expr]
  (assoc clz :expression expr))

(defn bind
  ([clz v x]
   (put-bindings clz
     (assoc (bindings clz) v x)))
  ([clz v x & ys]
   (put-bindings clz
     (reduce  ;; should be application transducers defined for 2 - 20 arguments
       (fn [bldg [x y]]
         (assoc bldg x y))
       (bindings clz)
       (partition 2
         (list* v x ys))))))

;; now need to make it work wiht usual clojure associative interface...
;; in the meantime:

(defn bind-in [clz [k & ks] v]
  (if ks
    (bind clz k (bind-in (get (.bindings clz) k) ks v))
    (bind clz k v)))

(defn unbind [clz v]
  (-> clz
    (put-bindings (dissoc (bindings clz) v))
    (put-variables (dissoc (variables clz) v))))

;; this could get more elaborate
(defn clozeur? [x]
  (instance? Clozeur x))

(defn free [clz]
  (reduce dissoc
    (variables clz)
    (keys (bindings clz))))

(defn clozeur
  ([variables expression]
   (clozeur variables {} expression))
  ([variables bindings expression]
   (let [v (into variables (keys bindings))]
     (assert (set? v)) 
     (Clozeur. v
       bindings
       expression))))

;; ============================================================
;; expr-zip

;; TODO: polymorphic version

(defn- expr-branch? [x]
  (or (coll? x) (clozeur? x)))

(defn- expr-children [x]
  (cond
    (clozeur? x) (list (variables x) (bindings x) (expression x)) ;; meh maybe should do it more map-like
    (coll? x) (seq x) ;; should be seqable or something
    :else (throw (Exception. "requires either standard clojure collection or clozeur"))))

(defn- list-like? [x]
  (or (seq? x) (instance? clojure.lang.MapEntry x)))

(defn- expr-make-node [x kids]
  (cond
    (list-like? x) (with-meta (into (empty x) (reverse kids)) (meta x))
    (clozeur? x) (let [[vs bndgs expr] kids]
                   (-> x
                     (put-variables vs)
                     (put-bindings bndgs)
                     (put-expression expr)
                     (with-meta (meta x))))
    (coll? x) (with-meta (into (empty x) kids) (meta x))
    :else (throw (Exception. "requires either standard clojure collection or clozeur"))))

(defn expr-zip [x]
  (zip/zipper
    expr-branch?
    expr-children
    expr-make-node
    x))

;; ============================================================
;; ctx-zip

(defn- znext [loc]
  (let [nxt (zip/next loc)]
    (when-not (zip/end? nxt)
      nxt)))

(defrecord CtxNode [ctx expr])

(defn ctx-branch? [^CtxNode node]
  (expr-branch? (.expr node)))

;; defining this NOT as a higher-order zipper per se, because those are headaches
(defn ctx-children [^CtxNode node]
  (cast CtxNode node)
  (let [ctx (.ctx node)
        expr (.expr node)
        children-ctx (if (clozeur? expr)
                       (merge ctx (bindings expr))
                       ctx)]
    (for [cexpr (expr-children expr)]
      (CtxNode. children-ctx cexpr))))

(defn ctx-make-node [^CtxNode node, kids]
  (let [ctx (.ctx node)
        expr (.expr node)
        res (CtxNode.
              ctx
              (expr-make-node expr
                (for [^CtxNode node2 kids]
                  (.expr node2))))]
    res))

;; check order of the following
(defn- ctx-zip [ctx-node]
  (assert (instance? CtxNode ctx-node))
  (zip/zipper
    ctx-branch?
    ctx-children
    ctx-make-node
    ctx-node))

;; following runs right into variable capturing awkwardness. Can deal
;; with it in the obvious ways - rewrite subclozeurs with gensyms, or
;; just capture the variables because that's what you're doing
(defn absorb [clz]
  (loop [loc (expr-zip (expression clz)), clzs '()]
    (if-let [nxt (znext loc)]
      (let [nd (zip/node nxt)]
        (if (clozeur? nd)
          (recur
            (zu/zip-up-to-right (zip/replace nxt (expression clz)))
            (conj clzs nxt))
          (recur nxt clzs)))
      (let [expr (zip/root loc)]
        (-> clz
          (put-expression expr)
          (put-variables (into (variables clz) (map variables clzs)))
          (put-bindings (into (bindings clz) (map bindings clzs))))))))

(defn minimize
  "Let res be clz with all its bound variables removed. If res has no
  free variables, minimize-clozeur returns (expression clz), otherwise
  returns res. Does not do replacement, so if clz has variables bound
  but not yet replaced in (expression clz) they will effectively
  become open symbols; to avoid this, use collapse instead."
  [clz]
  (assert (clozeur? clz) "requires clozeur")
  (let [vs2 (reduce disj
              (variables clz)
              (keys (bindings clz)))]
    (if (empty? vs2)
      (expression clz)
      (-> clz
        (put-bindings {})
        (put-variables vs2)))))

;; punt on specifics of polymorphism for now; can always back out of
;; the following. (could wrap it up in another level of indirection if
;; you're really being paranoid but probably no reason. Especially
;; since this stuff is going to be in an internal namespace for a
;; moment, and anyway you can always hoist the function signature if
;; you really want that sort of crap).

;; public or private? hm
;; just collapses the current clz. for collapse-all, use this
;; recursively or whatever I guess. Might be getting a little anal
;; with the types, could make this accept both clozeurs and CtxNodes


;; should be imperatively setting this during rewrite stages below; am not.
(def ^:dynamic *bail* 1000)

(defmacro bail-up [i & body]
  `(binding [*bail* (when *bail* (+ *bail* ~i))]
     ~@body))

;; just one level
(defn collapse-cloze
  ([clz]
   (collapse-cloze clz {}))
  ([clz ctx0]
   (assert (clozeur? clz) "requires clozeur") ;; fix this, perhaps at collapse (above)
   (let [bndgs (bindings clz)]
     (loop [prev-loc (ctx-zip ;; tricksy
                       (CtxNode. ctx0 ;; riiight?
                         (expression clz)))
            loc (znext prev-loc)
            i 0]
       (if (and *bail* (<= *bail* i))
         (throw (Exception. (str  "reached max iterations, *bail* = " *bail*)))
         (if loc
           (let [^CtxNode node (zip/node loc)
                 bndgs2 (reduce dissoc bndgs (keys (.ctx node)))]
             (if-let [[_ expr2] (find bndgs2 (.expr node))]
               (let [loc2 (zip/replace loc (assoc node :expr expr2))]
                 (recur loc2 (zu/zip-up-to-right loc2) (inc i)))
               (recur loc (znext loc) (inc i))))
           (let [^CtxNode r (zip/root prev-loc)]
             (minimize (put-expression clz (.expr r)))) ))))))

;; will NOT burrow into replacements
(defn collapse-walk-1 [expr]
  (loop [prev-loc nil
         loc (expr-zip expr)
         i 0]
    (if (and *bail* (<= *bail* i))
      (throw (Exception. (str  "reached max iterations, *bail* = " *bail*)))
      (if loc
        (let [expr (zip/node loc)]
          (if (clozeur? expr)
            (let [loc2 (zip/replace loc
                         (bail-up i (collapse-cloze expr)))]
              (recur loc2 (zu/zip-up-to-right loc2) (inc i)))
            (recur loc (znext loc) (inc i))))
        (zip/root prev-loc)))))

 ;; WILL burrow into replacements; rather dangerous
(defn collapse-walk-deep [expr]
  (zip/root
    (loop [prev-loc nil
           loc (expr-zip expr)
           i 0]
      (if (and *bail* (<= *bail* i))
        (throw (Exception. (str  "reached max iterations, *bail* = " *bail*)))
        (if loc
          (let [expr (zip/node loc)]
            (recur loc
              (znext
                (if (clozeur? expr)
                  (zip/replace loc
                    (bail-up i (collapse-cloze expr)))
                  loc))
              (inc i)))
          prev-loc)))))

(defn- fixpoint [f x]
  (loop [x x]
    (let [y (f x)]
      (if (= y x)
        y
        (recur y)))))

;; like mathematica's replace-all-repeated. goes to fixpoint. not
;; cheap, and might not terminate, but the best.
(defn collapse-walk-repeated [expr]
  (fixpoint collapse-walk-1 expr))

;; ============================================================
;; preliminary tests

(comment
  (t/deftest test-collapse
    (let [clz1 (clozeur '#{a b x}
                 '(fn [x]
                    (when a b)))]
      (t/is (= (collapse
                 (bind clz1
                   'x 'x
                   'a '(number? x)
                   'b '(+ 13 x)))
              '(fn [x]
                 (when (number? x)
                   (+ 13 x)))))
      (let [clz2 (bind clz1
                   'x 'num
                   'a '(number? num)
                   'b (bind clz1
                        'x 'x
                        'a '(odd? num)
                        'b '(+ 13 x)))]
        (t/is 
          (= (collapse-all clz2)
            '(fn [num]
               (when (number? num)
                 (fn [x]
                   (when (odd? num)
                     (+ 13 x)))))))))))
