(ns cloze.cloze
  (:require [clojure.zip :as zip]
            [clojure.test :as t]
            [cloze.zip-utils :as zu]
            [arcadia.internal.map-utils :as mu])) ;; TEMP

;; ============================================================
;; utils

;; ============================================================
;; clozeur

;; no attempt to define polymorphic interface for now, but room to in
;; the future if that seems like a coolthing

(declare collapse-walk expr-zip clozeur?)

(defrecord Clozeur [variables bindings expression])

(defn collapse [clz]
  (collapse-walk clz))

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
  (assert ;; not really sure if I should enforce this. Maybe not, you know?
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

(defn clozeur [variables expression]
  (Clozeur. variables {} expression))

;; ============================================================
;; expr-zip

;; I guess these should be polymorphic. Behold: they aren't. Fix later.
(defn- expr-branch? [x]
  (or (coll? x) (clozeur? x)))

(defn- expr-children [x]
  (cond
    (clozeur? x) (list (variables x) (bindings x) (expression x)) ;; meh maybe should do it more map-like
    (coll? x) (seq x) ;; bla. should be seqable or something, I know.
    :else (throw (Exception. "requires either standard clojure collection or clozeur"))))

(defn- list-like? [x]
  (or (seq? x) (instance? clojure.lang.MapEntry x)))

(defn- expr-make-node [x kids]
  (cond
    (list-like? x) (with-meta (into (empty x) (reverse kids)) (meta x))
    (coll? x) (with-meta (into (empty x) kids) (meta x))
    (clozeur? x) (let [[vs bndgs expr] kids]
                   (->
                     (put-variables vs)
                     (put-bindings bndgs)
                     (put-expression expr)
                     (with-meta (meta x))))
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

;; should probably implement a protocol or some bullshit
(defrecord CtxNode [ctx expr])

(def log (atom []))

(defn ctx-branch? [^CtxNode node]
  (swap! log conj node)
  (expr-branch? (.expr node)))

;; hmmmm what's the children? Does this cover traversing into the
;; bindings of a Clozeur vs into the expression? Do we need special
;; types or something for that?
;; defining this NOT as a higher-order zipper per se, because those are headaches
(defn ctx-children [^CtxNode node]
  (let [ctx (.ctx node)
        expr (.expr node)
        children-ctx (if (clozeur? expr)
                       (merge ctx (bindings expr))
                       ctx)]
    (for [cexpr (expr-children expr)]  ;; or whatever. children fn of an expr-that-might-be-a-clozeur. 
      (CtxNode. children-ctx cexpr))))

;; (def ctx-make-node-log
;;   (atom []))

(defn ctx-make-node [^CtxNode node, kids]
  (let [ctx (.ctx node)
        expr (.expr node)
        res (CtxNode.
              ctx
              (expr-make-node expr
                (for [^CtxNode node2 kids]
                  (.expr node2))))]
    ;; (swap! ctx-make-node-log conj
    ;;   (assoc (mu/lit-map node, kids, res)
    ;;     :stack (stackseq-methods)))
    res))

;; check order of the following
(defn- ctx-zip [ctx-node]
  (assert (instance? CtxNode ctx-node))
  (zip/zipper
    ctx-branch?
    ctx-children
    ctx-make-node
    ctx-node))

(declare clozeur?) ;; should probably be a multimethod or something. blah.

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

(def minimize-log
  (atom []))
  
(defn minimize
  "Let res be clz with all its bound variables removed. If res has no
  free variables, minimize-clozeur returns (expression clz), otherwise
  returns res. Does not do replacement, so if clz has variables bound
  but not yet replaced in (expression clz) they will effectively
  become open symbols; to avoid this, use collapse instead."
  [clz]
  (swap! minimize-log conj clz)
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

(def cw-log (atom []))

;; sketchy algorithm
(defn- collapse-walk [clz]
  (assert (clozeur? clz) "requires clozeur") ;; this is stupid
  (let [bndgs (bindings clz)]
    (loop [loc (ctx-zip (CtxNode. {} (expression clz)))] ;tricksy
      (if-let [loc2 (znext loc)]
        (let [^CtxNode node (zip/node loc2)
              ctx (.ctx node)
              expr (.expr node)
              bndgs2 (reduce dissoc bndgs (keys ctx))]
          (recur
            (if-let [[_ expr2] (find bndgs2 expr)]
              (let [loc3 (zip/replace loc2 (assoc node :expr expr2))]
                (swap! cw-log conj
                  (mu/lit-map node bndgs bndgs2 node ctx expr expr2 loc3))
                loc3)
              (do
                (swap! cw-log conj
                  (mu/lit-map node bndgs bndgs2 node ctx expr))
                loc2))))
        (let [^CtxNode r (zip/root loc)]
          (swap! cw-log conj
            {:bndgs bndgs :ctx-node r})
          (minimize
            (put-expression clz (.expr r))))))))

;; there's collapse, and then there's total-collapse. total-collapse
;; attempts to eliminate all clozeurs at every depth. collapse
;; attempts to eliminate only the top clozeur (I guess). Neither
;; throws an error if the entire clozeur or clozeurs cannot be
;; eliminated because they don't have all their free variables bound,
;; but you could write something else that validates for that. Except
;; then total-collapse is really a partial-collapse. Hm. Maybe it
;; should be collapse vs collapse-all.



;; ============================================================
;; tests

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
                   (+ 13 x))))))))))
