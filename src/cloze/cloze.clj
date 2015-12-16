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
   (Clozeur. variables bindings expression)))

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



(def ^:dynamic *bail* 1000)

(def cclz-log (atom []))

;; just one level
(defn- collapse-cloze
  ([clz]
   (collapse-cloze clz {}))
  ([clz ctx0]
   (assert (clozeur? clz) "requires clozeur") ;; fix this, perhaps at collapse (above)
   (let [bndgs (bindings clz)]
      ;; seems like there should be a better way than looping over 2
      ;; locs, but that would require thinking
     (loop [prev-loc (ctx-zip ;; tricksy
                       (CtxNode. ctx0 ;; riiight?
                         (expression clz)))
            loc (znext prev-loc)
            i 0]
       (swap! cclz-log conj loc)
       (if (<= *bail* i)
         (throw (Exception. (str  "reached max iterations, *bail* = " *bail*)))
         (if loc
           (let [^CtxNode node (zip/node loc)
                 ctx (.ctx node)
                 expr (.expr node)
                 bndgs2 (reduce dissoc bndgs (keys ctx))]
             (recur
               loc
               (if-let [[_ expr2] (find bndgs2 expr)]
                 (zu/zip-up-to-right ;; move OVER replacements
                   (zip/replace loc (assoc node :expr expr2)))
                 (znext loc))
               (inc i)))
           (let [^CtxNode r (zip/root prev-loc)
                 res (minimize
                       (put-expression clz (.expr r)))]
             (swap! cw-log conj [:RESULT res])
             res)))))))

(def cw-log (atom []))

;; NOT A GOOD POLICY. Variable capture.
(defn- collapse-walk [clz]
  (assert (clozeur? clz) "requires clozeur") ;; fix this, perhaps at collapse (above)
  (let [bndgs (bindings clz)]
    (loop [loc (ctx-zip (CtxNode. {} (expression clz)))  ;tricksy
           i 0]
      (swap! cw-log conj loc)
      (if (<= *bail* i)
        (throw (Exception. (str  "reached max iterations, *bail* = " *bail*)))
        (if-let [loc2 (znext loc)]
          (do (when (= loc2 loc)
                (swap! cw-log conj [:FAIL!! loc])
                (throw (Exception. "(= loc (znext loc)), somehow. It shouldn't.")))
              (let [^CtxNode node (zip/node loc2)
                    ctx (.ctx node)
                    expr (.expr node)
                    bndgs2 (reduce dissoc bndgs (keys ctx))]
                (recur
                  (if-let [[_ expr2] (find bndgs2 expr)]
                    (zip/replace loc2 (assoc node :expr expr2))
                    loc2)
                  (inc i))))
          (let [^CtxNode r (zip/root loc)
                res (minimize
                      (put-expression clz (.expr r)))]
            (swap! cw-log conj [:RESULT res])
            res))))))

;; ============================================================
;; preliminary tests

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
