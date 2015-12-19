(ns cloze.cloze
  (:refer-clojure :exclude [bound?])
  (:require [clojure.zip :as zip]
            [clojure.test :as t]
            [cloze.zip-utils :as zu]))

(declare collapse-walk-1)

(defn- ensure-set [x]
  (if (set? x) x (set x)))

(defn- fixpoint [f x]
  (loop [x x]
    (let [y (f x)]
      (if (= y x)
        y
        (recur y)))))

;; ============================================================
;; cloze

;; no attempt to define polymorphic interface for now, but room to in
;; the future if that seems like a coolthing

(declare collapse-walk expr-zip cloze?)

(defrecord Cloze [vs bindings expr])

(defn cloze
  ([variables expression]
   (cloze variables {} expression))
  ([variables bindings expression]
   (Cloze. (ensure-set variables)
     bindings expression)))

(defn cloze? [x]
  (instance? Cloze x))

;; ============================================================
;; cloze data API

(defn vs [clz]
  (.vs clz))

(defn bindings [clz]
  (.bindings clz))

(defn expr [clz]
  (.expr clz))

(defn get-binding [clz k]
  (get (bindings clz) k))

;; implementatino of get-in does some other stuff too
(defn get-binding-in [clz ks]
  (reduce get-binding ks))

(defn find-binding [clz k]
  (find (bindings clz) k))

(defn scope [clz]
  (into (vs clz) (keys (bindings clz))))

(defn scopes? [clz k]
  (contains? (scope clz) k))

;; point of put-* things (rather than (assoc clz :vs vs), for
;; example) is to leave open possibility of not representing Clozes as
;; records, down the line. 
(defn put-vs [clz vs]
  (assert (set? vs))
  (assoc clz :vs vs))

(defn put-bindings [clz bndgs]
  (assert (map? bndgs))
  (assoc clz :bindings bndgs))

(defn put-expr [clz expr]
  (assoc clz :expr expr))

;; (defn put-vs-in [clz path vs])
;; (defn put-bindings-in [clz path bndgs])
;; (defn put-expr-in [clz path expr])

(defn enscope
  ([clz x]
   (if (scopes? clz x)
     clz
     (put-vs clz (conj (vs clz) x))))
  ([clz x & xs]
   (reduce enscope (cons x xs))))

(defn unscope
  ([clz x]
   (as-> clz clz
     (if (contains? (vs clz) x)
       (put-vs clz (disj (vs clz) x))
       clz)
     (if (contains? (bindings clz) x)
       (put-vs clz (dissoc (bindings clz) x))
       clz)))
  ([clz x & xs]
   (reduce unscope (cons x xs))))

(defn bind
  ([clz k v]
   (put-bindings clz
     (assoc (bindings clz) k v)))
  ([clz k v & kvs]
   (put-bindings clz
     (apply assoc (bindings clz) k v kvs))))

(defn unbind
  ([clz k]
   (put-bindings clz
     (dissoc (bindings clz) k)))
  ([clz k & ks]
   (put-bindings clz
     (apply dissoc (bindings clz) k ks))))

(defn bind-in [clz [k & ks] v]
  (if ks
    (bind clz k (bind-in (get-binding clz k) ks v))
    (bind clz k v)))

(defn unbind-in [clz [k & ks]]
  (if ks
    (bind clz k (unbind-in (get-binding clz k) ks))
    (unbind clz k)))

(defn update-vs
  ([clz f]
   (put-vs clz (f (vs clz))))
  ([clz f & args]
   (put-vs clz (apply f (vs clz) args))))

(defn update-bindings
  ([clz f]
   (put-bindings clz (f (bindings clz))))
  ([clz f & args]
   (put-vs clz (apply f (vs clz) args))))

(defn update-expr
  ([clz f]
   (put-expr clz (f (expr clz))))
  ([clz f & args]
   (put-vs clz (apply f (vs clz) args))))

(defn update-clz-in
  ([clz [k & ks] f]
   (if ks
     (let [clz2 (get-binding clz k)]
       (if (cloze? clz2)
         (bind clz k (update-clz-in ks f))
         (throw (Exception.
                  (str "element in path not Cloze, type of element: "
                    (type clz2))))))
     (f (get-binding clz k))))
  ([clz ks f & args]
   (update-clz-in clz ks #(apply f % args) ks)))

(defn update-vs-in
  ([clz ks f]
   (update-clz-in clz ks #(update-vs % f)))
  ([clz ks f & args]
   (update-vs-in clz ks #(apply f % args) ks)))

(defn update-bindings-in
  ([clz ks f]
   (update-clz-in clz ks #(update-bindings % f)))
  ([clz ks f & args]
   (update-bindings-in clz ks #(apply f % args) ks)))

(defn update-expr-in
  ([clz ks f]
   (update-clz-in clz ks #(update-expr % f)))
  ([clz ks f & args]
   (update-expr-in clz ks #(apply f % args) ks)))

(defn update-expr-in [clz [k & ks] expr])

;; is this actually important?
;; (defn merge-vs [clz1 clz2])
;; (defn merge-bindings [clz1 clz2])
;; (defn merge-clz [clz1 clz2])


;; ============================================================
;; expr-zip

;; TODO: polymorphic version

(defn- expr-branch? [x]
  (or (coll? x) (cloze? x)))

(defn- expr-children [x]
  (cond
    (cloze? x) (list (vs x) (bindings x) (expr x))
    (coll? x) (seq x) ;; should be seqable or something
    :else (throw (Exception. "requires either standard clojure collection or cloze"))))

(defn- list-like? [x]
  (or (seq? x) (instance? clojure.lang.MapEntry x)))

(defn- expr-make-node [x kids]
  (-> (cond
        (list-like? x) (into (empty x) (reverse kids))
        (cloze? x) (let [[vs bndgs expr] kids]
                     (Cloze. vs bndgs expr))
        (coll? x) (into (empty x) kids)
        :else (throw (Exception. "requires either standard clojure collection or cloze")))
    (with-meta (meta x))))

(defn expr-zip [x]
  (zip/zipper
    expr-branch?
    expr-children
    expr-make-node
    x))

;; ============================================================
;; ctx-zip

;; should be in zip-utils
(defn- znext [loc]
  (let [nxt (zip/next loc)]
    (when-not (zip/end? nxt)
      nxt)))

;; looks a lot like a cloze
;; hmmmmmmmmmm
;; (defrecord CtxNode [vs bindings expr]) ;; <= might be a good idea, not doing it just yet

;; this variant of CtxNode really just tracks scope (vs + bindings)
;;; "vs" should be "shadow", "vs" doesn't mean anything

(defrecord CtxNode [ctx, expr])

(defn shadowed? [^CtxNode ctx-node, x]
  (contains? (.ctx ctx-node) x))

(defn ctx-branch? [^CtxNode node]
  (expr-branch? (.expr node)))

;; defining this NOT as a higher-order zipper per se, because those are headaches
(defn ctx-children [^CtxNode node]
  (assert (instance? CtxNode node))
  (let [ctx (.ctx node)
        expr (.expr node)
        children-ctx (if (cloze? expr)
                       (into ctx (scope expr)) ;; entire scope, not just bindings
                       ctx)]
    (seq
      (for [cexpr (expr-children expr)]
        (CtxNode. children-ctx cexpr)))))

(defn ctx-make-node [^CtxNode node, kids]
  (assert (instance? CtxNode node))
  (CtxNode.
    (.ctx node)
    (expr-make-node (.expr node)
      (for [^CtxNode node2 kids]
        (.expr node2)))))

;; check order of the following
(defn- ctx-zip [^CtxNode ctx-node]
  (assert (instance? CtxNode ctx-node))
  (zip/zipper
    ctx-branch?
    ctx-children
    ctx-make-node
    ctx-node))

;; ============================================================
;; replacement

(defn collapse [expr]
  (collapse-walk-1 expr))

 ;; sloppy for now
(defn collapse-all [expr] ;; need not be cloze
  (zip/root
    (zu/zip-prewalk (expr-zip expr)
      #(if (cloze? %) (collapse %) %))))

;; this could get more elaborate
(defn cloze? [x]
  (instance? Cloze x))

(defn free [clz]
  (reduce dissoc
    (vs clz)
    (keys (bindings clz))))

;; following runs right into variable capturing awkwardness. Can deal
;; with it in the obvious ways - rewrite subclozes with gensyms, or
;; just capture the variables because that's what you're doing
(defn absorb [clz]
  (loop [loc (expr-zip (expr clz)), clzs '()]
    (if-let [nxt (znext loc)]
      (let [nd (zip/node nxt)]
        (if (cloze? nd)
          (recur
            (zu/zip-up-to-right (zip/replace nxt (expr clz)))
            (conj clzs nxt))
          (recur nxt clzs)))
      (let [expr (zip/root loc)]
        (-> clz
          (put-expr expr)
          (put-vs (into (vs clz) (map vs clzs)))
          (put-bindings (into (bindings clz) (map bindings clzs))))))))

(defn minimize
  "Let res be clz with all its bound variables removed. If res has no
  free variables, minimize-cloze returns (expr clz), otherwise
  returns res. Does not do replacement, so if clz has variables bound
  but not yet replaced in (expr clz) they will effectively
  become open symbols; to avoid this, use collapse instead."
  [clz]
  (assert (cloze? clz) "requires cloze")
  (let [vs2 (reduce disj
              (vs clz)
              (keys (bindings clz)))]
    (if (empty? vs2)
      (expr clz)
      (-> clz
        (put-bindings {})
        (put-vs vs2)))))

;; punt on specifics of polymorphism for now; can always back out of
;; the following. (could wrap it up in another level of indirection if
;; you're really being paranoid but probably no reason. Especially
;; since this stuff is going to be in an internal namespace for a
;; moment, and anyway you can always hoist the function signature if
;; you really want that sort of crap).

;; public or private? hm
;; just collapses the current clz. for collapse-all, use this
;; recursively or whatever I guess. Might be getting a little anal
;; with the types, could make this accept both clozes and CtxNodes


;; should be imperatively setting this during rewrite stages below; am not.
(def ^:dynamic *bail* 1000)

(defmacro bail-up [i & body]
  `(clojure.core/binding [*bail* (when *bail* (+ *bail* ~i))]
     ~@body))

;; just one level
(defn collapse-cloze
  ([clz]
   (collapse-cloze clz #{}))
  ([clz ctx0]
   (assert (cloze? clz) "requires cloze") ;; fix this, perhaps at collapse (above)
   (let [bndgs (bindings clz)]
     (loop [prev-loc (ctx-zip ;; tricksy
                       (CtxNode. ctx0 ;; riiight?
                         (expr clz)))
            loc (znext prev-loc)
            i 0]
       (if (and *bail* (<= *bail* i))
         (throw (Exception. (str  "reached max iterations, *bail* = " *bail*)))
         (if loc
           (let [^CtxNode node (zip/node loc)]
             (if-let [[_ expr2] (and
                                  (not (shadowed? node (.expr node)))
                                  (find bndgs (.expr node)))]
               (let [loc2 (zip/replace loc (assoc node :expr expr2))]
                 (recur loc2 (zu/zip-up-to-right loc2) (inc i)))
               (recur loc (znext loc) (inc i))))
           (let [^CtxNode r (zip/root prev-loc)]
             (minimize (put-expr clz (.expr r)))) ))))))

;; will NOT burrow into replacements
(defn collapse-walk-1 [expr]
  (loop [prev-loc nil
         loc (expr-zip expr)
         i 0]
    (if (and *bail* (<= *bail* i))
      (throw (Exception. (str  "reached max iterations, *bail* = " *bail*)))
      (if loc
        (let [expr (zip/node loc)]
          (if (cloze? expr)
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
                (if (cloze? expr)
                  (zip/replace loc
                    (bail-up i (collapse-cloze expr)))
                  loc))
              (inc i)))
          prev-loc)))))

;; like mathematica's replace-all-repeated. goes to fixpoint. not
;; cheap, and might not terminate, but the best.
(defn collapse-walk-repeated [expr]
  (fixpoint collapse-walk-1 expr))

;; guess there should also be a collapse-walk-deep-repeated?

;; ============================================================
;; finesse
;; not necessary for Cloze templates; more related to expression zipper

;; step fn gets fed locs
(defn walk-loc [loc step-fn]
  (->> loc
    (iterate step-fn)
    (take-while (complement zip/end?))
    last
    zip/root))

;; step-fn gets fed nodes rather than locs; like clojure.walk/prewalk,
;; but preserves metadata
(defn walk-expression [expr step-fn]
  (walk-loc (expr-zip expr)
    (fn [loc]
      (zip/next
        (zip/edit loc step-fn)))))

;; removes clozes. find better name?
(defn scrub [expr]
  (walk-expression expr
    (fn [x]
      (if (cloze? x)
        (.expr x)
        x))))

(defn loc-children [loc]
  (when-let [loc2 (zip/down loc)]
    (->> loc2
      (iterate zip/right)
      (remove nil?))))

;; or something
(defrecord Splice [args])

(defn splice [& xs]
  (Splice. xs))

(defn splice? [x]
  (instance? Splice x))

(defn expand-splices [expr]
  (walk-loc (expr-zip expr)
    (fn step [loc]
      (zip/next
        (if (splice? (zip/node loc))
          (->> (loc-children loc)
            (map #(walk-loc % step))
            (reduce zip/insert-left loc))
          loc)))))

;; ============================================================
;; preliminary tests

(t/deftest test-collapse
  (let [clz1 (cloze '#{a b x}
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

;; shadowing
(t/deftest test-shadowing
  (t/is
    (= (collapse-walk-1
         (cloze nil '{a A}
           (cloze '#{a} 'a)))
      (cloze '#{a} 'a)))
  (t/is
    (= (collapse-walk-1
         (cloze nil '{a A b B}
           (cloze '#{a} '[a b])))
      (cloze '#{a} '[a B])))
  (t/is
    (= (collapse-walk-deep
         (cloze nil '{a A b B}
           (cloze '#{a} '[a b])))
      (cloze '#{a} '[a B])))
  (t/is
    (= (collapse-walk-deep
         (cloze nil {'a 'A
                     'b '[a b]}
           (cloze #{'a} '[a b])))
      (cloze #{'a}
        '[a [a b]])))
  (t/is
    (= (collapse-walk-deep
         (cloze nil {'a 'A
                     'b '[a b]}
           (cloze #{} '[a b])))
      (cloze #{}
        '[A [a b]])))
  (t/is
    (= (collapse-walk-repeated
         (cloze nil '{a A b B}
           (cloze nil '{a AA} '[a b])))
      '[AA B])))
