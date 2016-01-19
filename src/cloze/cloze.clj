(ns cloze.cloze
  (:refer-clojure :exclude [bound?])
  (:require [clojure.zip :as zip]
            [clojure.test :as t]
            [cloze.zip-utils :as zu]
            [cloze.traversal :as trv]))

(declare collapse-walk-1)

(defn- ensure-set [x]
  (if (set? x) x (set x)))

(defn- fixpoint [f x]
  (loop [x x]
    (let [y (f x)]
      (if (= y x)
        y
        (recur y)))))

(defn- fixpoint-vec [f x]
  (persistent!
    (loop [bldg (transient [x])
           x x]
      (let [y (f x)]
        (if (= y x)
          bldg
          (recur (conj! bldg y) y))))))

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
     (or bindings {})
     expression)))

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

;; is this actually important?
;; (defn merge-vs [clz1 clz2])
;; (defn merge-bindings [clz1 clz2])
;; (defn merge-clz [clz1 clz2])

;; maybe redefine this for exprs generally
(defn binding-paths [x]
  (when (cloze? x)
    (let [bndgs (bindings x)]
      (mapcat (fn [k]
                (map #(cons k %)
                  (or (binding-paths (bndgs k)) '(()))))
        (keys bndgs)))))

(defn cloze-paths [x]
  (when (or (map? x) (cloze? x))
    (mapcat (fn [k]
              (or
                (seq
                  (map #(cons k %)
                    (cloze-paths (get x k))))
                (list (list k))))
      (keys x))))

;; ============================================================
;; sugar

;; unlike let, bindings can't see previous bindings! because it turns into a map.
;; we can change this by iterating clozes, but it would be a headache to manipulate that data.
;; hm. maybe we should think about that more.
;; well we do have update-expr-in... still kind of annoying. Hm hm hm.
;; might be a use-case for collapse-walk-deep? or some variant
;; then could make form of collapse polymorphic on some cloze type or something


;; quoting vs not quoting thing here is annoying, this macro needs work
(defmacro cloze-let [bndgs frm]
  (let [qbndgs (apply hash-map
                 (interleave
                   (map #(list 'quote %)
                     (take-nth 2 bndgs))
                   (take-nth 2 (rest bndgs))))]
    `(cloze nil ~qbndgs ~frm))) ;; frm not quoted so we can nest clozes better

;; ============================================================
;; expr-zip

;; TODO: polymorphic version
(declare splice? coll-splice)
;; I mean this is just stupid ^

(defn expr-branch? [x]
  (or (coll? x) (cloze? x)))

(defn expr-children [x]
  (cond
    (cloze? x) (list (vs x) (bindings x) (expr x))
    (splice? x) (:args x)
    (coll? x) (seq x) ;; should be seqable or something
    :else (throw (Exception. "requires either standard clojure collection or cloze"))))

(defn list-like? [x]
  (or (seq? x) (instance? clojure.lang.MapEntry x)))

(defn expr-make-node [x kids]
  (-> (cond
        (list-like? x) (into (empty x) (reverse kids))
        (cloze? x) (let [[vs bndgs expr] kids]
                     (Cloze. vs bndgs expr))
        (splice? x) (coll-splice kids) ;; yep need multimethod or something
        ;; WISH you didn't have to do this shit with maps, is total bullshit:
        (map? x) (into (empty x) (map vec kids))
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

(defn ctx-branch-fn [expr-branch?]
  (fn [^CtxNode node]
    (expr-branch? (.expr node))))

(defn ctx-children-fn [expr-children]
  (fn [^CtxNode node]
    (let [ctx (.ctx node)
          expr (.expr node)
          children-ctx (if (cloze? expr)
                         (into ctx (scope expr)) ;; entire scope, not just bindings
                         ctx)]
      (seq
        (for [cexpr (expr-children expr)]
          (CtxNode. children-ctx cexpr))))))

(defn ctx-make-node-fn [expr-make-node]
  (fn [^CtxNode node kids]
    (CtxNode.
      (.ctx node)
      (expr-make-node (.expr node)
        (for [^CtxNode node2 kids]
          (.expr node2))))))

;; (defn ctx-branch? [^CtxNode node]
;;   (expr-branch? (.expr node)))

;; ;; defining this NOT as a higher-order zipper per se, because those are headaches
;; (defn ctx-children [^CtxNode node]
;;   (assert (instance? CtxNode node))
;;   (let [ctx (.ctx node)
;;         expr (.expr node)
;;         children-ctx (if (cloze? expr)
;;                        (into ctx (scope expr)) ;; entire scope, not just bindings
;;                        ctx)]
;;     (seq
;;       (for [cexpr (expr-children expr)]
;;         (CtxNode. children-ctx cexpr)))))

;; (defn ctx-make-node [^CtxNode node, kids]
;;   (assert (instance? CtxNode node))
;;   (CtxNode.
;;     (.ctx node)
;;     (expr-make-node (.expr node)
;;       (for [^CtxNode node2 kids]
;;         (.expr node2)))))

;; check order of the following
(defn- ctx-zip
  ([^CtxNode ctx-node]
   (ctx-zip expr-branch? expr-children expr-make-node ctx-node))
  ([expr-branch? expr-children expr-make-node ^CtxNode ctx-node]
   (assert (instance? CtxNode ctx-node))
   (zip/zipper
     (ctx-branch-fn expr-branch?)
     (ctx-children-fn expr-children)
     (ctx-make-node-fn expr-make-node)
     ctx-node)))

;; ============================================================
;; replacement

(defn collapse [expr]
  (collapse-walk-1 expr))

 ;; sloppy for now
(defn collapse-all [expr] ;; need not be cloze
  (collapse-walk-repeated expr))

;; this could get more elaborate
(defn cloze? [x]
  (instance? Cloze x))

(defn free [clz]
  (reduce dissoc
    (vs clz)
    (keys (bindings clz))))

(defn absorb [clz]
  (loop [loc (expr-zip (expr clz)), clzs []]
    (if (zip/end? loc)
      (let [expr (zip/root loc)]
        (-> clz
          (put-expr expr)
          (put-vs (reduce into (vs clz) (map vs clzs)))
          (put-bindings (into (bindings clz) (map bindings clzs)))))
      (let [nd (zip/node loc)]
        (if (cloze? nd)
          (recur
            (zupple (zip/replace loc (expr nd)))
            (conj clzs nd))
          (recur (zip/next loc) clzs))))))

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

;; should be imperatively setting this during rewrite stages below; am not.
;; not currently used!
(def ^:dynamic *bail* 1000)

(defmacro bail-up [i & body]
  `(clojure.core/binding [*bail* (when *bail* (+ *bail* ~i))]
     ~@body))

;; given behavior of zip/end? etc (as noted near walk-loc), not sure
;; at all that znext is right way to do this

;; ============================================================
;; core transformation functions

(defmacro ^:private traversaler [& args]
  (let [[expr-branch? expr-children expr-make-nod] (take-last 3 args)]
    `(~@(take (- (count args) 3) args)
      (ctx-branch-fn ~expr-branch?)
      (ctx-children-fn  ~expr-children)
      (ctx-make-node-fn ~expr-make-node))))

;; just one level
(defn collapse-cloze
  ([clz]
   (collapse-cloze clz #{}))
  ([clz ctx]
   (collapse-cloze clz #{}
     expr-branch? expr-children expr-make-node))
  ([clz ctx0
    expr-branch? expr-children expr-make-node]
   (assert (cloze? clz) "requires cloze") ;; fix this, perhaps at collapse (above)
   (let [bndgs (bindings clz)]
     (traversaler
       trv/prewalk-shallow
       (CtxNode. ctx0 (expr clz))
       (fn match? [^CtxNode node]
         (and
           (not (shadowed? node (.expr node)))
           (find bndgs (.expr node))))
       (fn replace [^CtxNode node]
         (get bndgs (.expr node)))
       expr-branch?
       expr-children
       expr-make-node))))

;; will NOT burrow into replacements
(defn collapse-walk-1
  ([expr]
   (collapse-walk-1 expr
     expr-branch? expr-children expr-make-node))
  ([expr expr-branch? expr-children expr-make-node]
   (traversaler
     trv/prewalk-shallow
     expr
     cloze?
     collapse-cloze
     expr-branch?
     expr-children
     expr-make-node)))

 ;; WILL burrow into replacements; rather dangerous
(defn collapse-walk-deep
  ([expr]
   (collapse-walk-deep expr-branch? expr-children expr-make-node))
  ([expr expr-branch? expr-children expr-make-node]
   (traversaler
     trv/prewalk
     expr
     (fn step [x]
       (if (cloze? x)
         (collapse-cloze x)
         x))
     expr-branch?
     expr-children
     expr-make-node)))

;; like mathematica's replace-all-repeated. goes to fixpoint. not
;; cheap, and might not terminate, but the best.
(defn collapse-walk-repeated
  ([expr]
   (collapse-walk-repeated expr
     expr-branch? expr-children expr-make-node))
  ([expr
    expr-branch? expr-children expr-make-node]
   (fixpoint
     (fn [x]
       (collapse-walk-1 x
         expr-branch? expr-children expr-make-node))
     expr)))

;; guess there should also be a collapse-walk-deep-repeated?

;; ============================================================
;; finesse
;; not necessary for Cloze templates; more related to expression zipper

;; step fn gets fed locs
;; seems that there's something important about the last loc (for
;; which zip/end? is true), such that some algorithms (such as
;; expand-splices) don't work if you just take up UNTIL you hit the
;; last loc, ie with (take-while (complement zip/end?)), which I had
;; been using. Might explain some of the trouble I've been having.
(defn walk-loc [loc step-fn]
  (loop [loc loc]
    (let [loc2 (step-fn loc)]
      (if loc2
        (if (zip/end? loc2)
          (zip/root loc2)
          (recur loc2))
        (zip/root loc)))))

;; step-fn gets fed nodes rather than locs; like clojure.walk/prewalk,
;; but preserves metadata
(defn walk-expression [expr step-fn]
  (walk-loc (expr-zip expr)
    (fn [loc]
      (zip/next
        (zip/edit loc step-fn)))))

;; names are so fun
(defn- zupple [loc]
  (or (zu/zip-up-to-right loc)
    [(zip/root loc) :end]))

;; like mathematica, except worse
(defn replace-all [expr & pred-fns]
  (let [pfs (vec (partition 2 pred-fns))]
    (walk-loc (expr-zip expr)
      (fn [loc]
        (let [node (zip/node loc)]
          (loop [i 0]
            (if (< i (count pfs))
              (let [[p f] (pfs i)]
                (if (p node)
                  (zupple
                    (zip/edit loc f))
                  (recur (inc i))))
              (zip/next loc))))))))

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
      (take-while identity))))

;; or something
(defrecord Splice [args])

(defn splice [& xs]
  (Splice. (vec xs)))

(defn coll-splice [xs]
  (Splice. (vec xs)))

(defn splice? [x]
  (instance? Splice x))

(defn expand-splices [expr]
  (if (splice? expr)
    (:args expr)
    (walk-loc (expr-zip expr)
      (fn step [loc]
        (zip/next
          (if (splice? (zip/node loc))
            (->> (:args (zip/node loc))
              expand-splices
              (reduce zip/insert-left loc)
              zip/remove)
            loc))))))

;; can't even splice into a map with backtick:
;; (let [kvs [1 2 3 4]]
;;   `{~@kvs})

;; so instead for that sort of thing perhaps use:
;; (let [kvs [1 2 3 4]]
;;   `(hash-map ~@kvs))

;; if a map literal is needed for syntax, though, we could
;; write a spliceable-map term:

;; (expand-splices
;;   (spliceable-map :a :b (splice :c :d)))
;; =>
;; {:a :b :c :d}


;; ============================================================
;; miracle of merge

(defn deep-merge
  ([] nil)
  ([a] a)
  ([a b]
   (cond
     (nil? b) a ;; contentious
     
     (cloze? a)
     (if (cloze? b)
       (cloze
         (deep-merge (vs a) (vs b))
         (deep-merge (bindings a) (bindings b))
         (deep-merge (expr a) (expr b)))
       b)

     (map? a)
     (if (map? b)
       (reduce-kv (fn [m k v]
                    (assoc m k
                      (if-let [e (find m k)]
                        (deep-merge v (val e))
                        v)))
         a b)
       b)

     (set? a)
     (if (set? b)
       (into a b)
       b)

     :else b))
  ([a b & cs]
   (reduce deep-merge (deep-merge a b) cs)))


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

;; finesse
(t/deftest test-splices
  (t/is
    (= (expand-splices
         ['a (splice 1 2 3) 'b])
      ['a 1 2 3 'b])))


;; ============================================================
;; fun

;; splice should maybe take a coll rather than n-args; at least,
;; something should, because otherwise annoying to rewrite into a
;; splice. maybe.

(comment
  (let [template (cloze '#{spec iss} nil
                   ;; {'spec (gensym "spec_")
                   ;;  'iss (gensym "initialized-spec-sym_")}
                   (cloze nil
                     {'initialized-spec 'iss
                      'let-bindings-1 (cloze nil
                                        {'iss-val '(oodlewoodle spec)}
                                        ['iss 'iss-val])
                      'reductioneer '(fn [subspec]
                                       (case subspec
                                         :hi 0 
                                         :there 1 
                                         :marty 2
                                         (throw Exception. "not really marty")))}
                     '(fn [spec]
                        (let let-bindings-1
                          (reduce reductioneer
                            initialized-spec
                            spec-subspecs)))))]
    (pprint
      (expand-splices
        (collapse-walk-deep
          (-> template
            (assoc-in '[:bindings spec] 'hispec)
            (assoc-in '[:expr :bindings let-bindings-1 :bindings iss-val]
              ["maaarty" 'spec
               (coll-splice
                 (interleave
                   '[a b c]
                   (range)))])))))))

;; oooooo can have a function that walks the whole thing looking for
;; shadowed, unbound variables at the end and replacing them with
;; consistent gensyms so we do the gensym dance AT THE END
;; !!!AAAAAAAAA!!!
;; and ya should probably have a key-rename function for clozes too



