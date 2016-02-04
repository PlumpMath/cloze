(ns cloze.traversal
  (:require [clojure.zip]))

;; ============================================================
;; traverser

(defprotocol ITraverser
  (branch? [this x])
  (children [this x])
  (make-node [this x kids]))

(defn traverser [branch? children make-node]
  (reify ITraverser
    (branch? [_ x] (branch? x))
    (children [_ x] (children x))
    (make-node [_ x kids] (make-node x kids))))

;; ============================================================
;; zipper

(defn traverser-zip [x trav]
  (clojure.zip/zipper
    #(branch? trav %)
    #(children trav %)
    #(make-node trav %1 %2)
    x))

;; ============================================================
;; basic traversals

(defn prewalk
  ([x f branch? children make-node]
   (prewalk x f
     (traverser branch? children make-node)))
  ([x f trav]
   (let [y (f x)]
     (if (not (branch? trav y))
       y
       (make-node trav y
         (map #(prewalk % f trav)
           (children trav y)))))))

(defn prewalk-shallow
  ([x p f branch? children make-node]
   (prewalk-shallow x p f
     (traverser branch? children make-node)))
  ([x p f trav]
   (cond
     (p x) (f x)
     (not (branch? trav x)) x
     :else (make-node trav x
             (map #(prewalk-shallow % p f trav)
               (children trav x))))))

(defn postwalk
  ([x f branch? children make-node]
   (postwalk x f
     (traverser branch? children make-node)))
  ([x f trav]
   (f
     (if (not (branch? trav x))
       x
       (make-node trav x
         (map #(postwalk % f trav)
           (children trav x)))))))

;; ============================================================
;; transducers tho


(comment
  ;; can we write a version of traverse-vector that sees if
  ;; anything's changed first and then does the construction?
  ;; should be possible to write a traversal that allocates only for
  ;; the tranducer fn if nothing changes
  ;; (ignoring the seq stuff for vectors etc)
  ;; actually not sure if this is true; doesn't cover structural transducers
  ;; etc etc, assumes we're dealing with a map op, bla bla. Which
  ;; kind of deflates the transducer interface and just isn't true
  ;; even for all the things we want to do in this library, some of
  ;; which add or remove elements.
  ;; then one might ask how much is gained by the somewhat ugly
  ;; volatile memoization thing in prewalk etc since we're going to be
  ;; constructing new nodes in memory for every step in the traversal
  ;; anyway; and I guess the answer is exactly we save exactly as many
  ;; allocations as there are branch nodes in the tree. which might be
  ;; worth it, shave a little off. Should benchmark though.
  ;; also might just not be worth the hit to legibility at this point
  ;; yeah fuck it for now use non-memoized version, people love to
  ;; casually judge the prettiness of code without thinking about what
  ;; it's doing
  (defn traverse-vector [xfrm v]
    (with-meta (into [] xfrm v) (meta v)))

  (defn prewalk [x f trav]
    (let [step-mem (volatile! nil) ;; reference for memoizing (map step)
          step (fn [x]
                 (let [y (f x)]
                   (if (branch? trav y)
                     (traverse trav @step-mem y)
                     y)))]
      (vreset! step-mem (map step))
      (step x)))

  (defn prewalk-shallow [x p f trav]
    (let [step-mem (volatile! nil) ;; reference for memoizing (map step)
          step (fn [x]
                 (cond
                   (p x) (f x)
                   (branch? trav x) (traverse trav @step-mem x)
                   :else x))]
      (vreset! step-mem (map step))
      (step x)))

  (defn postwalk [x f trav]
    (let [step-mem (volatile! nil) ;; reference for memoizing (map step)
          step (fn [x]
                 (f
                   (if (branch? trav x)
                     (traverse trav @step-mem x)
                     x)))]
      (vreset! step-mem (map step))
      (step x)))
  
  ;; ============================================================
  ;; "prettier" non-memoized version, you fucks

  (defn prewalk [x f trav]
    (letfn [(step [x]
              (let [y (f x)]
                (if (branch? trav y)
                  (traverse trav (map step) y)
                  y)))]
      (step x)))

  (defn prewalk-shallow [x p f trav]
    (letfn [(step [x]
               (cond
                 (p x) (f x)
                 (branch? trav x) (traverse trav (map step) x)
                 :else x))]
      (step x)))

  (defn postwalk [x f trav]
    (letfn [(step [x]
              (f
                (if (branch? trav x)
                  (traverse trav (map step) x)
                  x)))]
      (step x)))
  
  )
