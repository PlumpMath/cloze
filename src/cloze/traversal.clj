(ns cloze.traversal)

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
