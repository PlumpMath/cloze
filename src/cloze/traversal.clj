(ns cloze.traversal)

;; ============================================================
;; basic traversals

(defn prewalk [x f leaf? children make-node]
  (let [y (f x)]
    (if (leaf? y)
      y
      (make-node y
        (map #(prewalk % f leaf? children make-node)
          (children y))))))

(defn prewalk-shallow [x p f leaf? children make-node]
  (cond
    (p x) (f x)
    (leaf? x) x
    :else (make-node x
            (map #(prewalk-shallow % p f leaf? children make-node)
              (children x)))))

(defn postwalk [x f leaf? children make-node]
  (f
    (if (leaf? x)
      x
      (make-node x
        (map #(postwalk % f leaf? children make-node)
          (children x))))))

;; ============================================================
;; closures

(defn prewalk-fn [leaf? children make-node]
  (fn [x f]
    (prewalk x f leaf? children make-node)))

(defn prewalk-shallow-fn [leaf? children make-node]
  (fn [x p f]
    (prewalk-shallow x p f leaf? children make-node)))

(defn postwalk-fn [leaf? children make-node]
  (fn [x f]
    (postwalk x f leaf? children make-node)))
