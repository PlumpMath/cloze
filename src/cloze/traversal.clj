(ns cloze.traversal)

;; ============================================================
;; basic traversals

(defn prewalk [x f branch? children make-node]
  (let [y (f x)]
    (if (not (branch? y))
      y
      (make-node y
        (map #(prewalk % f branch? children make-node)
          (children y))))))

(defn prewalk-shallow [x p f branch? children make-node]
  (cond
    (p x) (f x)
    (not (branch? x)) x
    :else (make-node x
            (map #(prewalk-shallow % p f branch? children make-node)
              (children x)))))

(defn postwalk [x f branch? children make-node]
  (f
    (if (not (branch? x))
      x
      (make-node x
        (map #(postwalk % f branch? children make-node)
          (children x))))))

;; ============================================================
;; closures

(defn prewalk-fn [branch? children make-node]
  (fn [x f]
    (prewalk x f branch? children make-node)))

(defn prewalk-shallow-fn [branch? children make-node]
  (fn [x p f]
    (prewalk-shallow x p f branch? children make-node)))

(defn postwalk-fn [branch? children make-node]
  (fn [x f]
    (postwalk x f branch? children make-node)))
