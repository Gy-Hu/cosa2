(define-fun |predicate.0| ((x (_ BitVec 6)) (y (_ BitVec 6))) Bool
  (bvult x y))
(define-fun |predicate.1| ((x (_ BitVec 6)) (y (_ BitVec 6))) Bool
  (= x (_ bv61 6)))
(define-fun |predicate.2| ((x (_ BitVec 6)) (y (_ BitVec 6))) Bool
  (= x (_ bv61 6)))
(define-fun |predicate.3| ((x (_ BitVec 6)) (y (_ BitVec 6))) (_ BitVec 6)
  (ite (= x (_ bv61 6)) x (bvadd x (_ bv1 6))))
(define-fun |predicate.4| ((x (_ BitVec 6)) (y (_ BitVec 6))) (_ BitVec 6)
  (ite (= x (_ bv61 6)) y (bvadd y (_ bv1 6))))
(define-fun |predicate.5| ((x (_ BitVec 6)) (y (_ BitVec 6))) Bool
  (and (bvuge y x) (bvuge x y)))