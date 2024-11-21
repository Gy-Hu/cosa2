(define-fun |predicate.0| ((x (_ BitVec 6)) (y (_ BitVec 6))) Bool
  (bvule x (_ bv61 6)))

(define-fun |predicate.1| ((x (_ BitVec 6)) (y (_ BitVec 6))) Bool
  (bvule y (_ bv63 6)))

(define-fun |predicate.2| ((x (_ BitVec 6)) (y (_ BitVec 6))) Bool
  (= y (bvadd x (_ bv2 6))))