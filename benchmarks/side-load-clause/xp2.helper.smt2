(define-fun |predicate.0| ((x (_ BitVec 6)) (y (_ BitVec 6))) Bool
  (bvule x (_ bv61 6)))

(define-fun |predicate.1| ((x (_ BitVec 6)) (y (_ BitVec 6))) Bool
  (bvule y (_ bv63 6)))

(define-fun |predicate.2| ((x (_ BitVec 6)) (y (_ BitVec 6))) Bool
  (= y (bvadd x (_ bv2 6))))

(define-fun |predicate.3| ((x (_ BitVec 6)) (y (_ BitVec 6))) Bool
  (bvult x y))

(define-fun |predicate.4| ((x (_ BitVec 6)) (y (_ BitVec 6))) Bool
  (bvuge x (_ bv0 6)))
  
(define-fun |predicate.5| ((x (_ BitVec 6)) (y (_ BitVec 6))) Bool
  (bvuge y (_ bv2 6)))

(define-fun |predicate.6| ((x (_ BitVec 6)) (y (_ BitVec 6))) Bool
  (= (bvsub y x) (_ bv2 6)))

(define-fun |predicate.7| ((x (_ BitVec 6)) (y (_ BitVec 6))) Bool
  (bvult y (bvadd x (_ bv3 6))))

(define-fun |predicate.8| ((x (_ BitVec 6)) (y (_ BitVec 6))) Bool
  (= (bvand x (_ bv1 6)) (bvand y (_ bv1 6))))

(define-fun |predicate.9| ((x (_ BitVec 6)) (y (_ BitVec 6))) Bool
  (bvule (bvadd x (_ bv2 6)) (_ bv63 6)))

(define-fun |predicate.10| ((x (_ BitVec 6)) (y (_ BitVec 6))) Bool
  (bvule (bvsub y x) (_ bv2 6)))

(define-fun |predicate.11| ((x (_ BitVec 6)) (y (_ BitVec 6))) Bool
  (= (bvor x y) y))