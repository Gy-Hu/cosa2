(define-fun |clause.0| ((x (_ BitVec 6)) (y (_ BitVec 6))) Bool
  (or (not (bvult x y))
      (not (= y (_ bv61 6)))))

(define-fun |clause.1| ((x (_ BitVec 6))) Bool
  (or (not (bvult x (_ bv32 6)))
      (not (bvugt x (_ bv16 6)))))

(define-fun |clause.2| ((x (_ BitVec 6)) (y (_ BitVec 6))) Bool
  (= (bvand x #b000001) (bvand y #b000001)))

(define-fun |clause.3| ((x (_ BitVec 6)) (y (_ BitVec 6))) Bool
  (not (and (not (bvult y (bvadd x #b000011))) 
            (= ((_ extract 2 2) x) ((_ extract 2 2) #b011001)))))

(define-fun |clause.4| ((x (_ BitVec 6)) (y (_ BitVec 6))) Bool
  (not (and (not (bvult y (bvadd x #b000011))) 
            (= ((_ extract 1 1) x) ((_ extract 1 1) #b101111)))))

(define-fun |clause.5| ((x (_ BitVec 6)) (y (_ BitVec 6))) Bool
  (not (and (not (bvult y (bvadd x #b000011))) 
            (= ((_ extract 3 3) x) ((_ extract 3 3) #b010101)))))

(define-fun |clause.6| ((x (_ BitVec 6)) (y (_ BitVec 6))) Bool
  (not (and (not (bvult y (bvadd x #b000011))) 
            (= ((_ extract 5 5) x) ((_ extract 5 5) #b001101)))))

(define-fun |clause.7| ((x (_ BitVec 6)) (y (_ BitVec 6))) Bool
  (= y (bvadd x #b000010)))