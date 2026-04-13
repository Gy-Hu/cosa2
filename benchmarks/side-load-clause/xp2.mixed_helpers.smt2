; Mixed helper file for xp2 benchmark
; Contains predicates, clauses, and assertions in a single file.
; Pono automatically categorizes them by prefix.

; --- Predicates: abstraction hints for IC3ng ---
(define-fun |predicate.0| ((x (_ BitVec 6)) (y (_ BitVec 6))) Bool
  (bvult x y))

(define-fun |predicate.1| ((x (_ BitVec 6)) (y (_ BitVec 6))) Bool
  (bvule x (_ bv61 6)))

; --- Clauses: pre-validated lemmas added to frame F1 ---
(define-fun |clause.0| ((x (_ BitVec 6)) (y (_ BitVec 6))) Bool
  (= (bvand x #b000001) (bvand y #b000001)))

(define-fun |clause.1| ((x (_ BitVec 6)) (y (_ BitVec 6))) Bool
  (= y (bvadd x #b000010)))

; --- Assertions: conjoined with the property for strengthening ---
(define-fun |assertion.0| ((x (_ BitVec 6)) (y (_ BitVec 6))) Bool
  (= (bvsub y x) (_ bv2 6)))
