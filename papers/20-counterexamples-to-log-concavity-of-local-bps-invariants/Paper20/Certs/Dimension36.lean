import Paper20.PartitionShift

set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace Paper20.Cert.Dimension36

def check (ps : List ℕ) : Bool := decide ((hooksOf ps).prod ∣ (36:ℕ).factorial)

def branch (a : ℕ) : Bool := ((partitionsCappedAux 36 a (36-a)).map (fun ps => a::ps)).all check

theorem branch_36 : branch 36 = true := by decide

theorem branch_35 : branch 35 = true := by decide

theorem branch_34 : branch 34 = true := by decide

theorem branch_33 : branch 33 = true := by decide

theorem branch_32 : branch 32 = true := by decide

theorem branch_31 : branch 31 = true := by decide

theorem branch_30 : branch 30 = true := by decide

theorem branch_29 : branch 29 = true := by decide

theorem branch_28 : branch 28 = true := by decide

theorem branch_27 : branch 27 = true := by decide

theorem branch_26 : branch 26 = true := by decide

theorem branch_25 : branch 25 = true := by decide

theorem branch_24 : branch 24 = true := by decide

theorem branch_23 : branch 23 = true := by decide

theorem branch_22 : branch 22 = true := by decide

theorem branch_21 : branch 21 = true := by decide

theorem branch_20 : branch 20 = true := by decide

theorem branch_19 : branch 19 = true := by decide

theorem branch_18 : branch 18 = true := by decide

theorem branch_17 : branch 17 = true := by decide

theorem branch_16 : branch 16 = true := by decide

theorem branch_15 : branch 15 = true := by decide

theorem branch_14 : branch 14 = true := by decide

theorem branch_13 : branch 13 = true := by decide

theorem branch_12 : branch 12 = true := by decide

theorem branch_11 : branch 11 = true := by decide

theorem branch_10 : branch 10 = true := by decide

theorem branch_09 : branch 9 = true := by decide

theorem branch_08 : branch 8 = true := by decide

theorem branch_07 : branch 7 = true := by decide

theorem branch_06 : branch 6 = true := by decide

theorem branch_05 : branch 5 = true := by decide

theorem branch_04 : branch 4 = true := by decide

theorem branch_03 : branch 3 = true := by decide

theorem branch_02 : branch 2 = true := by decide

theorem branch_01 : branch 1 = true := by decide

theorem all_checked : (partitionsOf 36).all check = true := by
  change (((List.range' 1 36).reverse.flatMap (fun a => (partitionsCappedAux 36 a (36-a)).map (fun ps => a::ps))).all check) = true
  simp only [List.all_flatMap]
  change ((List.range' 1 36).reverse.all branch) = true
  have hr : (List.range' 1 36).reverse = [36, 35, 34, 33, 32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1] := by decide
  rw [hr]
  simp only [List.all_cons, List.all_nil, branch_36, branch_35, branch_34, branch_33, branch_32, branch_31, branch_30, branch_29, branch_28, branch_27, branch_26, branch_25, branch_24, branch_23, branch_22, branch_21, branch_20, branch_19, branch_18, branch_17, branch_16, branch_15, branch_14, branch_13, branch_12, branch_11, branch_10, branch_09, branch_08, branch_07, branch_06, branch_05, branch_04, branch_03, branch_02, branch_01, Bool.and_self]

theorem hook_product_dvd (ps : List ℕ) (hp : ps ∈ partitionsOf 36) :
    (hooksOf ps).prod ∣ (36:ℕ).factorial := by
  have hc := List.all_eq_true.mp all_checked ps hp
  exact of_decide_eq_true hc

theorem dimension_times_hooks (ps : List ℕ) (hp : ps ∈ partitionsOf 36) :
    dimOf 36 ps*(hooksOf ps).prod = (36:ℕ).factorial := by
  exact Nat.div_mul_cancel (hook_product_dvd ps hp)

end Paper20.Cert.Dimension36
