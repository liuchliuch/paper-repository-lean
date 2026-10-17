import Paper20.YoungDimensionBranching
import Paper20.YoungVacuumNorm
import Paper20.Polynomial

namespace Paper20.YoungShapes
open Matrix Finset Paper20.YoungCorners
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-- Restriction to the actual preceding finite level loses no lower
covers and introduces no additional diagrams. -/
def lowerSingleLevelEquiv {n : ℕ} (μ : Shape (n+1)) :
    {κ : Shape n // Covers κ.val μ.val} ≃ {κ : YoungDiagram // Covers κ μ.val} where
  toFun κ := ⟨κ.val.val,κ.property⟩
  invFun κ := ⟨⟨κ.val,by have := κ.property.2; have := μ.property; omega⟩,κ.property⟩
  left_inv κ := Subtype.ext (Subtype.ext rfl)
  right_inv κ := Subtype.ext rfl

/-- The actual hook quotient equals the actual number of single-box
paths from the empty diagram, derived from the proved common branching
recurrence and its empty-diagram value. -/
theorem vacuum_dimension (n : ℕ) : ∀ μ : Shape n, vacuum n μ=(dimension μ.val:ℤ) := by
  induction n with
  | zero =>
    intro μ
    have hμ : μ.val=⊥ := congrArg Subtype.val (Subsingleton.elim μ default)
    change (1:ℤ)=(dimension μ.val:ℤ)
    rw [hμ]
    have hz : (⊥:YoungDiagram).colLen 0=0 := by
      apply Nat.eq_zero_of_not_pos
      intro h
      have hm : (0,0) ∈ (⊥:YoungDiagram) := YoungDiagram.mem_iff_lt_colLen.mpr h
      simpa using hm
    simp [dimension,dimOf,hooksOf,YoungDiagram.rowLens,hz]
  | succ n ih =>
    intro μ
    change (∑ κ : Shape n, (if Covers κ.val μ.val then (1:ℤ) else 0)*vacuum n κ)=_
    simp_rw [ih]
    have he := Finset.sum_congr_set
      (s:={κ : Shape n | Covers κ.val μ.val})
      (fun κ => (if Covers κ.val μ.val then (1:ℤ) else 0)*(dimension κ.val:ℤ))
      (fun κ => (dimension κ.val.val:ℤ))
      (by intro κ hκ; dsimp only [Set.mem_setOf_eq] at hκ; dsimp only; rw [if_pos hκ,one_mul])
      (by intro κ hκ; dsimp only [Set.mem_setOf_eq] at hκ; dsimp only; rw [if_neg hκ,zero_mul])
    calc
      _ = ∑ κ : {κ : Shape n // Covers κ.val μ.val}, (dimension κ.val.val:ℤ) := he
      _ = ∑ κ : {κ : YoungDiagram // Covers κ μ.val}, (dimension κ.val:ℤ) :=
        Fintype.sum_equiv (lowerSingleLevelEquiv μ) _ _ (by intro κ; rfl)
      _ = _ := by exact_mod_cast dimension_branching μ.val (by rw [μ.property]; omega)

/-- The squared dimensions over the complete actual Young-diagram level
sum to n!, now for the very same executable hook quotient. -/
theorem dimension_square_sum (n : ℕ) :
    (∑ μ : Shape n, (dimension μ.val:ℤ)^2)=(n.factorial:ℤ) := by
  simpa only [vacuum_dimension] using vacuum_norm n

end
end Paper20.YoungShapes

namespace Paper20
open Finset YoungShapes
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- The original complete partition enumeration and original natural
hook quotient satisfy the dimension-square identity at every rank. -/
theorem dimSquareSum_eq_factorial (n : ℕ) : dimSquareSum n=n.factorial := by
  have he := sum_shapes n (fun p => (dimOf n p:ℤ)^2)
  have hd (μ : Shape n) : dimension μ.val=dimOf n μ.val.rowLens := by
    unfold dimension
    rw [μ.property]
  have hs := dimension_square_sum n
  simp_rw [hd] at hs
  rw [he] at hs
  unfold dimSquareSum
  rw [foldl_add_eq_sum,zero_add]
  change ((partitionsOf n).map (fun p => dimOf n p^2)).sum=n.factorial
  apply Int.ofNat_inj.mp
  simpa only [Nat.cast_list_sum,List.map_map,Function.comp_apply,Nat.cast_pow] using hs

end
end Paper20
