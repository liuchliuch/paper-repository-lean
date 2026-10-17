import Paper20.YoungCommonCovers
import Paper20.YoungBoundary

namespace Paper20.YoungCorners
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-- The diagonal Young-lattice differential identity, proved via the
explicit finite boundary bijection. -/
theorem cover_count_difference (μ : YoungDiagram) :
    Nat.card {γ : YoungDiagram // Covers μ γ}=
      Nat.card {κ : YoungDiagram // Covers κ μ}+1 := by
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,upperCover_card,lowerCover_card]
  exact addable_card_eq_removable_add_one μ

def commonUpperSelfEquiv (μ : YoungDiagram) :
    {γ : YoungDiagram // Covers μ γ ∧ Covers μ γ} ≃ {γ : YoungDiagram // Covers μ γ} where
  toFun γ := ⟨γ.val,γ.property.1⟩
  invFun γ := ⟨γ.val,γ.property,γ.property⟩
  left_inv γ := Subtype.ext rfl
  right_inv γ := Subtype.ext rfl

def commonLowerSelfEquiv (μ : YoungDiagram) :
    {κ : YoungDiagram // Covers κ μ ∧ Covers κ μ} ≃ {κ : YoungDiagram // Covers κ μ} where
  toFun κ := ⟨κ.val,κ.property.1⟩
  invFun κ := ⟨κ.val,κ.property,κ.property⟩
  left_inv κ := Subtype.ext rfl
  right_inv κ := Subtype.ext rfl

/-- The complete single-box differential identity for actual Young
shapes at the same level. This supplies the genuine combinatorial
branching foundation rather than a postulated dimension-sum formula. -/
theorem young_differential_identity (μ ν : YoungDiagram)
    (hn : μ.cells.card=ν.cells.card) :
    Nat.card {γ : YoungDiagram // Covers μ γ ∧ Covers ν γ}=
      Nat.card {κ : YoungDiagram // Covers κ μ ∧ Covers κ ν}+(if μ=ν then 1 else 0) := by
  classical
  by_cases he : μ=ν
  · subst ν
    rw [if_pos rfl,Nat.card_congr (commonUpperSelfEquiv μ),
      Nat.card_congr (commonLowerSelfEquiv μ)]
    exact cover_count_difference μ
  · rw [if_neg he,Nat.add_zero]
    exact common_cover_card μ ν hn he

end
end Paper20.YoungCorners
