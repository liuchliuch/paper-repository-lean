import UniformBorderRank.FlatteningBounds
import UniformBorderRank.BlockProducts

/-! Bounds at trivial cuts as well as the original nontrivial cuts. -/
noncomputable section
namespace UniformBorderRank
open Finset

lemma rowSpan_finrank_le_card_rows {I J : Type*} [Fintype I] [Fintype J]
    (M : I → J → ℂ) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range M)) ≤ Fintype.card I := by
  rw [rowSpan_finrank_transpose M]
  simpa using Submodule.finrank_le (Submodule.span ℂ (Set.range (fun j i => M i j)))

/-- A nonzero decomposable tensor has rank exactly one at every cut,
including the empty and full cuts. -/
theorem schmidtRank_eq_one_of_isProduct {N : ℕ} {d : Fin N → ℕ}
    {T : Coeffs d} (hT : T ≠ 0) (hprod : isProduct T) (S : Finset (Fin N)) :
    schmidtRank d T S = 1 := by
  have hlo := schmidtRank_pos_of_ne_zero T hT S
  have hhi := schmidtRank_le_of_cpRankLe (cpRankLe_one_of_isProduct hprod) S
  omega

end UniformBorderRank
