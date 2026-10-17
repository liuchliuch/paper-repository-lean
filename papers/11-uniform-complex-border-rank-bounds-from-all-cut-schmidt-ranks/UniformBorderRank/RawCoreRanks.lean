import UniformBorderRank.RawCore
import UniformBorderRank.AnchorTensor

/-! Boundary support ranks of the actual anchored coefficient tensor. -/
noncomputable section
namespace UniformBorderRank
set_option maxHeartbeats 1200000
open Finset

/-- The left boundary support of the full raw coefficient tensor is bounded
by its anchored empty-cut rank.  No coordinate space is assumed nonempty. -/
theorem boundary_row_rank_le_anchoredCut_empty {N : ℕ} {d : Fin N → ℕ}
    {I J : Type*} [Fintype I] [Fintype J] (H : I → J → Coeffs d) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range
      (fun a (z : J × (∀ i, Fin (d i))) => H a z.1 z.2))) ≤
      Module.finrank ℂ (Submodule.span ℂ (Set.range (anchoredCut (d := d) H ∅))) := by
  classical
  let z : ∀ i ∈ (∅ : Finset (Fin N)), Fin (d i) := by
    intro i hi
    simp at hi
  have he : (fun a (w : J × (∀ i, Fin (d i))) => H a w.1 w.2) =
      (fun (a : I) (w : J × (∀ i, Fin (d i))) => anchoredCut (d := d) H ∅ (a, z) (w.1, fun i _ => w.2 i)) := by
    funext a w
    simp [anchoredCut, flatIndexEquiv]
  rw [he]
  exact rowSpan_finrank_reindex_le (anchoredCut (d := d) H ∅)
    (fun a : I => (a, z)) (fun w : J × (∀ i, Fin (d i)) => (w.1, fun i _ => w.2 i))

/-- The right boundary support of the full raw coefficient tensor is bounded
by its anchored full-cut rank, with the row/column equality proved by transpose. -/
theorem boundary_column_rank_le_anchoredCut_univ {N : ℕ} {d : Fin N → ℕ}
    {I J : Type*} [Fintype I] [Fintype J] (H : I → J → Coeffs d) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range
      (fun b (z : I × (∀ i, Fin (d i))) => H z.1 b z.2))) ≤
      Module.finrank ℂ (Submodule.span ℂ (Set.range (anchoredCut (d := d) H univ))) := by
  classical
  let z : ∀ i ∈ ((univ : Finset (Fin N))ᶜ), Fin (d i) := by
    intro i hi
    simp at hi
  have he : (fun (w : I × (∀ i, Fin (d i))) b => H w.1 b w.2) =
      (fun (w : I × (∀ i, Fin (d i))) (b : J) => anchoredCut (d := d) H univ (w.1, fun i _ => w.2 i) (b, z)) := by
    funext w b
    simp [anchoredCut, flatIndexEquiv]
  rw [rowSpan_finrank_transpose (fun b (w : I × (∀ i, Fin (d i))) => H w.1 b w.2), he]
  exact rowSpan_finrank_reindex_le (anchoredCut (d := d) H univ)
    (fun w : I × (∀ i, Fin (d i)) => (w.1, fun i _ => w.2 i)) (fun b : J => (b, z))

end UniformBorderRank
