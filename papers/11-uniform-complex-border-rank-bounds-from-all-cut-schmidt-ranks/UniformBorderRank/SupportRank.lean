import UniformBorderRank.MatrixCore
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Matrix support spaces and preservation of rank by faithful maps. -/
noncomputable section
namespace UniformBorderRank
open Finset Module

lemma linearMap_apply_eq_sum_single {I J : Type*} [Fintype I] [DecidableEq I]
    (f : (I → ℂ) →ₗ[ℂ] (J → ℂ)) (x : I → ℂ) (j : J) :
    f x j = ∑ i, x i * f (Pi.single i 1) j := by
  classical
  have he : (∑ i, x i • (Pi.single i (1 : ℂ) : I → ℂ)) = x := by
    ext i
    simp [Pi.single_apply, mul_ite]
  have h := congrArg (fun y : I → ℂ => f y j) he
  simpa only [map_sum, Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul] using h.symm

lemma rowSpan_finrank_transpose {I J : Type*} [Fintype I] [Fintype J]
    (M : I → J → ℂ) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range M)) =
      Module.finrank ℂ (Submodule.span ℂ (Set.range (fun j i => M i j))) := by
  have h₁ := Matrix.rank_eq_finrank_span_row (M : Matrix I J ℂ)
  have h₂ := Matrix.rank_eq_finrank_span_row (Matrix.transpose (M : Matrix I J ℂ))
  change Matrix.rank (M : Matrix I J ℂ) = Module.finrank ℂ (Submodule.span ℂ (Set.range M)) at h₁
  change Matrix.rank (Matrix.transpose (M : Matrix I J ℂ)) =
    Module.finrank ℂ (Submodule.span ℂ (Set.range (fun j i => M i j))) at h₂
  exact h₁.symm.trans ((Matrix.rank_transpose _).symm.trans h₂)

lemma rowSpan_finrank_map_eq {I J J' : Type*} [Fintype J]
    (M : I → J → ℂ) (f : (J → ℂ) →ₗ[ℂ] (J' → ℂ))
    (hf : Function.Injective (f.comp (Submodule.span ℂ (Set.range M)).subtype)) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range (fun i => f (M i)))) =
      Module.finrank ℂ (Submodule.span ℂ (Set.range M)) := by
  have he : Submodule.span ℂ (Set.range (fun i => f (M i))) =
      (Submodule.span ℂ (Set.range M)).map f := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [he]
  have h := LinearMap.finrank_range_of_inj hf
  have heRange : LinearMap.range (f.comp (Submodule.span ℂ (Set.range M)).subtype) =
      (Submodule.span ℂ (Set.range M)).map f := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x.val, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
  rw [heRange] at h
  exact h

/-- If each side map is injective on the corresponding original support,
the transformed matrix has exactly the original rank. -/
theorem rowSpan_finrank_faithful_maps {I J I' J' : Type*}
    [Fintype I] [Fintype J] [Fintype I'] [Fintype J']
    (M : I → J → ℂ)
    (l : (I → ℂ) →ₗ[ℂ] (I' → ℂ)) (f : (J → ℂ) →ₗ[ℂ] (J' → ℂ))
    (hl : Function.Injective (l.comp (Submodule.span ℂ (Set.range (fun j i => M i j))).subtype))
    (hf : Function.Injective (f.comp (Submodule.span ℂ (Set.range M)).subtype)) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range
      (fun i' j' => l (fun i => f (M i) j') i'))) =
      Module.finrank ℂ (Submodule.span ℂ (Set.range M)) := by
  classical
  let C := Submodule.span ℂ (Set.range (fun j i => M i j))
  let C' := Submodule.span ℂ (Set.range (fun j' i => f (M i) j'))
  have hsub : C' ≤ C := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j', rfl⟩
    have he : (fun i => f (M i) j') = ∑ j, f (Pi.single j 1) j' • (fun i => M i j) := by
      ext i
      rw [linearMap_apply_eq_sum_single]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      apply sum_congr rfl
      intro j _
      ring
    change (fun i => f (M i) j') ∈ C
    rw [he]
    apply Submodule.sum_mem
    intro j _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hl' : Function.Injective (l.comp C'.subtype) := by
    intro x y h
    have hh := hl (show (l.comp C.subtype) ⟨x.val, hsub x.property⟩ =
      (l.comp C.subtype) ⟨y.val, hsub y.property⟩ from h)
    exact Subtype.ext (congrArg (fun z : C => z.val) hh)
  calc
    _ = Module.finrank ℂ (Submodule.span ℂ (Set.range (fun j' i' => l (fun i => f (M i) j') i'))) :=
      rowSpan_finrank_transpose _
    _ = Module.finrank ℂ C' := rowSpan_finrank_map_eq _ l hl'
    _ = Module.finrank ℂ (Submodule.span ℂ (Set.range (fun i => f (M i)))) :=
      (rowSpan_finrank_transpose _).symm
    _ = _ := rowSpan_finrank_map_eq M f hf

end UniformBorderRank
