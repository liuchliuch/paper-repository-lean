import Paper28.RelativeCarrierDeformation
import Mathlib.Analysis.Convex.StdSimplex

/-! Actual normalized spherical barycentric simplices. Their compact unit
finite-coordinate support is proved, providing the geometric support bridge
for the relative deformation of polyhedral chains. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def sphericalBarycentricVector {k : ℕ} (v : Fin (k+1) → H)
    (t : stdSimplex ℝ (Fin (k+1))) : H := ∑ i, t.val i • v i

theorem sphericalBarycentricVector_ne_zero {k : ℕ} (v : Fin (k+1) → H)
    (c : H) (hHemisphere : ∀ i, 0 < inner ℝ c (v i))
    (t : stdSimplex ℝ (Fin (k+1))) : sphericalBarycentricVector v t ≠ 0 := by
  have ht : ∃ i, 0 < t.val i := by
    by_contra h
    push_neg at h
    have hh := Finset.sum_nonpos (s := Finset.univ) (fun i _ => h i)
    rw [t.property.2] at hh
    linarith
  obtain ⟨i,hi⟩ := ht
  have hPos : 0 < ∑ j, t.val j * inner ℝ c (v j) := by
    apply Finset.sum_pos'
    · intro j _
      exact mul_nonneg (t.property.1 j) (hHemisphere j).le
    · exact ⟨i,Finset.mem_univ _,mul_pos hi (hHemisphere i)⟩
  intro hz
  have hInner : inner ℝ c (sphericalBarycentricVector v t) = ∑ j, t.val j * inner ℝ c (v j) := by
    simp only [sphericalBarycentricVector,inner_sum,real_inner_smul_right]
  rw [hz,inner_zero_right] at hInner
  linarith

def sphericalSimplexPatch {k : ℕ} (v : Fin (k+1) → H) : Set H :=
  Set.range (fun t : stdSimplex ℝ (Fin (k+1)) => sphericalNormalize (sphericalBarycentricVector v t))

theorem sphericalSimplexPatch_unit {k : ℕ} (v : Fin (k+1) → H)
    (c : H) (hHemisphere : ∀ i, 0 < inner ℝ c (v i)) :
    ∀ u ∈ sphericalSimplexPatch v, ‖u‖ = 1 := by
  rintro u ⟨t,rfl⟩
  exact sphericalNormalize_norm _ (sphericalBarycentricVector_ne_zero v c hHemisphere t)

theorem sphericalSimplexPatch_isCompact {k : ℕ} (v : Fin (k+1) → H)
    (c : H) (hHemisphere : ∀ i, 0 < inner ℝ c (v i)) : IsCompact (sphericalSimplexPatch v) := by
  have hVector : Continuous (sphericalBarycentricVector v) := by
    apply continuous_finset_sum
    intro i _
    exact (((continuous_apply i).comp continuous_subtype_val).smul continuous_const)
  have hNorm : Continuous (fun t : stdSimplex ℝ (Fin (k+1)) =>
      sphericalNormalize (sphericalBarycentricVector v t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (sphericalNormalize_contDiffAt _ (sphericalBarycentricVector_ne_zero v c hHemisphere t) 1).continuousAt.comp
      hVector.continuousAt
  simpa only [sphericalSimplexPatch,image_univ] using isCompact_univ.image hNorm

theorem sphericalSimplexPatch_mem_subspace {k : ℕ} (v : Fin (k+1) → H)
    (S : Submodule ℝ H) (hv : ∀ i, v i ∈ S) : sphericalSimplexPatch v ⊆ S := by
  rintro u ⟨t,rfl⟩
  apply S.smul_mem
  exact S.sum_mem (fun i _ => S.smul_mem _ (hv i))

end Paper28
