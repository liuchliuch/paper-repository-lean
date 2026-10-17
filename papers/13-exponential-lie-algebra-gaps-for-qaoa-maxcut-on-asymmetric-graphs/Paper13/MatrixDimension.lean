import Paper13.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Projection

noncomputable section
namespace Paper13
open Matrix

/-- Multiplication by i exchanges the Hermitian and skew-Hermitian real spaces. -/
def selfSkewEquiv (ι : Type*) [Fintype ι] [DecidableEq ι] :
    selfAdjoint (Matrix ι ι ℂ) ≃ₗ[ℝ] skewAdjoint (Matrix ι ι ℂ) where
  toFun x := ⟨Complex.I • x.val, by
    change star (Complex.I • x.val) = -(Complex.I • x.val)
    rw [star_smul, x.property.star_eq]
    simp⟩
  invFun y := ⟨(-Complex.I) • y.val, by
    change star ((-Complex.I) • y.val) = (-Complex.I) • y.val
    rw [star_smul, y.property]
    simp⟩
  left_inv x := by apply Subtype.ext; simp [smul_smul]
  right_inv y := by apply Subtype.ext; simp [smul_smul]
  map_add' x y := by apply Subtype.ext; simp [smul_add]
  map_smul' r x := by apply Subtype.ext; exact smul_comm _ _ _

/-- The real dimension of all skew-Hermitian complex matrices. -/
theorem skewAdjoint_finrank (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Module.finrank ℝ (skewAdjoint (Matrix ι ι ℂ)) = (Fintype.card ι)^2 := by
  letI : Module.Finite ℝ (selfAdjoint (Matrix ι ι ℂ)) :=
    Module.Finite.of_injective (selfAdjoint.submodule ℝ (Matrix ι ι ℂ)).subtype (Submodule.subtype_injective _)
  letI : Module.Finite ℝ (skewAdjoint (Matrix ι ι ℂ)) :=
    Module.Finite.of_injective (skewAdjoint.submodule ℝ (Matrix ι ι ℂ)).subtype (Submodule.subtype_injective _)
  have h := (StarModule.decomposeProdAdjoint ℝ (Matrix ι ι ℂ)).finrank_eq
  have he := (selfSkewEquiv ι).finrank_eq
  rw [Module.finrank_prod, he, finrank_real_of_complex] at h
  have hc : Module.finrank ℂ (Matrix ι ι ℂ) = (Fintype.card ι)^2 := by
    rw [Module.finrank_matrix]
    simp [pow_two]
  rw [hc] at h
  omega

/-- Trace equals range dimension for an idempotent complex matrix. -/
theorem trace_eq_range_finrank {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℂ) (hP : P * P = P) :
    Matrix.trace P = (Module.finrank ℂ (LinearMap.range (Matrix.toLin' P)) : ℂ) := by
  have hi : IsIdempotentElem (Matrix.toLin' P) := by
    change Matrix.toLin' P ∘ₗ Matrix.toLin' P = Matrix.toLin' P
    rw [← Matrix.toLin'_mul, hP]
  simpa only [Matrix.trace_toLin'_eq] using
    (LinearMap.IsIdempotentElem.isProj_range (Matrix.toLin' P) hi).trace

/-- The two parity projectors refine an invariant idempotent. -/
def parityRefinement {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R F : Matrix ι ι ℂ) (s : ℂ) : Matrix ι ι ℂ := (2 : ℂ)⁻¹ • (R + s • (R * F))

lemma parityRefinement_idem {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R F : Matrix ι ι ℂ) (hR : R * R = R) (hF : F * F = 1)
    (hcomm : R * F = F * R) (s : ℂ) (hs : s*s = 1) :
    parityRefinement R F s * parityRefinement R F s = parityRefinement R F s := by
  have hRF : R * (R * F) = R * F := by rw [← mul_assoc, hR]
  have hFR : (R * F) * R = R * F := by rw [mul_assoc, ← hcomm, ← mul_assoc, hR]
  have hFF : (R * F) * (R * F) = R := by
    rw [mul_assoc, ← mul_assoc F R F, ← hcomm, mul_assoc R F F, hF, mul_one, hR]
  have hsroot : s = 1 ∨ s = -1 := by
    have hz : (s - 1) * (s + 1) = 0 := by calc
      _ = s*s - 1 := by ring
      _ = 0 := by rw [hs]; ring
    rcases mul_eq_zero.mp hz with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  rcases hsroot with rfl | rfl <;>
    simp only [parityRefinement, smul_mul_smul, add_mul, mul_add, smul_mul_assoc,
    mul_smul_comm, hR, hRF, hFR, smul_smul, hs, one_smul, hFF]
  all_goals module

/-- A commuting involution of zero restricted trace splits a block into equal halves.
No rank/trace identification or equal-dimension conclusion is assumed. -/
theorem parity_half_rank {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R F : Matrix ι ι ℂ) (hR : R * R = R) (hF : F * F = 1)
    (hcomm : R * F = F * R) (htrace : Matrix.trace (R * F) = 0) :
    2 * Module.finrank ℂ (LinearMap.range (Matrix.toLin' (parityRefinement R F 1))) =
      Module.finrank ℂ (LinearMap.range (Matrix.toLin' R)) ∧
    2 * Module.finrank ℂ (LinearMap.range (Matrix.toLin' (parityRefinement R F (-1)))) =
      Module.finrank ℂ (LinearMap.range (Matrix.toLin' R)) := by
  have ht (s : ℂ) : Matrix.trace (parityRefinement R F s) = (2 : ℂ)⁻¹ * Matrix.trace R := by
    simp [parityRefinement, Matrix.trace_add, Matrix.trace_smul, htrace]
  constructor
  · have h := ht 1
    rw [trace_eq_range_finrank _ (parityRefinement_idem R F hR hF hcomm 1 (by norm_num)),
      trace_eq_range_finrank R hR] at h
    have h' : (2 : ℂ) * (Module.finrank ℂ (LinearMap.range (Matrix.toLin' (parityRefinement R F 1))) : ℂ) =
        (Module.finrank ℂ (LinearMap.range (Matrix.toLin' R)) : ℂ) := by rw [h]; field_simp
    exact_mod_cast h'
  · have h := ht (-1)
    rw [trace_eq_range_finrank _ (parityRefinement_idem R F hR hF hcomm (-1) (by norm_num)),
      trace_eq_range_finrank R hR] at h
    have h' : (2 : ℂ) * (Module.finrank ℂ (LinearMap.range (Matrix.toLin' (parityRefinement R F (-1)))) : ℂ) =
        (Module.finrank ℂ (LinearMap.range (Matrix.toLin' R)) : ℂ) := by rw [h]; field_simp
    exact_mod_cast h'
end Paper13
