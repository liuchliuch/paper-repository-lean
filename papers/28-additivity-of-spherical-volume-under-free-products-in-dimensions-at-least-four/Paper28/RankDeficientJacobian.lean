import Paper28.CompoundJacobian
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Native zero Gram/exterior Jacobian when the image lies in a strictly
smaller dimensional subspace. This is used for collapsed projective
simplex images, rather than treating them as nondegenerate generators. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
open scoped InnerProductSpace

theorem gram_det_zero_of_not_linearIndependent
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {k : ℕ}
    (v : Fin k → H) (hv : ¬ LinearIndependent ℝ v) : (Matrix.gram ℝ v).det = 0 := by
  classical
  by_contra hdet
  have hUnit : IsUnit (Matrix.gram ℝ v) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hInj := Matrix.mulVec_injective_iff_isUnit.mpr hUnit
  apply hv
  rw [Fintype.linearIndependent_iff]
  intro w hw i
  have hM : Matrix.mulVec (Matrix.gram ℝ v) w = 0 := by
    funext j
    have h := congrArg (fun z => inner ℝ (v j) z) hw
    simp only [inner_sum,real_inner_smul_right,inner_zero_right] at h
    simpa only [Matrix.mulVec,dotProduct,Matrix.gram_apply,Pi.zero_apply,mul_comm] using h
  have hw0 : w = 0 := hInj (hM.trans (Matrix.mulVec_zero _).symm)
  exact congrFun hw0 i

theorem gram_det_zero_of_subspace_dimension
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    {k : ℕ} (v : Fin k → H) (W : Submodule ℝ H) (hW : Module.finrank ℝ W < k)
    (hv : ∀ i, v i ∈ W) : (Matrix.gram ℝ v).det = 0 := by
  apply gram_det_zero_of_not_linearIndependent
  intro hLI
  have hLI' : LinearIndependent ℝ (fun i => (⟨v i,hv i⟩ : W)) :=
    LinearIndependent.of_comp W.subtype hLI
  have hcard : k ≤ Module.finrank ℝ W := by simpa using hLI'.fintype_card_le_finrank
  omega

theorem exteriorJacobian_zero_of_subspace_dimension (hCB : CauchyBinetInput) {d m k : ℕ}
    (D : Matrix (Fin m) (Fin d) ℝ) (e : Fin k → EuclideanSpace ℝ (Fin d))
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin m))) (hW : Module.finrank ℝ W < k)
    (he : ∀ i, Matrix.toEuclideanLin D (e i) ∈ W) :
    exteriorJacobian (k := k) D (pluckerCoordinates e) = 0 := by
  rw [exteriorJacobian_plucker hCB,gram_det_zero_of_subspace_dimension _ W hW he,Real.sqrt_zero]

end Paper28
