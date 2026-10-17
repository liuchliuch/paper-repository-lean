import Paper18.Category.DiagonalAlgebraSeparableBasic
import Paper18.Category.DiagonalAlgebraPairingCounit
import Paper18.Category.PivotalDimension

/-! # Normalization of the actual connected Frobenius section -/
noncomputable section
set_option maxHeartbeats 1000000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj
universe v u
namespace Paper18.Category.DiagonalAlgebra
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {A : C} [MonObj A] (P : ModuleBalancing.MultiplicationPairing A)

/-- The actual closed Frobenius cup-cap scalar. -/
def frobeniusScalar : ℂ := unitScalarEquiv (C := C)
  (@ExactPairing.coevaluation C _ _ A A P.pairing ≫
    @ExactPairing.evaluation C _ _ A A P.pairing)

/-- Connectedness and normalized counit evaluate multiplication on the
actual Frobenius cup. -/
lemma frobeniusCup_mul (hA : Module.finrank ℂ (𝟙_ C ⟶ A) = 1)
    (hP : η[A] ≫ P.counit = 𝟙 _) :
    @ExactPairing.coevaluation C _ _ A A P.pairing ≫ μ[A] = frobeniusScalar P • η[A] := by
  letI := P.pairing
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hA
    (connected_one_ne_zero A hA) (η_ A A ≫ μ[A])
  have he : c • 𝟙 (𝟙_ C) = η_ A A ≫ ε_ A A := by
    have h := congrArg (fun k => k ≫ P.counit) hc
    simpa only [Linear.smul_comp, hP, assoc, P.evaluation] using h
  have hs : c = frobeniusScalar P := by
    simpa only [unitScalarEquiv_smul_id, frobeniusScalar] using
      congrArg (unitScalarEquiv (C := C)) he
  rw [← hc, hs]

/-- The actual Frobenius section is special, with scalar equal to its
actual cup-cap closure. -/
lemma frobeniusComultiplication_mul (hA : Module.finrank ℂ (𝟙_ C ⟶ A) = 1)
    (hP : η[A] ≫ P.counit = 𝟙 _) :
    frobeniusComultiplication P ≫ μ[A] = frobeniusScalar P • 𝟙 A := by
  letI := P.pairing
  dsimp [frobeniusComultiplication, tensorLeftHomEquiv]
  simp only [assoc]
  rw [MonObj.mul_assoc_flip]
  simp only [assoc, Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight_assoc, frobeniusCup_mul P hA hP]
  simp only [MonoidalLinear.smul_whiskerRight, Linear.smul_comp, Linear.comp_smul, MonObj.one_mul,
    Iso.inv_hom_id]

/-- A nonzero actual Frobenius closure normalizes the derived actual
bimodule comultiplication into a genuine separability section. -/
def separableOfFrobeniusScalar (hA : Module.finrank ℂ (𝟙_ C ⟶ A) = 1)
    (hP : η[A] ≫ P.counit = 𝟙 _) (h : frobeniusScalar P ≠ 0) : SeparableAlgebra A where
  section_ := (frobeniusScalar P)⁻¹ • frobeniusComultiplication P
  section_mul := by
    rw [Linear.smul_comp, frobeniusComultiplication_mul P hA hP, smul_smul,
      inv_mul_cancel₀ h, one_smul]
  left_linear := by
    simp only [Linear.comp_smul, MonoidalLinear.whiskerLeft_smul, Linear.smul_comp]
    rw [frobeniusComultiplication_left_linear]
  right_linear := by
    simp only [Linear.comp_smul, MonoidalLinear.smul_whiskerRight, Linear.smul_comp]
    rw [frobeniusComultiplication_right_linear]

end Paper18.Category.DiagonalAlgebra
