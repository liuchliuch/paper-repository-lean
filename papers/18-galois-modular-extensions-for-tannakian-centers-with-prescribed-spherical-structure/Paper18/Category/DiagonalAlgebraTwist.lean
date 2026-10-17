import Paper18.Category.DiagonalAlgebraGeneralPairing
import Paper18.Category.DrinfeldPivotalFactorization
import Paper18.Category.PivotalReverseBraiding

/-! # Trivial actual twist on the canonical diagonal algebra -/
noncomputable section
set_option maxHeartbeats 1000000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped TensorProduct
universe v u w
namespace Paper18.Category.DiagonalAlgebra
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (J : PivotalStructure C) (hJ : J.Spherical)

include hJ

/-- The original and reversed twist scalars cancel on an actual dual pair. -/
lemma reverseSecondTwist_simple_dual (i : ι) :
    (Drinfeld.reverseSecondTwist J).hom.app
      (⟨S.simpleObject i, S.simpleObject (S.dualLabel i)⟩ : LinearTensor C C) = 𝟙 _ := by
  have hτ : J.twistScalar (S.simpleObject (S.dualLabel i)) = J.twistScalar (S.simpleObject i) := by
    rw [J.twistScalar_dualLabel S, (J.pivotalData_spherical S hJ) i]
    simp
  have hi := TensorAutomorphism.scalar_spec J.twistNatIso.symm (S.simpleObject (S.dualLabel i))
  rw [TensorAutomorphism.inv_scalar] at hi
  change (J.twistScalar (S.simpleObject (S.dualLabel i)))⁻¹ •
    𝟙 (S.simpleObject (S.dualLabel i)) = _ at hi
  change (J.twistIso (S.simpleObject i)).hom ⊗ₜ[ℂ]
    (letI : BraidedCategory C := reverseBraiding C;
      (J.twistIso (S.simpleObject (S.dualLabel i))).hom) =
    (𝟙 (S.simpleObject i)) ⊗ₜ[ℂ] (𝟙 (S.simpleObject (S.dualLabel i)))
  rw [J.twist_reverse_of_spherical S hJ]
  change _ ⊗ₜ[ℂ] J.twistNatIso.symm.hom.app (S.simpleObject (S.dualLabel i)) = _
  rw [← hi, ← J.twistScalar_spec, hτ]
  simp only [TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul,
    inv_mul_cancel₀ (J.twistScalar_ne_zero (S.simpleObject i)), one_smul]

/-- The prescribed reverse-second product twist fixes every actual
simple-dual diagonal summand. -/
lemma diagonalPair_twist (i : ι) :
    letI : BraidedCategory (DeligneProduct C C) := Drinfeld.deligneReverseSecondBraiding C
    ((Drinfeld.reverseSecondPivotal J).twistIso
      (DeligneProduct.pairObject S S i (S.dualLabel i))).hom = 𝟙 _ := by
  letI : BraidedCategory (DeligneProduct C C) := Drinfeld.deligneReverseSecondBraiding C
  change (Drinfeld.reverseSecondPivotal J).twistNatIso.hom.app _ = _
  rw [Drinfeld.reverseSecondPivotal_twist]
  change LinearMat.indexEquivHom _ _ = _
  ext ⟨⟩ ⟨⟩
  erw [LinearMat.indexEquivHom_apply]
  simpa [DeligneProduct.pairObject, Mat_.id_apply] using reverseSecondTwist_simple_dual S J hJ i

/-- The actual canonical algebra has trivial actual twist for the
prescribed spherical structure, even when C is degenerate. -/
theorem canonicalAlgebra_twist :
    letI : BraidedCategory (DeligneProduct C C) := Drinfeld.deligneReverseSecondBraiding C
    ((Drinfeld.reverseSecondPivotal J).twistIso (canonicalAlgebra S)).hom = 𝟙 _ := by
  letI : BraidedCategory (DeligneProduct C C) := Drinfeld.deligneReverseSecondBraiding C
  let K := Drinfeld.reverseSecondPivotal J
  have hd : (K.twistIso (diagonalObject S)).hom = 𝟙 _ := by
    apply biproduct.hom_ext'
    intro i
    erw [K.twist_naturality]
    rw [diagonalPair_twist S J hJ, id_comp]
    erw [comp_id]
  apply (cancel_epi (canonicalAlgebraIso S).inv).mp
  erw [K.twist_naturality]
  rw [hd, id_comp]
  erw [comp_id]

end Paper18.Category.DiagonalAlgebra
