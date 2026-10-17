import Paper18.Category.PivotalPartialTrace
import Paper18.Category.HopfLinkBasic

/-!
# Multiplicativity of actual Hopf-link rows

Closing the moving strand of a double braiding gives an actual endomorphism
of the retained object. The hexagon identities and partial-trace Fubini prove
its tensor composition law before Schur's lemma extracts any scalars.
-/
noncomputable section
open Classical
universe v u w
namespace Paper18.Category
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory CategoryTheory.Limits
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C]

omit [RightRigidCategory C] in
/-- Expanding the double braiding against a tensor product by the two actual
hexagon identities exposes the inner double braiding. -/
lemma doubleBraiding_tensor_right_expand (A X Y : C) :
    (α_ A X Y).hom ≫ (doubleBraiding A (X ⊗ Y)).hom ≫ (α_ A X Y).inv =
      (β_ A X).hom ▷ Y ≫ (α_ X A Y).hom ≫
        X ◁ (doubleBraiding A Y).hom ≫ (α_ X A Y).inv ≫ (β_ X A).hom ▷ Y := by
  simp only [doubleBraiding, Iso.trans_hom, braiding_tensor_left_hom,
    braiding_tensor_right_hom, whiskerLeft_comp, assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id_assoc, Iso.hom_inv_id, comp_id]

namespace PivotalStructure
variable (J : PivotalStructure C)

/-- The actual open Hopf loop around a retained object. -/
def hopfLoop (A X : C) : A ⟶ A := J.rightPartialTrace X (doubleBraiding A X).hom

/-- Two successive actual Hopf loops are the loop labelled by the tensor
product. This is a morphism identity, prior to scalar extraction. -/
theorem hopfLoop_tensor (A X Y : C) :
    J.hopfLoop A (X ⊗ Y) = J.hopfLoop A Y ≫ J.hopfLoop A X := by
  unfold hopfLoop
  rw [J.rightPartialTrace_tensor, doubleBraiding_tensor_right_expand]
  have hn := J.rightPartialTrace_naturality Y (β_ A X).hom
    ((α_ X A Y).hom ≫ X ◁ (doubleBraiding A Y).hom ≫ (α_ X A Y).inv) (β_ X A).hom
  simp only [assoc] at hn
  rw [hn, J.rightPartialTrace_whiskerLeft]
  rw [← braiding_naturality_left_assoc]
  change J.rightPartialTrace X
    ((J.rightPartialTrace Y (doubleBraiding A Y).hom) ▷ X ≫
      (doubleBraiding A X).hom) = _
  simpa only [id_whiskerRight, comp_id] using
    J.rightPartialTrace_naturality X (J.rightPartialTrace Y (doubleBraiding A Y).hom)
      (doubleBraiding A X).hom (𝟙 A)

/-- Closing the remaining strand recovers the actual Hopf-link trace. -/
lemma rightTrace_hopfLoop (A X : C) :
    J.rightTrace (J.hopfLoop A X) = J.rightTrace (doubleBraiding A X).hom :=
  J.rightTrace_rightPartialTrace A X _

variable [Preadditive C] [Linear ℂ C] [HasKernels C]
  [HasFiniteBiproducts C] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

include S in
/-- On a simple retained object, the actual open loop is the Hopf-link scalar
divided by its nonzero categorical dimension. -/
lemma hopfLoop_eq_smul (A X : C) [Simple A] :
    J.hopfLoop A X = (J.hopfLink A X / J.rightDim A) • 𝟙 A := by
  obtain ⟨c, hc⟩ := CategoryTheory.endomorphism_simple_eq_smul_id ℂ (J.hopfLoop A X)
  have ht : J.hopfLink A X = c * J.rightDim A := by
    rw [hopfLink, ← J.rightTrace_hopfLoop, ← hc]
    exact J.rightTrace_smul_id A c
  rw [ht, mul_div_cancel_right₀ c (J.rightDim_ne_zero S A)]
  exact hc.symm

include S in
/-- Every actual Hopf-link row indexed by a simple object multiplies on
arbitrary tensor products, as a consequence of the morphism-level loop law. -/
theorem hopfLink_tensor (A X Y : C) [Simple A] :
    J.hopfLink A (X ⊗ Y) = J.hopfLink A X * J.hopfLink A Y / J.rightDim A := by
  have h := J.hopfLoop_tensor A X Y
  rw [J.hopfLoop_eq_smul S, J.hopfLoop_eq_smul S,
    J.hopfLoop_eq_smul S] at h
  have hs : J.hopfLink A (X ⊗ Y) / J.rightDim A =
      (J.hopfLink A Y / J.rightDim A) * (J.hopfLink A X / J.rightDim A) := by
    apply smul_left_injective ℂ (CategoryTheory.id_nonzero A)
    simpa only [Linear.smul_comp, Linear.comp_smul, id_comp, smul_smul, mul_comm] using h
  have hd := J.rightDim_ne_zero S A
  field_simp [hd] at hs ⊢
  linear_combination hs

end PivotalStructure
end Paper18.Category
