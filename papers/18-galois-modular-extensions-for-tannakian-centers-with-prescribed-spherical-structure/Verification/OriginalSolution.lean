import Paper18.Results.CategoricalLacabanne
import Paper18.Category.PointedTannakian

/-! Original categorical solutions. This module never imports the challenge.
Only completed original targets are exported here. -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Paper18.Category
namespace P18Original
universe v u w
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)] [BraidedCategory C]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

include S in
theorem lemma2_1 (J : PivotalStructure C) (hC : IsNondegenerate (C := C)) :
    ∃ t : C, ∃ A : TensorInverse t,
      (∀ X : C, Simple X →
        (doubleBraiding t X).hom =
          (J.rightDim X / J.rightDim (dual C X)) • 𝟙 (t ⊗ X)) ∧
      (J.twistIso A.inverse).hom = 𝟙 A.inverse ∧
      (∀ u : C, TensorInverse u →
        (∀ X : C, Simple X →
          (doubleBraiding u X).hom =
            (J.rightDim X / J.rightDim (dual C X)) • 𝟙 (u ⊗ X)) →
        Nonempty (t ≅ u)) :=
  Paper18.Category.lemma2_1 S J hC

end P18Original

namespace P18Original
open Paper18.Category.AppendixBPointed

theorem appendixB :
    ∃ _T : TannakianCenter B (Multiplicative (ZMod 2)),
      IsModular canonicalPivotal ∧
      canonicalPivotal.twistNatIso = twist ∧
      prescribedPivotal.Spherical ∧
      centerPrescribedPivotal = centerCanonicalPivotal ∧
      PreservesPivotal BInclusion prescribedPivotal nonsphericalPivotalExtension ∧
      ¬ nonsphericalPivotalExtension.Spherical ∧
      (∀ J : PivotalStructure Vec, J.Spherical →
        ¬ PreservesPivotal BInclusion prescribedPivotal J) ∧
      (PointedVec.skeleton Paper18.PointedA).fusionBasis.totalFPdim =
        bSkeleton.fusionBasis.totalFPdim * bCenterSkeleton.fusionBasis.totalFPdim := by
  obtain ⟨T, _, h⟩ := appendixB_actual_counterexample
  exact ⟨T,h⟩

end P18Original
