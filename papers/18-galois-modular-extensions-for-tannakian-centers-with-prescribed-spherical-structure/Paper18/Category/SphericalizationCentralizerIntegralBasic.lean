import Paper18.Category.FusionSubcategoryFunctor
import Paper18.Category.CentralizerFusion

/-! # Actual integrality reflection for centralizers under braided tensor functors

The restricted functor is constructed on actual centralizer objects and
morphisms. Integrality then reflects by the already derived preservation
of categorical FP dimensions. No simple-image classification is required.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w v' u' w' v'' u''
namespace Paper18.Category
section Centralization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D]
  (U : D ⥤ C) [U.Braided] [U.Faithful]

/-- An actual faithful braided functor reflects the whole tested centralizer,
with an actual natural comparison identifying the tested images. -/
lemma centralizer_functor_comp_iso_iff {E : Type u''} [Category.{v''} E]
    (F : E ⥤ C) (Fhat : E ⥤ D) (e : Fhat ⋙ U ≅ F) (X : D) :
    X ∈ centralizer (Set.range Fhat.obj) ↔ U.obj X ∈ centralizer (Set.range F.obj) := by
  constructor
  · rintro h _ ⟨Y, rfl⟩
    exact (centralizes_iso_right (e.app Y)).mp ((h _ ⟨Y, rfl⟩).map U)
  · rintro h _ ⟨Y, rfl⟩
    exact (centralizes_map_iff U X (Fhat.obj Y)).mp
      ((centralizes_iso_right (e.app Y)).mpr (h _ ⟨Y, rfl⟩))
end Centralization
end Paper18.Category

namespace Paper18.Category.FiniteSemisimpleSkeleton
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)] [BraidedCategory C]
  [HasKernels C] [HasFiniteBiproducts C] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [RightRigidCategory D] [Simple (𝟙_ D)] [BraidedCategory D]
  [HasKernels D] [HasFiniteBiproducts D] [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)
  (U : D ⥤ C) [U.Additive] [U.Braided]

/-- Actual centralizer integrality reflects whenever the tested ambient
collection consists of actual isomorphic images of the source collection. -/
theorem centralizerIntegral_of_braided_images (A : Set D) (B : Set C)
    (himage : ∀ b ∈ B, ∃ a ∈ A, Nonempty (U.obj a ≅ b))
    (hI : S.CentralizerIntegral B) : T.CentralizerIntegral A := by
  let P := centralizerProperty A
  let Q := centralizerProperty B
  letI := T.fullSubcategoryHasKernels P
  letI := T.fullSubcategoryRightRigid P
  letI := T.fullSubcategorySimpleUnit P
  letI := S.fullSubcategoryHasKernels Q
  letI := S.fullSubcategoryRightRigid Q
  letI := S.fullSubcategorySimpleUnit Q
  let hpq : ∀ X : D, P X → Q (U.obj X) := by
    intro X hX b hb
    obtain ⟨a, ha, ⟨e⟩⟩ := himage b hb
    exact (centralizes_iso_right e).mp ((hX a ha).map U)
  let R := fullSubcategoryFunctor P Q U hpq
  exact (T.fullSubcategorySkeleton P).integral_of_integral_target
    (S.fullSubcategorySkeleton Q) R hI

/-- An actual natural comparison between the forgotten lift and the original
functor supplies the required tested-object image relation. -/
theorem centralizerIntegral_of_comp_iso {E : Type u''} [Category.{v''} E]
    (F : E ⥤ C) (Fhat : E ⥤ D) (e : Fhat ⋙ U ≅ F)
    (hI : S.CentralizerIntegral (Set.range F.obj)) :
    T.CentralizerIntegral (Set.range Fhat.obj) := by
  apply S.centralizerIntegral_of_braided_images T U _ _ ?_ hI
  rintro b ⟨Y, rfl⟩
  exact ⟨Fhat.obj Y, ⟨Y, rfl⟩, ⟨e.app Y⟩⟩

end Paper18.Category.FiniteSemisimpleSkeleton
