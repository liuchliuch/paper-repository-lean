import Paper18.Category.SphericalizationSection
import Paper18.Category.SphericalizationFunctorLift
import Paper18.Category.PivotalFunctorComposition

/-!
# Transporting a prescribed spherical structure into sphericalization

An actual braided tensor functor out of a category with a prescribed spherical
structure has a canonical pivotal lift into sphericalization of its target.
When the original functor is fully faithful, this is an actual fully faithful
braided spherical tensor embedding.
-/
noncomputable section
universe v u v₁ u₁ w
namespace Paper18.Category
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [BraidedCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (J : PivotalStructure C) (hJ : J.Spherical)
  {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] [RightRigidCategory D]
  [BraidedCategory D] (F : C ⥤ D) [F.Braided]

namespace Sphericalized

/-- The canonical actual embedding carrying the prescribed spherical structure. -/
def embedding : C ⥤ Sphericalized D := sectionFunctor S J hJ ⋙ mapFunctor F

instance embedding_monoidal : (embedding S J hJ F).Monoidal :=
  inferInstanceAs (sectionFunctor S J hJ ⋙ mapFunctor F).Monoidal

instance embedding_braided : (embedding S J hJ F).Braided :=
  inferInstanceAs (sectionFunctor S J hJ ⋙ mapFunctor F).Braided

instance embedding_faithful [F.Faithful] : (embedding S J hJ F).Faithful :=
  inferInstanceAs (sectionFunctor S J hJ ⋙ mapFunctor F).Faithful

instance embedding_full [F.Full] [F.Faithful] : (embedding S J hJ F).Full :=
  inferInstanceAs (sectionFunctor S J hJ ⋙ mapFunctor F).Full

/-- Forgetting the lift recovers the given actual braided tensor functor. -/
lemma embedding_comp_forget : embedding S J hJ F ⋙ forget = F := rfl

/-- The prescribed actual pivotal structure is preserved, with the canonical
chosen-dual comparison of the composite functor. -/
theorem embedding_preservesPivotal : PreservesPivotal (embedding S J hJ F)
    J (pivotalStructure (C := D)) :=
  (section_preservesPivotal S J hJ).comp (map_preservesPivotal F)

section Linear
variable [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]

instance embedding_additive [F.Additive] : (embedding S J hJ F).Additive :=
  inferInstanceAs (sectionFunctor S J hJ ⋙ mapFunctor F).Additive

instance embedding_linear [F.Linear ℂ] : (embedding S J hJ F).Linear ℂ :=
  inferInstanceAs (Functor.Linear ℂ (sectionFunctor S J hJ ⋙ mapFunctor F))

end Linear
end Sphericalized
end Paper18.Category
