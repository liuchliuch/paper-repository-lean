import Paper18.Category.RelativeTensorCentralImage
import Paper18.Category.CentralizerDimensionBasic
import Paper18.Category.FunctorImage

/-! # Actual intrinsic dimensions of fully faithful tensor images -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u v' u' w w'
namespace Paper18.Category.RelativeTensor
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

section ImageFunctor
variable [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal]

instance toEssImageMonoidal : F.toEssImage.Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := F.essImage.isoMk (Functor.Monoidal.εIso F)
      μIso X Y := F.essImage.isoMk (Functor.Monoidal.μIso F X Y)
      μIso_hom_natural_left := fun f Y => Functor.LaxMonoidal.μ_natural_left F f Y
      μIso_hom_natural_right := fun X f => Functor.LaxMonoidal.μ_natural_right F X f
      associativity X Y Z := Functor.LaxMonoidal.associativity F X Y Z
      left_unitality X := Functor.LaxMonoidal.left_unitality F X
      right_unitality X := Functor.LaxMonoidal.right_unitality F X }

instance toEssImageIsEquivalence [F.Full] [F.Faithful] : F.toEssImage.IsEquivalence where

variable [Preadditive C] [Preadditive D]
instance toEssImageAdditive [F.Additive] : F.toEssImage.Additive where
  map_add := by intros; exact F.map_add

instance toEssImageLinear [Linear ℂ C] [Linear ℂ D] [F.Linear ℂ] : F.toEssImage.Linear ℂ where
  map_smul f r := F.map_smul r f
end ImageFunctor

section Fusion
variable [Preadditive C] [Linear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  [Preadditive D] [Linear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [RightRigidCategory D] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)
  (F : C ⥤ D) [F.Monoidal] [F.Additive] [F.Linear ℂ] [F.Full] [F.Faithful]

/-- An actual tensor equivalence identifies the intrinsic total FP
dimensions computed from any actual finite semisimple skeletons. -/
theorem totalFPdim_eq_of_equivalence [F.IsEquivalence] :
    S.fusionBasis.totalFPdim = T.fusionBasis.totalFPdim := by
  let E := F.asEquivalence
  letI : E.functor.Monoidal := inferInstanceAs F.Monoidal
  letI : E.functor.Additive := inferInstanceAs F.Additive
  letI : E.functor.Linear ℂ := inferInstanceAs (F.Linear ℂ)
  letI := E.inverseMonoidal
  exact le_antisymm (S.totalFPdim_le_of_fullyFaithful T F)
    (T.totalFPdim_le_of_fullyFaithful S E.inverse)

/-- The support dimension of an actual fully faithful tensor image is the
intrinsic total FP dimension of its actual source. -/
theorem supportFPdim_essImage :
    T.supportFPdim F.essImage = S.fusionBasis.totalFPdim := by
  letI := T.fullSubcategoryHasKernels F.essImage
  letI := T.fullSubcategoryRightRigid F.essImage
  letI := T.fullSubcategorySimpleUnit F.essImage
  rw [← T.fullSubcategory_totalFPdim_eq F.essImage]
  exact (totalFPdim_eq_of_equivalence S (T.fullSubcategorySkeleton F.essImage) F.toEssImage).symm
end Fusion
end Paper18.Category.RelativeTensor
