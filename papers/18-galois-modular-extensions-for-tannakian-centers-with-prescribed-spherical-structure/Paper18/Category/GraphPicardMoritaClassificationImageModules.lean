import Paper18.Category.GraphPicardMoritaImageSemisimple

/-! # Recovering the actual target from its dominant central monad

If an actual tensor functor is essentially surjective, its genuine
summand image is the whole target. Composing that actual equivalence
with the proved Beck and rigid-projection comparisons recovers the
target as the genuine category of right modules over its adjoint unit.
This statement concerns the target category, not a classification of
the original module category.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj
universe v u w u' w'
namespace Paper18.Category.GraphPicard.MoritaImage
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasFiniteBiproducts C]
  {D : Type u'} [Category.{v} D] [Preadditive D] [Linear ℂ D]
  [HasFiniteBiproducts D]
  (F : C ⥤ D) [F.Additive] [F.Linear ℂ] [F.EssSurj]

omit [Preadditive C] [Linear ℂ C] [HasFiniteBiproducts C]
  [Preadditive D] [Linear ℂ D] [HasFiniteBiproducts D]
  [F.Additive] [F.Linear ℂ] in
/-- Actual essential surjectivity supplies an actual image retract for
every actual target object. -/
theorem property_of_essSurj (Y : D) : property F Y :=
  ⟨F.objPreimage Y, ⟨Retract.ofIso (F.objObjPreimageIso Y).symm⟩⟩

/-- The inclusion of actual image summands is essentially surjective
when the original actual functor is essentially surjective. -/
def inclusionEssSurj : (property F).ι.EssSurj where
  mem_essImage Y := ⟨⟨Y, property_of_essSurj F Y⟩, ⟨Iso.refl Y⟩⟩

/-- The whole target is genuinely equivalent to the actual summand
image; the forward functor is the original full inclusion. -/
def inclusionEquivalence : Image F ≌ D := by
  letI := inclusionEssSurj F
  letI : (property F).ι.IsEquivalence := {}
  exact (property F).ι.asEquivalence

instance inclusionEquivalence_additive : (inclusionEquivalence F).functor.Additive :=
  inferInstanceAs ((property F).ι.Additive)
instance inclusionEquivalence_linear : (inclusionEquivalence F).functor.Linear ℂ :=
  inferInstanceAs ((property F).ι.Linear ℂ)
instance inclusionEquivalence_inverse_additive : (inclusionEquivalence F).inverse.Additive :=
  Equivalence.inverse_additive (inclusionEquivalence F)
instance inclusionEquivalence_inverse_linear : (inclusionEquivalence F).inverse.Linear ℂ :=
  Equivalence.inverseLinear ℂ (inclusionEquivalence F)

variable [HasKernels C] [MonoidalCategory C] [MonoidalPreadditive C]
  [MonoidalLinear ℂ C] [RightRigidCategory C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [HasKernels D] [MonoidalCategory D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  [F.Monoidal] {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)

/-- Actual monadic recovery of the whole target from the actual
right-adjoint unit, with the genuine right-module orientation. -/
def wholeModuleEquivalence : D ≌
    Mod_ Cᴹᵒᵖ (mop (DiagonalAlgebra.semisimpleAdjointAlgebra S F)) :=
  (inclusionEquivalence F).symm.trans (moduleEquivalence S F T)

instance wholeModuleEquivalence_additive : (wholeModuleEquivalence F S T).functor.Additive := by
  change ((inclusionEquivalence F).inverse ⋙ (moduleEquivalence S F T).functor).Additive
  infer_instance
instance wholeModuleEquivalence_linear : (wholeModuleEquivalence F S T).functor.Linear ℂ := by
  change ((inclusionEquivalence F).inverse ⋙ (moduleEquivalence S F T).functor).Linear ℂ
  infer_instance
instance wholeModuleEquivalence_inverse_additive :
    (wholeModuleEquivalence F S T).inverse.Additive :=
  Equivalence.inverse_additive (wholeModuleEquivalence F S T)
instance wholeModuleEquivalence_inverse_linear :
    (wholeModuleEquivalence F S T).inverse.Linear ℂ :=
  Equivalence.inverseLinear ℂ (wholeModuleEquivalence F S T)

end Paper18.Category.GraphPicard.MoritaImage
