import Paper18.Category.CentralizerJoin
import Paper18.Category.RelativeCenterCentralizerDimension

/-! # The actual tensor functor from two full fusion subcategories -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped TensorProduct BigOperators
universe v u w
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasFiniteBiproducts C]
  (P Q : ObjectProperty C) [P.IsMonoidal] [Q.IsMonoidal]
  [IsAdditiveFullProperty P] [IsAdditiveFullProperty Q]
namespace FusionJoin

/-- Inclusion of both actual full subcategories on tensor-product Hom spaces. -/
def linearInclusion : LinearTensor P.FullSubcategory Q.FullSubcategory ⥤ LinearTensor C C where
  obj X := ⟨X.left.obj, X.right.obj⟩
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

instance : (linearInclusion P Q).Additive where
  map_add := by intros; rfl
instance : (linearInclusion P Q).Linear ℂ where
  map_smul := by intros; rfl

instance linearInclusion_monoidal : (linearInclusion P Q).Monoidal :=
  Functor.CoreMonoidal.toMonoidal {
    εIso := Iso.refl _
    μIso _ _ := Iso.refl _
    μIso_hom_natural_left := by intros; simp only [Iso.refl_hom, id_whiskerRight, whiskerLeft_id, id_comp, comp_id]; rfl
    μIso_hom_natural_right := by intros; simp only [Iso.refl_hom, id_whiskerRight, whiskerLeft_id, id_comp, comp_id]; rfl
    associativity := by intros; simp only [Iso.refl_hom, id_whiskerRight, whiskerLeft_id, id_comp, comp_id]; rfl
    left_unitality := by intros; simp only [Iso.refl_hom, id_whiskerRight, whiskerLeft_id, id_comp, comp_id]; rfl
    right_unitality := by intros; simp only [Iso.refl_hom, id_whiskerRight, whiskerLeft_id, id_comp, comp_id]; rfl }

/-- The genuine complex-linear tensor functor, lifted to the additive
Deligne product. Its pair images are the actual ambient tensor products. -/
def tensorFunctor : DeligneProduct P.FullSubcategory Q.FullSubcategory ⥤ C :=
  linearMatLift (linearInclusion P Q ⋙ Drinfeld.linearFactorization C ⋙ Center.forget C)

instance : (tensorFunctor P Q).Additive := by unfold tensorFunctor; infer_instance
instance : (tensorFunctor P Q).Linear ℂ := by unfold tensorFunctor; infer_instance
instance : (tensorFunctor P Q).Monoidal := by unfold tensorFunctor; infer_instance

/-- The singleton matrix envelope identifies the pair image with its
actual ambient tensor product. -/
def tensorPairIso (X : P.FullSubcategory) (Y : Q.FullSubcategory) :
    (tensorFunctor P Q).obj ((Mat_.embedding _).obj ⟨X,Y⟩) ≅ X.obj ⊗ Y.obj := by
  change (⨁ fun _ : PUnit => X.obj ⊗ Y.obj) ≅ _
  refine { hom := biproduct.π (fun _ : PUnit => X.obj ⊗ Y.obj) PUnit.unit
           inv := biproduct.ι (fun _ : PUnit => X.obj ⊗ Y.obj) PUnit.unit
           hom_inv_id := ?_
           inv_hom_id := by simp }
  apply biproduct.hom_ext
  intro j
  cases j
  simp

end FusionJoin
end Paper18.Category
