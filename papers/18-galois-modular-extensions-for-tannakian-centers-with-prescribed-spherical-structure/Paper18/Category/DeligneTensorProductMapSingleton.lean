import Paper18.Category.DeligneTensorProductMapMat
import Paper18.Category.LinearMatLiftFullyFaithful

/-! # The singleton identification of an actual monoidal additive lift -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open CategoryTheory.Functor.LaxMonoidal
universe v u v' u'
namespace Paper18.Category.DeligneTensorProductMap
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [HasFiniteBiproducts D] (F : C ⥤ D) [F.Additive] [F.Linear ℂ] [F.Monoidal]

@[reassoc (attr := simp)] lemma ι_singletonIso (X : C) :
    biproduct.ι (fun _ : PUnit => F.obj X) PUnit.unit ≫
      (linearMatLiftSingletonIso F X).hom = 𝟙 _ := by
  simp [linearMatLiftSingletonIso, biproductUniqueIso, limitBiconeOfUnique]

@[reassoc] lemma lift_embedding_tensor_generator (X Y : C) :
    biproduct.ι (fun _ : PUnit × PUnit => F.obj (X ⊗ Y)) (PUnit.unit,PUnit.unit) ≫
      (linearMatLift F).map (μ (Mat_.embedding C) X Y) =
        biproduct.ι (fun _ : PUnit => F.obj (X ⊗ Y)) PUnit.unit := by
  have h := LinearMat.lift_ι_map F (μ (Mat_.embedding C) X Y) (PUnit.unit,PUnit.unit)
  change biproduct.ι (fun _ : PUnit × PUnit => F.obj (X ⊗ Y)) (PUnit.unit,PUnit.unit) ≫
      (linearMatLift F).map (μ (Mat_.embedding C) X Y) =
    ∑ j : PUnit, F.map (𝟙 (X ⊗ Y)) ≫ biproduct.ι (fun _ : PUnit => F.obj (X ⊗ Y)) j at h
  simpa using h

/-- The actual singleton comparison preserves the actual tensorator and
unit of the finite-biproduct lift. -/
instance linearMatLiftEmbeddingIso_monoidal :
    NatTrans.IsMonoidal (linearMatLiftEmbeddingIso F).hom where
  unit := by
    dsimp only [Functor.LaxMonoidal.comp_ε, linearMatLiftEmbeddingIso,
      NatIso.ofComponents_hom_app, Functor.comp_obj]
    have he : ε (Mat_.embedding C) = 𝟙 (𝟙_ (Mat_ C)) := rfl
    rw [he, (linearMatLift F).map_id, Category.comp_id]
    change (LinearMat.liftUnitIso F).hom ≫ (linearMatLiftSingletonIso F (𝟙_ C)).hom = ε F
    rw [LinearMat.liftUnitIso_hom, Category.assoc, ι_singletonIso, Category.comp_id]
  tensor X Y := by
    dsimp only [Functor.LaxMonoidal.comp_μ, linearMatLiftEmbeddingIso,
      NatIso.ofComponents_hom_app, Functor.comp_obj]
    simp only [Category.assoc]
    apply LinearMat.tensorBiproduct_hom_ext
    rintro ⟨⟩ ⟨⟩
    erw [LinearMat.tensor_ι_liftTensorIso_assoc]
    dsimp only [Mat_.embedding_obj_X]
    erw [lift_embedding_tensor_generator_assoc F X Y]
    rw [ι_singletonIso, Category.comp_id]
    rw [← Category.assoc, tensorHom_comp_tensorHom]
    erw [ι_singletonIso F X, ι_singletonIso F Y]
    simp

end Paper18.Category.DeligneTensorProductMap
