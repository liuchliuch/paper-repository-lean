import Paper18.Category.PivotalFunctor
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # The actual rigid projection comparison for a strong tensor functor -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal
universe v u v' u'
namespace Paper18.Category.NondegenerateBraidedFunctor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal] {R : D ⥤ C} (adj : F ⊣ R)

/-- The actual strong tensorator as a comparison of left tensor functors. -/
def tensoratorLeftIso (X : C) :
    F ⋙ tensorLeft (F.obj X) ≅ tensorLeft X ⋙ F :=
  NatIso.ofComponents (fun Y => Functor.Monoidal.μIso F X Y)
    (fun f => Functor.LaxMonoidal.μ_natural_right F X f)

/-- The canonical mate of the tensorator followed by the actual counit. -/
def projection (X : C) (Y : D) : X ⊗ R.obj Y ⟶ R.obj (F.obj X ⊗ Y) :=
  adj.homEquiv _ _ (δ F X (R.obj Y) ≫ F.obj X ◁ adj.counit.app Y)

@[reassoc]
lemma projection_counit (X : C) (Y : D) :
    F.map (projection F adj X Y) ≫ adj.counit.app (F.obj X ⊗ Y) =
      δ F X (R.obj Y) ≫ F.obj X ◁ adj.counit.app Y :=
  (adj.homEquiv _ _).symm_apply_apply _

/-- Conjugating the tensorator on an actual dual gives an actual
isomorphism between the composite right adjoints. -/
def rigidProjectionIso (X DX : C) [ExactPairing X DX] :
    R ⋙ tensorLeft X ≅ tensorLeft (F.obj X) ⋙ R := by
  letI := mapExactPairing F X DX
  exact (conjugateIsoEquiv ((tensorLeftAdjunction X DX).comp adj)
    (adj.comp (tensorLeftAdjunction (F.obj X) (F.obj DX)))) (tensoratorLeftIso F DX)


/-- The image of the actual tensor-left evaluation is the transported
actual tensor-left evaluation. -/
lemma map_tensorLeftEvaluation (X DX Z : C) [ExactPairing X DX] :
    letI := mapExactPairing F X DX
    μ F DX (X ⊗ Z) ≫ F.map
      ((α_ DX X Z).inv ≫ (ε_ X DX ▷ Z) ≫ (λ_ Z).hom) =
    (F.obj DX ◁ δ F X Z) ≫ (α_ (F.obj DX) (F.obj X) (F.obj Z)).inv ≫
      (ε_ (F.obj X) (F.obj DX) ▷ F.obj Z) ≫ (λ_ (F.obj Z)).hom := by
  letI := mapExactPairing F X DX
  simp only [Functor.map_comp, Functor.Monoidal.map_associator_inv,
    Functor.Monoidal.map_whiskerRight, Functor.Monoidal.map_leftUnitor,
    ExactPairing.evaluation, mapExactPairing, comp_whiskerRight, Category.assoc]
  simp only [Functor.Monoidal.μ_δ_assoc, ← comp_whiskerRight_assoc]

lemma rigidProjectionIso_hom (X DX : C) [ExactPairing X DX] :
    letI := mapExactPairing F X DX
    (rigidProjectionIso F adj X DX).hom =
      conjugateEquiv ((tensorLeftAdjunction X DX).comp adj)
        (adj.comp (tensorLeftAdjunction (F.obj X) (F.obj DX)))
        (tensoratorLeftIso F DX).hom := rfl

lemma rigidProjectionIso_counit (X DX : C) [ExactPairing X DX] (Y : D) :
    letI := mapExactPairing F X DX
    F.obj DX ◁ (F.map ((rigidProjectionIso F adj X DX).hom.app Y) ≫
        adj.counit.app (F.obj X ⊗ Y)) ≫
      (α_ (F.obj DX) (F.obj X) Y).inv ≫
        (ε_ (F.obj X) (F.obj DX) ▷ Y) ≫ (λ_ Y).hom =
    μ F DX (X ⊗ R.obj Y) ≫ F.map
      ((α_ DX X (R.obj Y)).inv ≫ (ε_ X DX ▷ R.obj Y) ≫ (λ_ (R.obj Y)).hom) ≫
        adj.counit.app Y := by
  letI := mapExactPairing F X DX
  have h := conjugateEquiv_counit ((tensorLeftAdjunction X DX).comp adj)
    (adj.comp (tensorLeftAdjunction (F.obj X) (F.obj DX))) (tensoratorLeftIso F DX).hom Y
  rw [rigidProjectionIso_hom]
  simpa only [Adjunction.comp_counit_app, Functor.comp_map,
    tensorLeft, curriedTensor, tensoratorLeftIso, NatIso.ofComponents_hom_app,
    Functor.Monoidal.μIso_hom, tensorLeftAdjunction,
    Adjunction.mkOfHomEquiv_counit_app, tensorLeftHomEquiv, Equiv.symm, Equiv.coe_fn_mk, Functor.comp_obj,
    MonoidalCategory.whiskerLeft_id, Category.id_comp, Category.assoc,
    MonoidalCategory.whiskerLeft_comp] using h

/-- The canonical projection mate is the genuine rigid comparison. -/
lemma rigidProjectionIso_hom_app (X DX : C) [ExactPairing X DX] (Y : D) :
    (rigidProjectionIso F adj X DX).hom.app Y = projection F adj X Y := by
  letI := mapExactPairing F X DX
  apply (adj.homEquiv _ _).symm.injective
  change F.map ((rigidProjectionIso F adj X DX).hom.app Y) ≫
      adj.counit.app (F.obj X ⊗ Y) =
    F.map (projection F adj X Y) ≫ adj.counit.app (F.obj X ⊗ Y)
  rw [projection_counit]
  apply (tensorLeftHomEquiv (F.obj (X ⊗ R.obj Y)) (F.obj X) (F.obj DX) Y).symm.injective
  change (F.obj DX ◁ (F.map ((rigidProjectionIso F adj X DX).hom.app Y) ≫
      adj.counit.app (F.obj X ⊗ Y))) ≫ (α_ (F.obj DX) (F.obj X) Y).inv ≫
      (ε_ (F.obj X) (F.obj DX) ▷ Y) ≫ (λ_ Y).hom =
    (F.obj DX ◁ (δ F X (R.obj Y) ≫ F.obj X ◁ adj.counit.app Y)) ≫
      (α_ (F.obj DX) (F.obj X) Y).inv ≫
        (ε_ (F.obj X) (F.obj DX) ▷ Y) ≫ (λ_ Y).hom
  rw [rigidProjectionIso_counit]
  have hn : (F.obj DX ◁ (F.obj X ◁ adj.counit.app Y)) ≫
        (α_ (F.obj DX) (F.obj X) Y).inv ≫
          (ε_ (F.obj X) (F.obj DX) ▷ Y) ≫ (λ_ Y).hom =
      (α_ (F.obj DX) (F.obj X) (F.obj (R.obj Y))).inv ≫
        (ε_ (F.obj X) (F.obj DX) ▷ F.obj (R.obj Y)) ≫
          (λ_ (F.obj (R.obj Y))).hom ≫ adj.counit.app Y := by
    erw [associator_inv_naturality_right_assoc (F.obj DX) (F.obj X) (adj.counit.app Y),
      whisker_exchange_assoc (ε_ (F.obj X) (F.obj DX)) (adj.counit.app Y),
      leftUnitor_naturality (adj.counit.app Y)]
    rfl
  rw [MonoidalCategory.whiskerLeft_comp, Category.assoc, hn]
  simpa only [Category.assoc] using congrArg (fun f => f ≫ adj.counit.app Y)
    (map_tensorLeftEvaluation F X DX (R.obj Y))

/-- Rigidity proves invertibility of the actual projection formula. -/
lemma projection_isIso (X DX : C) [ExactPairing X DX] (Y : D) :
    IsIso (projection F adj X Y) := by
  rw [← rigidProjectionIso_hom_app F adj X DX Y]
  infer_instance

end Paper18.Category.NondegenerateBraidedFunctor
