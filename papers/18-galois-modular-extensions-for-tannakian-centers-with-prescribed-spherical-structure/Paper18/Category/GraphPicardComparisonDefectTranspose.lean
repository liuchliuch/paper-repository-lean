import Paper18.Category.GraphPicardComparisonDefectBasic
import Paper18.Category.GraphPicardTensorTransposeMonoidal

/-! # Transposing a genuine monodromy-twisted cap product -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal
universe v u v' u'
namespace Paper18.Category.GraphPicard
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [BraidedCategory C]
  {E : Type u'} [Category.{v'} E] [MonoidalCategory E]
  (F G : C ⥤ E) [F.Monoidal] [G.Monoidal]
  (e : ∀ X : C, F.obj (dual C X) ⊗ G.obj X ⟶ 𝟙_ E)
  (he : ∀ {X Y : C} (f : X ⟶ Y),
    F.map (dualMap C f) ▷ G.obj X ≫ e X =
      F.obj (dual C Y) ◁ G.map f ≫ e Y)

/-- The actual inverse-monodromy cap product transposes to the actual
positive-monodromy tensor defect. The sign follows from naturality of the
already constructed transpose, rather than being prescribed separately. -/
theorem capFamilyNatTrans_tensor_defect_of_cap_product (X Y : C)
    (hmul : F.obj (dual C (X ⊗ Y)) ◁
        (μ G X Y ≫ G.map (doubleBraiding X Y).inv) ≫ e (X ⊗ Y) =
      (F.map (dualTensorIso X Y).hom ≫ δ F (dual C Y) (dual C X)) ▷
        (G.obj X ⊗ G.obj Y) ≫ nestedCap (e X) (e Y)) :
    μ G X Y ≫ (capFamilyNatTrans F G e he).app (X ⊗ Y) =
      ((capFamilyNatTrans F G e he).app X ⊗ₘ
        (capFamilyNatTrans F G e he).app Y) ≫ μ F X Y ≫
          F.map (doubleBraiding X Y).hom := by
  let σ := capFamilyNatTrans F G e he
  have ht : F.obj (dual C (X ⊗ Y)) ◁ μ F X Y ≫
      @ExactPairing.evaluation E _ _ (F.obj (X ⊗ Y)) (F.obj (dual C (X ⊗ Y)))
        (mapExactPairing F (X ⊗ Y) (dual C (X ⊗ Y))) =
      (F.map (dualTensorIso X Y).hom ≫ δ F (dual C Y) (dual C X)) ▷
        (F.obj X ⊗ F.obj Y) ≫
      nestedCap
        (@ExactPairing.evaluation E _ _ (F.obj X) (F.obj (dual C X))
          (mapExactPairing F X (dual C X)))
        (@ExactPairing.evaluation E _ _ (F.obj Y) (F.obj (dual C Y))
          (mapExactPairing F Y (dual C Y))) := (mapped_tensor_evaluation F X Y).symm
  have hs : (μ G X Y ≫ G.map (doubleBraiding X Y).inv) ≫ σ.app (X ⊗ Y) =
      (σ.app X ⊗ₘ σ.app Y) ≫ μ F X Y := by
    letI := mapExactPairing F (X ⊗ Y) (dual C (X ⊗ Y))
    apply cap_evaluation_injective (F.obj (X ⊗ Y)) (F.obj (dual C (X ⊗ Y)))
      (G.obj X ⊗ G.obj Y)
    dsimp only [σ]
    simp only [whiskerLeft_comp, Category.assoc]
    rw [capFamilyNatTrans_evaluation, ht, whisker_exchange_assoc,
      nestedCap_naturality, capFamilyNatTrans_evaluation, capFamilyNatTrans_evaluation]
    simpa only [whiskerLeft_comp, Category.assoc] using hmul
  apply (cancel_mono (F.map (doubleBraiding X Y).inv)).mp
  simp only [Category.assoc, ← F.map_comp, Iso.hom_inv_id, F.map_id, Category.comp_id]
  rw [← σ.naturality (doubleBraiding X Y).inv]
  simpa only [σ, Category.assoc] using hs

end Paper18.Category.GraphPicard
