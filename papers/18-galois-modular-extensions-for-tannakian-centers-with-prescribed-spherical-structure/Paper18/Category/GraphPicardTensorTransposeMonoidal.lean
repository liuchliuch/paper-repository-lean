import Paper18.Category.GraphPicardTensorTransposeFunctor

/-! # Actual tensor laws obtained from actual cap multiplication -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal
universe v u v' u'
namespace Paper18.Category.GraphPicard
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  {E : Type u'} [Category.{v'} E] [MonoidalCategory E]
  (F G : C ⥤ E) [F.Monoidal] [G.Monoidal]
  (e : ∀ X : C, F.obj (dual C X) ⊗ G.obj X ⟶ 𝟙_ E)
  (he : ∀ {X Y : C} (f : X ⟶ Y),
    F.map (dualMap C f) ▷ G.obj X ≫ e X =
      F.obj (dual C Y) ◁ G.map f ≫ e Y)

/-- Actual multiplication of the cap family gives the actual tensor
condition of its rigid transpose. The hypothesis concerns the original
caps and the original functor tensorators, before transposition. -/
theorem capFamilyNatTrans_tensor_of_cap_product (X Y : C)
    (hmul : F.obj (dual C (X ⊗ Y)) ◁ μ G X Y ≫ e (X ⊗ Y) =
      (F.map (dualTensorIso X Y).hom ≫ δ F (dual C Y) (dual C X)) ▷
        (G.obj X ⊗ G.obj Y) ≫ nestedCap (e X) (e Y)) :
    μ G X Y ≫ (capFamilyNatTrans F G e he).app (X ⊗ Y) =
      ((capFamilyNatTrans F G e he).app X ⊗ₘ
        (capFamilyNatTrans F G e he).app Y) ≫ μ F X Y := by
  letI := mapExactPairing F (X ⊗ Y) (dual C (X ⊗ Y))
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
  apply cap_evaluation_injective (F.obj (X ⊗ Y)) (F.obj (dual C (X ⊗ Y)))
    (G.obj X ⊗ G.obj Y)
  simp only [whiskerLeft_comp, Category.assoc]
  rw [capFamilyNatTrans_evaluation, ht, whisker_exchange_assoc,
    nestedCap_naturality, capFamilyNatTrans_evaluation, capFamilyNatTrans_evaluation]
  exact hmul

/-- Actual normalization of the cap at the unit gives the unit law of
its transpose. The source dual-unit comparison is constructed by rigidity. -/
theorem capFamilyNatTrans_unit_of_cap_unit
    (hunit : F.obj (dual C (𝟙_ C)) ◁ ε G ≫ e (𝟙_ C) =
      (ρ_ (F.obj (dual C (𝟙_ C)))).hom ≫
        F.map (dualUnitIso (C := C)).hom ≫ η F) :
    ε G ≫ (capFamilyNatTrans F G e he).app (𝟙_ C) = ε F := by
  letI := mapExactPairing F (𝟙_ C) (dual C (𝟙_ C))
  apply cap_evaluation_injective (F.obj (𝟙_ C)) (F.obj (dual C (𝟙_ C))) (𝟙_ E)
  rw [whiskerLeft_comp, Category.assoc, capFamilyNatTrans_evaluation]
  exact hunit.trans (mapped_unit_evaluation F).symm

/-- An actual cap algebra supplies a monoidal actual transpose, through
the proved unit and multiplication diagram identities. -/
def capFamilyNatTransMonoidal
    (hunit : F.obj (dual C (𝟙_ C)) ◁ ε G ≫ e (𝟙_ C) =
      (ρ_ (F.obj (dual C (𝟙_ C)))).hom ≫
        F.map (dualUnitIso (C := C)).hom ≫ η F)
    (hmul : ∀ X Y : C, F.obj (dual C (X ⊗ Y)) ◁ μ G X Y ≫ e (X ⊗ Y) =
      (F.map (dualTensorIso X Y).hom ≫ δ F (dual C Y) (dual C X)) ▷
        (G.obj X ⊗ G.obj Y) ≫ nestedCap (e X) (e Y)) :
    NatTrans.IsMonoidal (capFamilyNatTrans F G e he) where
  unit := capFamilyNatTrans_unit_of_cap_unit F G e he hunit
  tensor X Y := capFamilyNatTrans_tensor_of_cap_product F G e he X Y (hmul X Y)

end Paper18.Category.GraphPicard
