import Paper18.Category.DrinfeldInduction
import Paper18.Category.DrinfeldLinear

/-! # Actual functoriality of central induction -/
noncomputable section
universe v u w
namespace Paper18.Category.Drinfeld
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
attribute [local instance 2000] RightRigidCategory.rightDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

lemma inductionMapComponents_dinatural {X Y T V : C} (f : X ⟶ Y) (g : T ⟶ V) :
    ((T ⊗ X) ◁ dualMap C g) ≫ ((T ◁ f) ▷ dual C T) ≫ inductionι S Y T =
      ((g ▷ X) ▷ dual C V) ≫ ((V ◁ f) ▷ dual C V) ≫ inductionι S Y V := by
  rw [whisker_exchange_assoc, inductionι_dinatural]
  rw [← comp_whiskerRight_assoc, whisker_exchange]
  rw [comp_whiskerRight_assoc]

/-- The actual coend map induced by a morphism in the middle strand. -/
def inductionUnderlyingMap {X Y : C} (f : X ⟶ Y) :
    inductionUnderlying S X ⟶ inductionUnderlying S Y :=
  letI := inductionHasCoend S X
  coend.desc (fun T => ((T ◁ f) ▷ dual C T) ≫ inductionι S Y T)
    (fun _ _ g => inductionMapComponents_dinatural S f g)

@[reassoc (attr := simp)]
lemma inductionUnderlyingMap_ι {X Y : C} (f : X ⟶ Y) (T : C) :
    inductionι S X T ≫ inductionUnderlyingMap S f =
      ((T ◁ f) ▷ dual C T) ≫ inductionι S Y T := by
  letI := inductionHasCoend S X
  exact coend.ι_desc _ _ T

@[simp] lemma inductionUnderlyingMap_id (X : C) :
    inductionUnderlyingMap S (𝟙 X) = 𝟙 (inductionUnderlying S X) := by
  letI := inductionHasCoend S X
  apply coend.hom_ext
  intro T
  change inductionι S X T ≫ _ = inductionι S X T ≫ _
  simp only [inductionUnderlyingMap_ι, whiskerLeft_id, id_whiskerRight, id_comp, comp_id]

@[simp] lemma inductionUnderlyingMap_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    inductionUnderlyingMap S (f ≫ g) = inductionUnderlyingMap S f ≫ inductionUnderlyingMap S g := by
  letI := inductionHasCoend S X
  apply coend.hom_ext
  intro T
  change inductionι S X T ≫ _ = inductionι S X T ≫ _
  simp only [inductionUnderlyingMap_ι, inductionUnderlyingMap_ι_assoc, whiskerLeft_comp,
    comp_whiskerRight, assoc]

lemma inductionBraidingTail_map {X Y : C} (f : X ⟶ Y) (U T : C) :
    inductionBraidingTail S X U T ≫ inductionUnderlyingMap S f =
      ((dual C U ◁ ((T ◁ f) ▷ dual C T)) ▷ dual C (dual C U)) ≫
        inductionBraidingTail S Y U T := by
  calc
    _ = 𝟙 ((dual C U ⊗ ((T ⊗ X) ⊗ dual C T)) ⊗ dual C (dual C U)) ⊗≫
        ((((dual C U ⊗ T) ⊗ X) ◁ (dualTensorIso (dual C U) T).inv) ≫
          (((dual C U ⊗ T) ◁ f) ▷ dual C (dual C U ⊗ T))) ⊗≫
        inductionι S Y (dual C U ⊗ T) := by
      dsimp only [inductionBraidingTail]
      simp only [monoidalComp, assoc, id_comp]
      rw [inductionUnderlyingMap_ι]
      monoidal
    _ = _ := by
      rw [whisker_exchange]
      dsimp only [inductionBraidingTail]
      monoidal

lemma inductionHalfBraidingComponent_map (J : PivotalStructure C)
    {X Y : C} (f : X ⟶ Y) (U T : C) :
    (((T ◁ f) ▷ dual C T) ▷ U) ≫ inductionHalfBraidingComponent S J Y U T =
      inductionHalfBraidingComponent S J X U T ≫ U ◁ inductionUnderlyingMap S f := by
  dsimp only [inductionHalfBraidingComponent]
  rw [← assoc, rigidInsertion_naturality, assoc, ← whiskerLeft_comp,
    ← inductionBraidingTail_map, whiskerLeft_comp, assoc]

lemma inductionUnderlyingMap_central (J : PivotalStructure C)
    {X Y : C} (f : X ⟶ Y) (U : C) :
    (inductionUnderlyingMap S f ▷ U) ≫ inductionHalfBraidingHom S J Y U =
      inductionHalfBraidingHom S J X U ≫ U ◁ inductionUnderlyingMap S f := by
  letI := inductionHasCoend S X
  apply mappedCoend_hom_ext (inductionDiagram X) (tensorRight U)
  intro T
  change (inductionι S X T ▷ U) ≫ _ = (inductionι S X T ▷ U) ≫ _
  rw [← comp_whiskerRight_assoc, inductionUnderlyingMap_ι, comp_whiskerRight_assoc,
    inductionHalfBraidingHom_ι, inductionHalfBraidingHom_ι_assoc,
    inductionHalfBraidingComponent_map]

/-- Central induction as an actual functor into the actual Drinfeld center. -/
def inductionFunctor (J : PivotalStructure C) : C ⥤ Center C where
  obj := inductionObj S J
  map f := { f := inductionUnderlyingMap S f, comm := inductionUnderlyingMap_central S J f }
  map_id X := by ext; exact inductionUnderlyingMap_id S X
  map_comp f g := by ext; exact inductionUnderlyingMap_comp S f g

@[simp] lemma inductionFunctor_obj (J : PivotalStructure C) (X : C) :
    (inductionFunctor S J).obj X = inductionObj S J X := rfl

@[simp] lemma inductionFunctor_map_f (J : PivotalStructure C) {X Y : C} (f : X ⟶ Y) :
    ((inductionFunctor S J).map f).f = inductionUnderlyingMap S f := rfl

lemma inductionUnderlyingMap_add {X Y : C} (f g : X ⟶ Y) :
    inductionUnderlyingMap S (f + g) = inductionUnderlyingMap S f + inductionUnderlyingMap S g := by
  letI := inductionHasCoend S X
  apply coend.hom_ext
  intro T
  change inductionι S X T ≫ _ = inductionι S X T ≫ _
  simp only [inductionUnderlyingMap_ι, Preadditive.comp_add, Preadditive.add_comp,
    MonoidalPreadditive.whiskerLeft_add, MonoidalPreadditive.add_whiskerRight]

lemma inductionUnderlyingMap_smul {X Y : C} (c : ℂ) (f : X ⟶ Y) :
    inductionUnderlyingMap S (c • f) = c • inductionUnderlyingMap S f := by
  letI := inductionHasCoend S X
  apply coend.hom_ext
  intro T
  change inductionι S X T ≫ _ = inductionι S X T ≫ _
  simp only [inductionUnderlyingMap_ι, Linear.comp_smul, Linear.smul_comp,
    MonoidalLinear.whiskerLeft_smul, MonoidalLinear.smul_whiskerRight]

instance inductionFunctor_additive (J : PivotalStructure C) : (inductionFunctor S J).Additive where
  map_add {X Y} f g := by ext; exact inductionUnderlyingMap_add S f g

instance inductionFunctor_linear (J : PivotalStructure C) : (inductionFunctor S J).Linear ℂ where
  map_smul := by intro X Y f c; ext; exact inductionUnderlyingMap_smul S c f

end Paper18.Category.Drinfeld
