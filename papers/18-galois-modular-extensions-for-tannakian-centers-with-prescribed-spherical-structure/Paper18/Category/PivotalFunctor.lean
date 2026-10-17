import Paper18.Category.PivotalTrace

/-! # Pivotal tensor functors and preservation of traces -/
noncomputable section
universe v u v₁ u₁
namespace Paper18.Category
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal
open CategoryTheory.Functor.Monoidal
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D]

private lemma mixed_associativity (F : C ⥤ D) [F.Monoidal] (X Y Z : C) :
    δ F X Y ▷ F.obj Z ≫ (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫
      F.obj X ◁ μ F Y Z = μ F (X ⊗ Y) Z ≫ F.map (α_ X Y Z).hom ≫ δ F X (Y ⊗ Z) := by
  rw [Functor.Monoidal.map_associator]
  simp only [assoc, μ_δ_assoc, μ_δ, comp_id]

private lemma mixed_associativity_inv (F : C ⥤ D) [F.Monoidal] (X Y Z : C) :
    F.obj X ◁ δ F Y Z ≫ (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv ≫
      μ F X Y ▷ F.obj Z = μ F X (Y ⊗ Z) ≫ F.map (α_ X Y Z).inv ≫ δ F (X ⊗ Y) Z := by
  rw [Functor.Monoidal.map_associator_inv]
  simp only [assoc, μ_δ_assoc, μ_δ, comp_id]

/-- Strong monoidal functors transport exact pairings. -/
def mapExactPairing (F : C ⥤ D) [F.Monoidal] (X Y : C) [ExactPairing X Y] :
    ExactPairing (F.obj X) (F.obj Y) where
  evaluation' := μ F Y X ≫ F.map (ε_ X Y) ≫ η F
  coevaluation' := ε F ≫ F.map (η_ X Y) ≫ δ F X Y
  evaluation_coevaluation' := by
    simp only [comp_whiskerRight, whiskerLeft_comp, assoc]
    rw [reassoc_of% mixed_associativity F X Y X]
    rw [Functor.LaxMonoidal.μ_natural_left_assoc,
      Functor.OplaxMonoidal.δ_natural_right_assoc]
    simp only [← F.map_comp_assoc]
    rw [ExactPairing.evaluation_coevaluation]
    simp
  coevaluation_evaluation' := by
    simp only [comp_whiskerRight, whiskerLeft_comp, assoc]
    rw [reassoc_of% mixed_associativity_inv F Y X Y]
    rw [Functor.LaxMonoidal.μ_natural_right_assoc,
      Functor.OplaxMonoidal.δ_natural_left_assoc]
    simp only [← F.map_comp_assoc]
    rw [ExactPairing.coevaluation_evaluation]
    simp

/-- The canonical isomorphism between right duals preserves evaluation. -/
lemma rightDualIso_evaluation {X Y₁ Y₂ : C} (p₁ : ExactPairing X Y₁)
    (p₂ : ExactPairing X Y₂) :
    (rightDualIso p₁ p₂).hom ▷ X ≫ @ExactPairing.evaluation _ _ _ X Y₂ p₂ =
      @ExactPairing.evaluation _ _ _ X Y₁ p₁ := by
  simpa [rightDualIso] using
    (@rightAdjointMate_comp_evaluation C _ _ X X (@HasRightDual.mk C _ _ X Y₂ p₂) (@HasRightDual.mk C _ _ X Y₁ p₁) (𝟙 X))

/-- The canonical isomorphism between right duals preserves coevaluation. -/
lemma rightDualIso_coevaluation {X Y₁ Y₂ : C} (p₁ : ExactPairing X Y₁)
    (p₂ : ExactPairing X Y₂) :
    @ExactPairing.coevaluation _ _ _ X Y₁ p₁ ≫ X ◁ (rightDualIso p₁ p₂).hom =
      @ExactPairing.coevaluation _ _ _ X Y₂ p₂ := by
  simpa [rightDualIso] using
    (@coevaluation_comp_rightAdjointMate C _ _ X X (@HasRightDual.mk C _ _ X Y₂ p₂) (@HasRightDual.mk C _ _ X Y₁ p₁) (𝟙 X))

variable [RightRigidCategory C] [RightRigidCategory D]

/-- A strong monoidal functor's canonical identification of the image of a right
 dual with the chosen right dual of the image. No preservation data are assumed. -/
def dualComparison (F : C ⥤ D) [F.Monoidal] (X : C) :
    F.obj (dual C X) ≅ dual D (F.obj X) :=
  rightDualIso (mapExactPairing F X (dual C X))
    (inferInstanceAs (ExactPairing (F.obj X) (dual D (F.obj X))))

lemma dualComparison_evaluation (F : C ⥤ D) [F.Monoidal] (X : C) :
    (dualComparison F X).hom ▷ F.obj X ≫ ε_ (F.obj X) (dual D (F.obj X)) =
      μ F (dual C X) X ≫ F.map (ε_ X (dual C X)) ≫ η F :=
  rightDualIso_evaluation _ _

lemma dualComparison_coevaluation (F : C ⥤ D) [F.Monoidal] (X : C) :
    ε F ≫ F.map (η_ X (dual C X)) ≫ δ F X (dual C X) ≫
      F.obj X ◁ (dualComparison F X).hom = η_ (F.obj X) (dual D (F.obj X)) := by
  simpa [mapExactPairing, ExactPairing.coevaluation, assoc] using
    (rightDualIso_coevaluation (mapExactPairing F X (dual C X))
      (inferInstanceAs (ExactPairing (F.obj X) (dual D (F.obj X)))))

/-- Contravariant dualization of an actual isomorphism. -/
def dualMapIso {X Y : D} (i : X ≅ Y) : dual D Y ≅ dual D X where
  hom := dualMap D i.hom
  inv := dualMap D i.inv
  hom_inv_id := by simp [dualMap, ← comp_rightAdjointMate]
  inv_hom_id := by simp [dualMap, ← comp_rightAdjointMate]

/-- The canonical identification `F(X**) ≅ F(X)**`. -/
def doubleDualComparison (F : C ⥤ D) [F.Monoidal] (X : C) :
    F.obj ((doubleDualFunctor C).obj X) ≅ (doubleDualFunctor D).obj (F.obj X) :=
  dualComparison F (dual C X) ≪≫ (dualMapIso (dualComparison F X)).symm

/-- A strong monoidal functor is pivotal when its canonical double-dual
comparison identifies the two pivotal structures. -/
def PreservesPivotal (F : C ⥤ D) [F.Monoidal]
    (JC : PivotalStructure C) (JD : PivotalStructure D) : Prop :=
  ∀ X : C, F.map (JC.j.hom.app X) ≫ (doubleDualComparison F X).hom =
    JD.j.hom.app (F.obj X)

namespace PreservesPivotal

variable {F : C ⥤ D} [F.Monoidal] {JC : PivotalStructure C} {JD : PivotalStructure D}
variable (h : PreservesPivotal F JC JD)
include h

/-- Compatibility with the pivotal left evaluation is a theorem, not extra functor data. -/
lemma leftEvaluation (X : C) :
    F.obj X ◁ (dualComparison F X).hom ≫ JD.leftEvaluation (F.obj X) =
      μ F X (dual C X) ≫ F.map (JC.leftEvaluation X) ≫ η F := by
  dsimp only [PivotalStructure.leftEvaluation]
  rw [← h X]
  dsimp only [doubleDualComparison, Iso.trans_hom, Iso.symm_hom, dualMapIso]
  simp only [comp_whiskerRight, assoc]
  rw [rightAdjointMate_comp_evaluation (dualComparison F X).inv]
  rw [whisker_exchange_assoc]
  rw [whisker_exchange_assoc]
  simp only [← whiskerLeft_comp_assoc, Iso.hom_inv_id, whiskerLeft_id, id_comp]
  rw [dualComparison_evaluation]
  have hn := Functor.LaxMonoidal.μ_natural_left F (JC.j.hom.app X) (dual C X)
  dsimp only [doubleDualFunctor] at hn
  rw [reassoc_of% hn, F.map_comp]
  simp only [assoc]

lemma inverseCompatibility (X : C) :
    (doubleDualComparison F X).inv ≫ F.map (JC.j.inv.app X) =
      JD.j.inv.app (F.obj X) := by
  have hi : F.mapIso (JC.j.app X) ≪≫ doubleDualComparison F X = JD.j.app (F.obj X) :=
    Iso.ext (h X)
  exact congrArg Iso.inv hi

/-- Compatibility with the other pivotal cup follows from the same pivotal equation. -/
lemma leftCoevaluation (X : C) :
    ε F ≫ F.map (JC.leftCoevaluation X) ≫ δ F (dual C X) X ≫
      (dualComparison F X).hom ▷ F.obj X = JD.leftCoevaluation (F.obj X) := by
  dsimp only [PivotalStructure.leftCoevaluation]
  rw [← h.inverseCompatibility X]
  dsimp only [doubleDualComparison, Iso.trans_inv, Iso.symm_inv, dualMapIso]
  simp only [whiskerLeft_comp, assoc]
  rw [coevaluation_comp_rightAdjointMate_assoc (dualComparison F X).hom]
  rw [← whisker_exchange_assoc]
  have he := whisker_exchange (dualComparison F X).hom (F.map (JC.j.inv.app X))
  dsimp only [doubleDualFunctor] at he ⊢
  rw [← he]
  have hc := dualComparison_coevaluation F (dual C X)
  have hc' : ε F ≫ F.map (η_ (dual C X) (dual C (dual C X))) ≫
      δ F (dual C X) (dual C (dual C X)) =
      η_ (F.obj (dual C X)) (dual D (F.obj (dual C X))) ≫
        F.obj (dual C X) ◁ (dualComparison F (dual C X)).inv := by
    rw [← hc]
    simp [← whiskerLeft_comp]
  rw [← reassoc_of% hc']
  have hn := Functor.OplaxMonoidal.δ_natural_right F (dual C X) (JC.j.inv.app X)
  dsimp only [doubleDualFunctor] at hn
  rw [reassoc_of% hn, F.map_comp]
  simp only [assoc, Functor.id_obj]

/-- Pivotal tensor functors preserve the actual right trace, with the unit
identification of a strong monoidal functor displayed explicitly. -/
lemma rightTrace {X : C} (f : X ⟶ X) :
    ε F ≫ F.map (JC.rightTrace f) ≫ η F = JD.rightTrace (F.map f) := by
  simp only [PivotalStructure.rightTrace, F.map_comp, assoc]
  rw [Functor.Monoidal.map_whiskerRight]
  simp only [assoc]
  rw [← h.leftEvaluation X]
  rw [← whisker_exchange_assoc]
  rw [reassoc_of% dualComparison_coevaluation F X]

/-- The left trace is preserved by the same pivotal equation. -/
lemma leftTrace {X : C} (f : X ⟶ X) :
    ε F ≫ F.map (JC.leftTrace f) ≫ η F = JD.leftTrace (F.map f) := by
  simp only [PivotalStructure.leftTrace, F.map_comp, assoc]
  rw [Functor.Monoidal.map_whiskerLeft]
  simp only [assoc]
  rw [← dualComparison_evaluation F X]
  rw [whisker_exchange_assoc]
  rw [reassoc_of% h.leftCoevaluation X]

/-- Sphericality of an ambient pivotal category restricts along a faithful
pivotal tensor functor. Fullness and braiding are not needed for this direction. -/
lemma spherical_of_faithful [F.Faithful] (hD : JD.Spherical) : JC.Spherical := by
  intro X f
  apply F.map_injective
  apply (cancel_epi (ε F)).1
  apply (cancel_mono (η F)).1
  simp only [assoc, h.leftTrace, h.rightTrace]
  exact hD (F.obj X) (F.map f)

/-- The image of a categorical dimension, using the strong monoidal unit map. -/
lemma rightDimension (X : C) :
    ε F ≫ F.map (JC.rightDimension X) ≫ η F = JD.rightDimension (F.obj X) := by
  simpa [PivotalStructure.rightDimension] using h.rightTrace (𝟙 X)

lemma leftDimension (X : C) :
    ε F ≫ F.map (JC.leftDimension X) ≫ η F = JD.leftDimension (F.obj X) := by
  simpa [PivotalStructure.leftDimension] using h.leftTrace (𝟙 X)

/-- Under a full pivotal tensor functor, source sphericality gives equality of
traces on all endomorphisms of every image object. -/
lemma spherical_on_image [F.Full] (hC : JC.Spherical) (X : C)
    (g : F.obj X ⟶ F.obj X) : JD.leftTrace g = JD.rightTrace g := by
  have hg : F.map (F.preimage g) = g := F.map_preimage g
  rw [← hg, ← h.leftTrace, ← h.rightTrace, hC X (F.preimage g)]

/-- For a fully faithful pivotal tensor functor, sphericality of the source is
exactly sphericality on all endomorphisms of the image objects. -/
lemma spherical_iff_on_image [F.Full] [F.Faithful] :
    JC.Spherical ↔ ∀ (X : C) (g : F.obj X ⟶ F.obj X), JD.leftTrace g = JD.rightTrace g := by
  constructor
  · exact h.spherical_on_image
  · intro hs X f
    apply F.map_injective
    apply (cancel_epi (ε F)).1
    apply (cancel_mono (η F)).1
    simp only [assoc, h.leftTrace, h.rightTrace]
    exact hs X (F.map f)

end PreservesPivotal

end Paper18.Category
