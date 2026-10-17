import Paper18.Category.EquivariantMonoidal
import Paper18.Category.PivotalFunctor
import Paper18.Category.PivotalDuality
import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence

/-! # Actual right duals in a weak monoidal equivariantization -/

noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal
attribute [local instance 2000] RightRigidCategory.rightDual
universe v u w
namespace Paper18.Category

section Pairings
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The actual image of a pairing evaluation under a strong monoidal functor. -/
def capImage (F : C ⥤ C) [F.Monoidal] {X D : C} (e : D ⊗ X ⟶ 𝟙_ C) :
    F.obj D ⊗ F.obj X ⟶ 𝟙_ C := μ F D X ≫ F.map e ≫ η F

/-- Monoidal natural transformations preserve the actual image pairing. -/
theorem capImage_natural {F H : C ⥤ C} [F.Monoidal] [H.Monoidal]
    (τ : F ⟶ H) [NatTrans.IsMonoidal τ] {X D : C} (e : D ⊗ X ⟶ 𝟙_ C) :
    (τ.app D ⊗ₘ τ.app X) ≫ capImage H e = capImage F e := by
  unfold capImage
  rw [← NatTrans.IsMonoidal.tensor_assoc, ← τ.naturality_assoc, monoidalNatTrans_eta]

/-- Preservation of a pairing is stable under composite functors and
composite structure maps. -/
theorem capImage_comp (F H : C ⥤ C) [F.Monoidal] [H.Monoidal] {X D : C}
    (e : D ⊗ X ⟶ 𝟙_ C) (pF : F.obj D ⟶ D) (uF : F.obj X ⟶ X)
    (pH : H.obj D ⟶ D) (uH : H.obj X ⟶ X)
    (hF : (pF ⊗ₘ uF) ≫ e = capImage F e)
    (hH : (pH ⊗ₘ uH) ≫ e = capImage H e) :
    ((H.map pF ≫ pH) ⊗ₘ (H.map uF ≫ uH)) ≫ e = capImage (F ⋙ H) e := by
  rw [← tensorHom_comp_tensorHom, Category.assoc, hH]
  unfold capImage
  rw [Functor.LaxMonoidal.μ_natural_assoc]
  simp only [← Functor.map_comp_assoc]
  rw [hF]
  simp [capImage, Functor.map_comp, Category.assoc]

variable [RightRigidCategory C]

/-- Simultaneously transporting an object isomorphism and its inverse dual
preserves the actual evaluation. -/
theorem dualMapIso_tensor_evaluation {X Y : C} (e : X ≅ Y) :
    ((dualMapIso e).inv ⊗ₘ e.hom) ≫ ε_ Y (dual C Y) = ε_ X (dual C X) := by
  dsimp only [dualMapIso, dualMap]
  rw [tensorHom_def', Category.assoc, rightAdjointMate_comp_evaluation]
  simp [← whiskerLeft_comp_assoc]

/-- The corresponding identity for the actual coevaluation. -/
theorem dualMapIso_tensor_coevaluation {X Y : C} (e : X ≅ Y) :
    η_ X (dual C X) ≫ (e.hom ⊗ₘ (dualMapIso e).inv) = η_ Y (dual C Y) := by
  dsimp only [dualMapIso, dualMap]
  rw [tensorHom_def', coevaluation_comp_rightAdjointMate_assoc]
  simp

/-- A right-dual map is determined by its evaluation with any isomorphic
representative of the paired object. -/
theorem pairing_tensor_iso_ext {X T Z : C} (u : T ≅ X) {f h : Z ⟶ dual C X}
    (he : (f ⊗ₘ u.hom) ≫ ε_ X (dual C X) =
      (h ⊗ₘ u.hom) ≫ ε_ X (dual C X)) : f = h := by
  apply pairing_hom_ext (inferInstanceAs (ExactPairing X (dual C X)))
  apply (cancel_epi (Z ◁ u.hom)).mp
  simpa only [tensorHom_def', Category.assoc] using he

end Pairings

namespace WeakAction
variable {G : Type w} [Group G] {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] (A : WeakAction G C) [∀ g : G, (A.ρ g).Monoidal] [A.IsMonoidal]

namespace Equivariant

/-- The translate of the chosen dual is identified with the dual by the
canonical dual comparison and inverse dual of the object structure map. -/
def dualStructureIso (X : A.Equivariant) (g : G) : (A.ρ g).obj (dual C X.obj) ≅ dual C X.obj :=
  dualComparison (A.ρ g) X.obj ≪≫ (dualMapIso (X.structureIso g)).symm

omit [A.IsMonoidal] in
/-- The constructed dual structure preserves the actual evaluation. -/
theorem dualStructureIso_cap (X : A.Equivariant) (g : G) :
    ((dualStructureIso A X g).hom ⊗ₘ (X.structureIso g).hom) ≫
      ε_ X.obj (dual C X.obj) = capImage (A.ρ g) (ε_ X.obj (dual C X.obj)) := by
  dsimp only [dualStructureIso, Iso.trans_hom, Iso.symm_hom]
  rw [show ((dualComparison (A.ρ g) X.obj).hom ≫ (dualMapIso (X.structureIso g)).inv) ⊗ₘ
      (X.structureIso g).hom =
      ((dualComparison (A.ρ g) X.obj).hom ⊗ₘ 𝟙 _) ≫
        ((dualMapIso (X.structureIso g)).inv ⊗ₘ (X.structureIso g).hom) by
      rw [tensorHom_comp_tensorHom, Category.id_comp],
    Category.assoc, dualMapIso_tensor_evaluation, tensorHom_id]
  exact dualComparison_evaluation _ _

/-- Weak-action unitality of the constructed dual structure follows from
uniqueness of maps into the actual right dual. -/
theorem dualStructureIso_unit (X : A.Equivariant) :
    (dualStructureIso A X 1).hom = A.unitIso.hom.app (dual C X.obj) := by
  apply pairing_tensor_iso_ext (X.structureIso 1)
  rw [dualStructureIso_cap, X.unit]
  have h := capImage_natural A.unitIso.hom (ε_ X.obj (dual C X.obj))
  simpa [capImage] using h.symm

/-- Weak-action multiplicativity of the constructed dual structure follows
from actual pairing preservation and monoidality of the action comparisons. -/
theorem dualStructureIso_mul (X : A.Equivariant) (g h : G) :
    (A.ρ g).map (dualStructureIso A X h).hom ≫ (dualStructureIso A X g).hom =
      (A.mulIso g h).hom.app (dual C X.obj) ≫ (dualStructureIso A X (g * h)).hom := by
  let u : (A.ρ h ⋙ A.ρ g).obj X.obj ≅ X.obj :=
    (A.ρ g).mapIso (X.structureIso h) ≪≫ X.structureIso g
  apply pairing_tensor_iso_ext u
  change ((_ ≫ _) ⊗ₘ ((A.ρ g).map (X.structureIso h).hom ≫ (X.structureIso g).hom)) ≫ _ = _
  rw [capImage_comp (A.ρ h) (A.ρ g) _ _ _ _ _
    (dualStructureIso_cap A X h) (dualStructureIso_cap A X g)]
  change capImage (A.ρ h ⋙ A.ρ g) _ =
    ((_ ≫ _) ⊗ₘ ((A.ρ g).map (X.structureIso h).hom ≫ (X.structureIso g).hom)) ≫ _
  rw [X.mul, ← tensorHom_comp_tensorHom, Category.assoc, dualStructureIso_cap]
  exact (capImage_natural (A.mulIso g h).hom _).symm

/-- The actual right dual of an equivariant object. -/
def rightDualObj (X : A.Equivariant) : A.Equivariant where
  obj := dual C X.obj
  structureIso := dualStructureIso A X
  unit := dualStructureIso_unit A X
  mul := dualStructureIso_mul A X

/-- Evaluation is an actual equivariant morphism. -/
def rightEvaluation (X : A.Equivariant) : rightDualObj A X ⊗ X ⟶ 𝟙_ A.Equivariant where
  hom := ε_ X.obj (dual C X.obj)
  comm g := by
    change (A.ρ g).map (ε_ X.obj (dual C X.obj)) ≫ η (A.ρ g) =
      (δ (A.ρ g) (dual C X.obj) X.obj ≫
        ((dualStructureIso A X g).hom ⊗ₘ (X.structureIso g).hom)) ≫ _
    rw [Category.assoc, dualStructureIso_cap]
    simp [capImage]

omit [A.IsMonoidal] in
/-- The constructed dual structure also preserves the coevaluation. -/
theorem dualStructureIso_cup (X : A.Equivariant) (g : G) :
    ε (A.ρ g) ≫ (A.ρ g).map (η_ X.obj (dual C X.obj)) ≫
      δ (A.ρ g) X.obj (dual C X.obj) ≫
        ((X.structureIso g).hom ⊗ₘ (dualStructureIso A X g).hom) =
          η_ X.obj (dual C X.obj) := by
  dsimp only [dualStructureIso, Iso.trans_hom, Iso.symm_hom]
  rw [show (X.structureIso g).hom ⊗ₘ
      ((dualComparison (A.ρ g) X.obj).hom ≫ (dualMapIso (X.structureIso g)).inv) =
      (𝟙 _ ⊗ₘ (dualComparison (A.ρ g) X.obj).hom) ≫
        ((X.structureIso g).hom ⊗ₘ (dualMapIso (X.structureIso g)).inv) by
      rw [tensorHom_comp_tensorHom, Category.id_comp]]
  have hc := dualComparison_coevaluation (A.ρ g) X.obj =≫
    ((X.structureIso g).hom ⊗ₘ (dualMapIso (X.structureIso g)).inv)
  rw [dualMapIso_tensor_coevaluation] at hc
  simpa only [Category.assoc, id_tensorHom] using hc

/-- Coevaluation is an actual equivariant morphism. -/
def rightCoevaluation (X : A.Equivariant) : 𝟙_ A.Equivariant ⟶ X ⊗ rightDualObj A X where
  hom := η_ X.obj (dual C X.obj)
  comm g := by
    change (A.ρ g).map (η_ X.obj (dual C X.obj)) ≫
      (δ (A.ρ g) X.obj (dual C X.obj) ≫
        ((X.structureIso g).hom ⊗ₘ (dualStructureIso A X g).hom)) =
      η (A.ρ g) ≫ η_ X.obj (dual C X.obj)
    apply (cancel_epi (ε (A.ρ g))).mp
    simpa [Category.assoc] using dualStructureIso_cup A X g

/-- The dual evaluation and coevaluation satisfy the triangle equations
because their actual underlying maps do. -/
def rightExactPairing (X : A.Equivariant) : ExactPairing X (rightDualObj A X) := by
  letI : ExactPairing (A.forget.obj X) (A.forget.obj (rightDualObj A X)) := by
    change ExactPairing X.obj (dual C X.obj)
    infer_instance
  apply exactPairingOfFaithful A.forget (rightEvaluation A X) (rightCoevaluation A X)
  · simp only [forget_δ, forget_ε]
    erw [Category.id_comp, Category.comp_id]
    rfl
  · simp only [forget_η, forget_μ]
    erw [Category.id_comp, Category.comp_id]
    rfl

instance equivariant_rightRigidCategory : RightRigidCategory A.Equivariant where
  rightDual X :=
    { rightDual := rightDualObj A X
      exact := rightExactPairing A X }

end Equivariant
end WeakAction
end Paper18.Category
