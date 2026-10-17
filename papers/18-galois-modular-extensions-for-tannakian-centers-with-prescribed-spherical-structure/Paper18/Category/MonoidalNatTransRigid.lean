import Paper18.Category.MonoidalNatTransRigidBasic
import Paper18.Category.PivotalFunctor
import Paper18.Category.EquivariantMonoidal

/-! # Every monoidal natural transformation out of a rigid category is invertible -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal
universe v u v' u'
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  {F H : C ⥤ D} [F.Monoidal] [H.Monoidal]
  (τ : F ⟶ H) [NatTrans.IsMonoidal τ]

/-- A monoidal transformation preserves the actual transported evaluation. -/
lemma monoidalNatTrans_image_evaluation (X Y : C) [ExactPairing X Y] :
    (τ.app Y ⊗ₘ τ.app X) ≫
        @ExactPairing.evaluation D _ _ (H.obj X) (H.obj Y) (mapExactPairing H X Y) =
      @ExactPairing.evaluation D _ _ (F.obj X) (F.obj Y) (mapExactPairing F X Y) := by
  change (τ.app Y ⊗ₘ τ.app X) ≫ μ H Y X ≫ H.map (ε_ X Y) ≫ η H =
    μ F Y X ≫ F.map (ε_ X Y) ≫ η F
  rw [← NatTrans.IsMonoidal.tensor_assoc, ← τ.naturality_assoc, monoidalNatTrans_eta]

/-- The same transformation preserves the actual transported coevaluation. -/
lemma monoidalNatTrans_image_coevaluation (X Y : C) [ExactPairing X Y] :
    @ExactPairing.coevaluation D _ _ (F.obj X) (F.obj Y) (mapExactPairing F X Y) ≫
        (τ.app X ⊗ₘ τ.app Y) =
      @ExactPairing.coevaluation D _ _ (H.obj X) (H.obj Y) (mapExactPairing H X Y) := by
  change (ε F ≫ F.map (η_ X Y) ≫ δ F X Y) ≫ (τ.app X ⊗ₘ τ.app Y) =
    ε H ≫ H.map (η_ X Y) ≫ δ H X Y
  rw [Category.assoc, Category.assoc, ← monoidalNatTrans_delta,
    τ.naturality_assoc, ← Category.assoc, NatTrans.IsMonoidal.unit]

/-- Each actual component has a cup-cap inverse constructed from the
component at the source's chosen dual. No rigid structure on the target is needed. -/
def monoidalNatTransComponentIso (X : C) : F.obj X ≅ H.obj X := by
  letI := mapExactPairing F X (dual C X)
  letI := mapExactPairing H X (dual C X)
  exact pairingMapIso (τ.app X) (τ.app (dual C X))
    (monoidalNatTrans_image_evaluation τ X (dual C X))
    (monoidalNatTrans_image_coevaluation τ X (dual C X))

@[simp] lemma monoidalNatTransComponentIso_hom (X : C) :
    (monoidalNatTransComponentIso τ X).hom = τ.app X := rfl

/-- A monoidal natural transformation between strong tensor functors
from an actual right rigid category is an actual natural isomorphism. -/
def monoidalNatTransIso : F ≅ H :=
  NatIso.ofComponents (monoidalNatTransComponentIso τ) (fun f => τ.naturality f)

@[simp] lemma monoidalNatTransIso_hom : (monoidalNatTransIso τ).hom = τ := rfl

instance monoidalNatTransIsoMonoidal : NatTrans.IsMonoidal (monoidalNatTransIso τ).hom :=
  inferInstanceAs (NatTrans.IsMonoidal τ)

end Paper18.Category
