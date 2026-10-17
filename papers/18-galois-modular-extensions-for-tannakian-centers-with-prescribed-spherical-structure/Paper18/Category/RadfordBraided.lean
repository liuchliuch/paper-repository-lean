import Paper18.Category.RigidDoubleDual
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-!
# The actual Drinfeld comparison and the braided four-dual map

The Drinfeld natural isomorphism is constructed from the canonical comparison
between the swapped braided exact pairing and the chosen right dual pairing.
This does not assume a pivotal structure. The four-dual comparison is introduced
separately from any assertion of the fusion-category Radford trace theorem.
-/
noncomputable section
universe v u
namespace Paper18.Category
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C]

/-- Drinfeld's canonical comparison `X ≅ X**`, from the braided swapped pairing. -/
def drinfeldIso (X : C) : X ≅ (doubleDualFunctor C).obj X :=
  rightDualIso (BraidedCategory.exactPairing_swap X (dual C X))
    (inferInstanceAs (ExactPairing (dual C X) (dual C (dual C X))))

lemma drinfeldIso_evaluation (X : C) :
    (drinfeldIso X).hom ▷ dual C X ≫ ε_ (dual C X) (dual C (dual C X)) =
      (β_ X (dual C X)).hom ≫ ε_ X (dual C X) :=
  rightDualIso_evaluation _ _

lemma drinfeldIso_coevaluation (X : C) :
    η_ X (dual C X) ≫ (β_ (dual C X) X).inv ≫ dual C X ◁ (drinfeldIso X).hom =
      η_ (dual C X) (dual C (dual C X)) := by
  simpa only [BraidedCategory.exactPairing_swap, ExactPairing.coevaluation, assoc] using
    rightDualIso_coevaluation (BraidedCategory.exactPairing_swap X (dual C X))
      (inferInstanceAs (ExactPairing (dual C X) (dual C (dual C X))))

lemma drinfeldIso_naturality {X Y : C} (f : X ⟶ Y) :
    f ≫ (drinfeldIso Y).hom = (drinfeldIso X).hom ≫ (doubleDualFunctor C).map f := by
  apply pairing_hom_ext (inferInstanceAs (ExactPairing (dual C Y) (dual C (dual C Y))))
  simp only [comp_whiskerRight, assoc]
  rw [drinfeldIso_evaluation]
  have he := rightAdjointMate_comp_evaluation (dualMap C f)
  dsimp only [doubleDualFunctor, dualMap, dual] at he ⊢
  rw [he, ← whisker_exchange_assoc, drinfeldIso_evaluation]
  rw [braiding_naturality_right_assoc, rightAdjointMate_comp_evaluation]
  rw [braiding_naturality_left_assoc]

/-- The actual Drinfeld natural isomorphism, without monoidality assumptions. -/
def drinfeldNatIso : 𝟭 C ≅ doubleDualFunctor C :=
  NatIso.ofComponents drinfeldIso (fun f => drinfeldIso_naturality f)

/-- The canonical four-dual comparison available from the braiding and rigidity. -/
def braidedFourDualIso (X : C) :
    X ≅ (doubleDualFunctor C ⋙ doubleDualFunctor C).obj X :=
  drinfeldIso X ≪≫ (dualMapIso (drinfeldIso (dual C X))).symm

/-- Dualized Drinfeld comparison, with its two contravariances cancelled. -/
def dualDrinfeldNatIso :
    (doubleDualFunctor C ⋙ doubleDualFunctor C) ≅ doubleDualFunctor C :=
  NatIso.ofComponents (fun X => dualMapIso (drinfeldIso (dual C X))) (fun f => by
    have hn := drinfeldIso_naturality (dualMap C f)
    have hd := congrArg (dualMap C) hn
    dsimp only [doubleDualFunctor, dualMap, Functor.comp_map] at hd ⊢
    simp only [comp_rightAdjointMate] at hd
    exact hd.symm)

/-- The braided four-dual comparison as an actual natural isomorphism. -/
def braidedFourDualNatIso : 𝟭 C ≅ (doubleDualFunctor C ⋙ doubleDualFunctor C) :=
  drinfeldNatIso ≪≫ (dualDrinfeldNatIso (C := C)).symm

@[simp] lemma braidedFourDualNatIso_app (X : C) :
    (braidedFourDualNatIso (C := C)).app X = braidedFourDualIso X := rfl

end Paper18.Category
