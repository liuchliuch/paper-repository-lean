import Paper18.Category.RadfordBraided
import Paper18.Category.PivotalBalancingTensor

/-! # Double-dual and dual compatibility of the braided four-dual comparison -/
noncomputable section
universe v u
namespace Paper18.Category
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory
open Functor.LaxMonoidal Functor.Monoidal
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C]

/-- A natural comparison from the identity to double dual commutes with its
own double dual. -/
lemma drinfeldIso_doubleDual (X : C) :
    (drinfeldIso ((doubleDualFunctor C).obj X)).hom =
      (doubleDualFunctor C).map (drinfeldIso X).hom := by
  apply (cancel_epi (drinfeldIso X).hom).mp
  exact drinfeldIso_naturality (drinfeldIso X).hom

lemma drinfeldIso_doubleDual_inv (X : C) :
    (drinfeldIso ((doubleDualFunctor C).obj X)).inv =
      (doubleDualFunctor C).map (drinfeldIso X).inv := by
  have hi : drinfeldIso ((doubleDualFunctor C).obj X) =
      (doubleDualFunctor C).mapIso (drinfeldIso X) :=
    Iso.ext (drinfeldIso_doubleDual X)
  exact congrArg Iso.inv hi

/-- The braided four-dual comparison is compatible with the chosen right
dual: dualizing it reverses its direction. -/
lemma braidedFourDualIso_dual (X : C) :
    (braidedFourDualIso (dual C X)).hom =
      (dualMapIso (braidedFourDualIso X)).inv := by
  have hn := drinfeldIso_naturality (dualMap C (drinfeldIso X).hom)
  have hdX := drinfeldIso_doubleDual_inv X
  have hdD := drinfeldIso_doubleDual (dual C X)
  dsimp only [braidedFourDualIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, dualMapIso]
  simp only [dualMap, comp_rightAdjointMate]
  apply (cancel_epi (dualMapIso (drinfeldIso X)).hom).mp
  dsimp only [dualMapIso, dualMap] at hn ⊢
  dsimp only [doubleDualFunctor, dualMap, dual] at hdX hdD hn ⊢
  rw [← assoc, hn, assoc, hdD, hdX]
  simp only [← comp_rightAdjointMate, Iso.inv_hom_id, Iso.hom_inv_id, rightAdjointMate_id,
    comp_id, id_comp]
  simp only [assoc, Iso.inv_hom_id, comp_id]

/-- The four-dual comparison commutes with canonical double dualization. -/
lemma braidedFourDualIso_doubleDual (X : C) :
    (braidedFourDualIso ((doubleDualFunctor C).obj X)).hom =
      (doubleDualFunctor C).map (braidedFourDualIso X).hom := by
  have hdX := drinfeldIso_doubleDual X
  have hdD := drinfeldIso_doubleDual_inv (dual C X)
  dsimp only [braidedFourDualIso, Iso.trans_hom, Iso.symm_hom, dualMapIso]
  rw [Functor.map_comp, hdX]
  dsimp only [doubleDualFunctor, dualMap, dual] at hdD ⊢
  rw [hdD]

/-- Canonical double dualization preserves the actual braiding. Its
braidedness is derived from the Drinfeld tensor formula and naturality. -/
instance canonicalDoubleDualBraided : (doubleDualFunctor C).Braided where
  toMonoidal := canonicalDoubleDualMonoidal
  braided X Y := by
    apply (cancel_epi ((drinfeldIso X) ⊗ᵢ (drinfeldIso Y)).hom).mp
    change ((drinfeldIso X).hom ⊗ₘ (drinfeldIso Y).hom) ≫ _ =
      ((drinfeldIso X).hom ⊗ₘ (drinfeldIso Y).hom) ≫ _
    rw [canonicalDoubleDual_tensor, ← assoc, ← drinfeldIso_tensor, assoc,
      ← drinfeldIso_naturality]
    have hm : (doubleBraiding X Y).hom ≫ (β_ X Y).hom =
        (β_ X Y).hom ≫ (doubleBraiding Y X).hom := by
      simp only [doubleBraiding, Iso.trans_hom, assoc]
    rw [← assoc, hm, assoc, drinfeldIso_tensor]
    rw [braiding_naturality_assoc, canonicalDoubleDual_tensor]

end Paper18.Category
