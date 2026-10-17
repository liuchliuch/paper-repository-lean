import Paper18.Category.RadfordBraided
import Paper18.Category.SphericalizationRigid

/-!
# The trace characterization of the braided four-dual comparison

The four-dual map constructed from Drinfeld's comparison satisfies the actual
cap/cup trace identity. In particular, the Radford square condition implies
equality of left and right traces of every ambient endomorphism. No dimension
or sphericality assertion is assumed.
-/
noncomputable section
universe v u
namespace Paper18.Category
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C]

lemma drinfeldIso_inverse_evaluation (X : C) :
    ε_ X (dual C X) = (β_ X (dual C X)).inv ≫
      (drinfeldIso X).hom ▷ dual C X ≫ ε_ (dual C X) (dual C (dual C X)) := by
  rw [drinfeldIso_evaluation, Iso.inv_hom_id_assoc]

lemma drinfeldIso_dual_inverse_coevaluation (X : C) :
    η_ (dual C X) (dual C (dual C X)) ≫
      (β_ (dual C (dual C X)) (dual C X)).inv =
        η_ (dual C (dual C X)) (dual C (dual C (dual C X))) ≫
          dual C (dual C X) ◁ (drinfeldIso (dual C X)).inv := by
  rw [← drinfeldIso_coevaluation (dual C X)]
  simp only [assoc, ← whiskerLeft_comp, Iso.hom_inv_id, whiskerLeft_id, comp_id]

/-- The left cap/cup trace of an arbitrary identification `phi` is the right
trace for its canonical Radford conjugate. This is an equality in `End(1)`. -/
theorem braidedFourDual_trace (X : C) (phi : X ≅ (doubleDualFunctor C).obj X)
    (f : X ⟶ X) :
    η_ (dual C X) (dual C (dual C X)) ≫ dual C X ◁ phi.inv ≫
      dual C X ◁ f ≫ ε_ X (dual C X) =
        η_ X (dual C X) ≫ f ▷ dual C X ≫
          ((braidedFourDualIso X).hom ≫ (doubleDualFunctor C).map phi.inv) ▷ dual C X ≫
            ε_ (dual C X) (dual C (dual C X)) := by
  let s : dual C (dual C X) ⟶ dual C (dual C X) :=
    phi.inv ≫ f ≫ (drinfeldIso X).hom
  have hc := pivotalized_iso_coevaluation phi
  dsimp only [doubleDualFunctor, dualMapIso] at hc
  have he := rightAdjointMate_comp_evaluation (drinfeldIso (dual C X)).inv
  have hf := rightAdjointMate_comp_evaluation (dualMap C phi.inv)
  dsimp only [doubleDualFunctor, dualMap, dual] at he hf ⊢
  calc
    _ = η_ (dual C X) (dual C (dual C X)) ≫ (β_ (dual C (dual C X)) (dual C X)).inv ≫ s ▷ (dual C X) ≫ ε_ (dual C X) (dual C (dual C X)) := by
      rw [drinfeldIso_inverse_evaluation]
      simp only [assoc, ← whiskerLeft_comp_assoc, braiding_inv_naturality_right_assoc,
        comp_whiskerRight, s]
    _ = η_ (dual C (dual C X)) (dual C (dual C (dual C X))) ≫ s ▷ (dual C (dual C (dual C X))) ≫
        (rightAdjointMate (drinfeldIso (dual C X)).inv) ▷ (dual C (dual C (dual C X))) ≫ ε_ (dual C (dual C (dual C X))) (dual C (dual C (dual C (dual C X)))) := by
      rw [← assoc, ← assoc, drinfeldIso_dual_inverse_coevaluation]
      rw [assoc, assoc, whisker_exchange_assoc, ← he]
    _ = η_ X (dual C X) ≫ phi.hom ▷ (dual C X) ≫
        (s ≫ rightAdjointMate (drinfeldIso (dual C X)).inv ≫
          rightAdjointMate (rightAdjointMate phi.inv)) ▷ (dual C X) ≫ ε_ (dual C X) (dual C (dual C X)) := by
      rw [← hc]
      simp only [tensorHom_def, assoc]
      rw [whisker_exchange_assoc, whisker_exchange_assoc]
      dsimp only [doubleDualFunctor, dualMap, dual]
      rw [← hf]
      simp only [comp_whiskerRight, assoc]
    _ = _ := by
      dsimp only [s, braidedFourDualIso, Iso.trans_hom, Iso.symm_hom, dualMapIso, dualMap]
      simp only [← comp_whiskerRight_assoc, assoc, Iso.hom_inv_id_assoc]

/-- The actual Radford square condition forces actual spherical traces on
that object, for every ambient endomorphism. -/
theorem braidedFourDual_trace_of_square (X : C) (phi : X ≅ (doubleDualFunctor C).obj X)
    (hsquare : phi.hom ≫ (doubleDualFunctor C).map phi.hom = (braidedFourDualIso X).hom)
    (f : X ⟶ X) :
    η_ (dual C X) (dual C (dual C X)) ≫ dual C X ◁ phi.inv ≫
      dual C X ◁ f ≫ ε_ X (dual C X) =
        η_ X (dual C X) ≫ f ▷ dual C X ≫ phi.hom ▷ dual C X ≫
          ε_ (dual C X) (dual C (dual C X)) := by
  rw [braidedFourDual_trace, ← hsquare]
  simp only [assoc, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    comp_id]

end Paper18.Category
