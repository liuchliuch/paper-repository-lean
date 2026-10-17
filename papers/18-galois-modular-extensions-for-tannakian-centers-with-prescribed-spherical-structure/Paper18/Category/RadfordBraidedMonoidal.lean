import Paper18.Category.RadfordBraidedCoherence
import Paper18.Category.RadfordDualBraiding

/-! # Monoidality of the braided four-dual comparison -/
noncomputable section
universe v u
namespace Paper18.Category
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C]

lemma dualTensorIso_doubleBraiding (X Y : C) :
    dualMap C (doubleBraiding X Y).hom ≫ (dualTensorIso X Y).hom =
      (dualTensorIso X Y).hom ≫ (doubleBraiding (dual C Y) (dual C X)).hom := by
  dsimp only [doubleBraiding, Iso.trans_hom]
  rw [show dualMap C ((β_ X Y).hom ≫ (β_ Y X).hom) =
      dualMap C (β_ Y X).hom ≫ dualMap C (β_ X Y).hom from comp_rightAdjointMate]
  rw [assoc, dualTensorIso_braiding, ← assoc, dualTensorIso_braiding, assoc]

lemma dualTensorIso_inv_doubleBraiding (X Y : C) :
    (dualTensorIso X Y).inv ≫ dualMap C (doubleBraiding X Y).hom =
      (doubleBraiding (dual C Y) (dual C X)).hom ≫ (dualTensorIso X Y).inv := by
  apply (cancel_mono (dualTensorIso X Y).hom).mp
  rw [assoc, dualTensorIso_doubleBraiding]
  simp only [← assoc, Iso.inv_hom_id, id_comp, Iso.inv_hom_id_assoc]
  simp only [assoc, Iso.inv_hom_id, comp_id]

lemma drinfeldIso_conjugate {X Y : C} (e : X ≅ Y) :
    drinfeldIso X = e ≪≫ drinfeldIso Y ≪≫ (doubleDualFunctor C).mapIso e.symm := by
  apply Iso.ext
  apply (cancel_mono ((doubleDualFunctor C).mapIso e).hom).mp
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, assoc,
    ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, comp_id]
  exact (drinfeldIso_naturality e.hom).symm

lemma drinfeldIso_tensor_iso (X Y : C) :
    drinfeldIso (X ⊗ Y) = (doubleBraiding X Y).symm ≪≫
      ((drinfeldIso X) ⊗ᵢ (drinfeldIso Y)) ≪≫ μIso (doubleDualFunctor C) X Y := by
  apply Iso.ext
  apply (cancel_epi (doubleBraiding X Y).hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, μIso_hom,
    ← assoc, Iso.hom_inv_id, id_comp, canonicalDoubleDual_tensor]
  exact drinfeldIso_tensor X Y

lemma canonicalDoubleDual_tensor_iso (X Y : C) :
    μIso (doubleDualFunctor C) X Y =
      (dualTensorIso (dual C Y) (dual C X)).symm ≪≫ dualMapIso (dualTensorIso X Y) := by
  apply Iso.ext
  rw [μIso_hom, canonicalDoubleDual_tensor]
  simp only [Iso.trans_hom, Iso.symm_hom, dualTensorIso_inv,
    dualMapIso, dualTensorIso_hom, doubleDualTensorHom]

lemma braidedFourDualIso_tensor_expand (X Y : C) :
    (braidedFourDualIso (X ⊗ Y)).hom =
      (doubleBraiding X Y).inv ≫
        ((drinfeldIso X).hom ⊗ₘ (drinfeldIso Y).hom) ≫
          (dualTensorIso (dual C Y) (dual C X)).inv ≫
            dualMap C (drinfeldIso (dual C Y ⊗ dual C X)).inv ≫
              dualMap C ((doubleDualFunctor C).map (dualTensorIso X Y).hom) := by
  dsimp only [braidedFourDualIso, Iso.trans_hom, Iso.symm_hom, dualMapIso]
  rw [drinfeldIso_conjugate (dualTensorIso X Y), drinfeldIso_tensor_iso X Y,
    canonicalDoubleDual_tensor_iso]
  dsimp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    tensorIso_hom, Functor.mapIso_hom, dualMapIso]
  simp only [dualMap, comp_rightAdjointMate, assoc]
  simp only [← comp_rightAdjointMate_assoc, Iso.inv_hom_id, rightAdjointMate_id, id_comp]
  simp only [assoc, Iso.inv_hom_id, comp_id, Functor.mapIso_inv, Iso.symm_inv]

lemma drinfeld_tensor_dual_inverse (X Y : C) :
    dualMap C (drinfeldIso (X ⊗ Y)).inv =
      dualMap C (doubleBraiding X Y).hom ≫
        dualMap C ((drinfeldIso X).inv ⊗ₘ (drinfeldIso Y).inv) ≫
          dualMap C (μIso (doubleDualFunctor C) X Y).inv := by
  rw [drinfeldIso_tensor_iso]
  dsimp only [Iso.trans_inv, Iso.symm_inv, tensorIso_inv]
  simp only [dualMap, comp_rightAdjointMate, assoc]

lemma dual_tensor_inverse_naturality {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    (dualTensorIso X' Y').inv ≫ dualMap C (f ⊗ₘ g) =
      (dualMap C g ⊗ₘ dualMap C f) ≫ (dualTensorIso X Y).inv := by
  apply (cancel_mono (dualTensorIso X Y).hom).mp
  rw [assoc, dualTensorIso_naturality]
  simp only [← assoc, Iso.inv_hom_id, id_comp]
  simp only [assoc, Iso.inv_hom_id, comp_id]

lemma canonicalDoubleDual_iterated_tensor (X Y : C) :
    (dualTensorIso ((doubleDualFunctor C).obj (dual C Y))
      ((doubleDualFunctor C).obj (dual C X))).inv ≫
        dualMap C (μIso (doubleDualFunctor C) (dual C Y) (dual C X)).inv ≫
          dualMap C ((doubleDualFunctor C).map (dualTensorIso X Y).hom) =
            μ (doubleDualFunctor C ⋙ doubleDualFunctor C) X Y := by
  rw [canonicalDoubleDual_tensor_iso, Functor.LaxMonoidal.comp_μ]
  dsimp only [Iso.trans_inv, Iso.symm_inv, dualMapIso]
  simp only [canonicalDoubleDual_tensor, doubleDualTensorHom,
    ← dualTensorIso_inv, ← dualTensorIso_hom, Functor.map_comp]
  dsimp only [doubleDualFunctor, dualMap]
  simp only [comp_rightAdjointMate, assoc]

/-- The canonical braided four-dual comparison respects tensor products.
The two Drinfeld tensor defects cancel after dualization. -/
theorem braidedFourDualIso_tensor (X Y : C) :
    (braidedFourDualIso (X ⊗ Y)).hom =
      ((braidedFourDualIso X).hom ⊗ₘ (braidedFourDualIso Y).hom) ≫
        μ (doubleDualFunctor C ⋙ doubleDualFunctor C) X Y := by
  have hm := dualTensorIso_inv_doubleBraiding (dual C Y) (dual C X)
  have hn : ((drinfeldIso X).hom ⊗ₘ (drinfeldIso Y).hom) ≫
      (doubleBraiding ((doubleDualFunctor C).obj X) ((doubleDualFunctor C).obj Y)).hom =
        (doubleBraiding X Y).hom ≫ ((drinfeldIso X).hom ⊗ₘ (drinfeldIso Y).hom) := by
    simp only [doubleBraiding, Iso.trans_hom, braiding_naturality_assoc,
      braiding_naturality, assoc]
  rw [braidedFourDualIso_tensor_expand, drinfeld_tensor_dual_inverse]
  simp only [assoc]
  dsimp only [doubleDualFunctor] at hn
  rw [reassoc_of% hm, reassoc_of% hn]
  simp only [assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% (dual_tensor_inverse_naturality
    (drinfeldIso (dual C Y)).inv (drinfeldIso (dual C X)).inv)]
  rw [← assoc, tensorHom_comp_tensorHom]
  change ((braidedFourDualIso X).hom ⊗ₘ (braidedFourDualIso Y).hom) ≫ _ = _
  rw [canonicalDoubleDual_iterated_tensor]

lemma canonicalDoubleDual_unit_iso :
    εIso (doubleDualFunctor C) =
      (dualUnitIso (C := C)).symm ≪≫ dualMapIso (dualUnitIso (C := C)) := by
  apply Iso.ext
  rw [εIso_hom, canonicalDoubleDual_unit]
  simp only [Iso.trans_hom, Iso.symm_hom, dualUnitIso_inv,
    dualMapIso, dualUnitIso_hom, doubleDualUnitHom]

/-- Unit coherence for the actual four-dual natural comparison. -/
theorem braidedFourDualIso_unit :
    (braidedFourDualIso (𝟙_ C)).hom = ε (doubleDualFunctor C ⋙ doubleDualFunctor C) := by
  have hu : drinfeldIso (𝟙_ C) = εIso (doubleDualFunctor C) := by
    apply Iso.ext
    simpa only [εIso_hom, canonicalDoubleDual_unit] using (drinfeldIso_unit (C := C))
  dsimp only [braidedFourDualIso, Iso.trans_hom, Iso.symm_hom, dualMapIso]
  rw [drinfeldIso_conjugate (dualUnitIso (C := C)), hu,
    canonicalDoubleDual_unit_iso, Functor.LaxMonoidal.comp_ε]
  dsimp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    dualMapIso, Functor.mapIso_inv]
  simp only [canonicalDoubleDual_unit, doubleDualUnitHom,
    ← dualUnitIso_inv, ← dualUnitIso_hom, Functor.map_comp]
  dsimp only [doubleDualFunctor, dualMap]
  simp only [comp_rightAdjointMate, assoc]
  simp only [← comp_rightAdjointMate_assoc, Iso.inv_hom_id, rightAdjointMate_id, id_comp]
  simp only [assoc, Iso.inv_hom_id, comp_id]

/-- Radford's braided four-dual comparison is an actual monoidal natural
isomorphism, constructed without a pivotal structure. -/
instance braidedFourDual_isMonoidal :
    NatTrans.IsMonoidal (braidedFourDualNatIso (C := C)).hom where
  unit := by
    change 𝟙 (𝟙_ C) ≫ (braidedFourDualIso (𝟙_ C)).hom = _
    rw [id_comp, braidedFourDualIso_unit]
  tensor X Y := by
    change 𝟙 (X ⊗ Y) ≫ (braidedFourDualIso (X ⊗ Y)).hom = _
    rw [id_comp, braidedFourDualIso_tensor]
    rfl

end Paper18.Category
