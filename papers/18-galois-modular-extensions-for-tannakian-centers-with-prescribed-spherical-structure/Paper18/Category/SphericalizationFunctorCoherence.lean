import Paper18.Category.SphericalizationFunctor
import Paper18.Category.PivotalBalancingTensor

/-! # Monoidal coherence of the canonical double-dual functor comparison -/
noncomputable section
universe v u v₁ u₁
namespace Paper18.Category
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Functor
open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [BraidedCategory C]
  {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] [RightRigidCategory D]
  [BraidedCategory D] (F : C ⥤ D) [F.Braided]

lemma doubleDualComparison_unit :
    ε (doubleDualFunctor C ⋙ F) ≫ (doubleDualComparison F (𝟙_ C)).hom =
      ε (F ⋙ doubleDualFunctor D) := by
  simp only [comp_ε, canonicalDoubleDual_unit, assoc]
  rw [← drinfeldIso_unit, doubleDualComparison_drinfeld]
  have hn := (drinfeldNatIso (C := D)).hom.naturality (ε F)
  change ε F ≫ (drinfeldIso (F.obj (𝟙_ C))).hom =
    (drinfeldIso (𝟙_ D)).hom ≫ (doubleDualFunctor D).map (ε F) at hn
  rw [hn, drinfeldIso_unit]

/-- The canonical comparison preserves tensorators. The double-braiding
defects of the two Drinfeld maps cancel using actual braided functor coherence. -/
lemma doubleDualComparison_tensor (X Y : C) :
    μ (doubleDualFunctor C ⋙ F) X Y ≫ (doubleDualComparison F (X ⊗ Y)).hom =
      ((doubleDualComparison F X).hom ⊗ₘ (doubleDualComparison F Y).hom) ≫
        μ (F ⋙ doubleDualFunctor D) X Y := by
  apply (cancel_epi (F.map (drinfeldIso X).hom ⊗ₘ F.map (drinfeldIso Y).hom)).mp
  simp only [comp_μ, assoc]
  rw [μ_natural_assoc, ← F.map_comp_assoc, canonicalDoubleDual_tensor,
    ← drinfeldIso_tensor, F.map_comp, assoc, doubleDualComparison_drinfeld]
  have hm : μ F X Y ≫ F.map (doubleBraiding X Y).hom =
      (doubleBraiding (F.obj X) (F.obj Y)).hom ≫ μ F X Y := by
    simp only [doubleBraiding, Iso.trans_hom, Functor.map_comp,
      assoc, Functor.LaxBraided.braided_assoc, Functor.LaxBraided.braided]
  rw [reassoc_of% hm]
  have hn := (drinfeldNatIso (C := D)).hom.naturality (μ F X Y)
  change μ F X Y ≫ (drinfeldIso (F.obj (X ⊗ Y))).hom =
    (drinfeldIso (F.obj X ⊗ F.obj Y)).hom ≫ (doubleDualFunctor D).map (μ F X Y) at hn
  rw [hn, ← assoc, drinfeldIso_tensor]
  simp only [tensorHom_comp_tensorHom_assoc, doubleDualComparison_drinfeld,
    canonicalDoubleDual_tensor, assoc]

/-- The comparison used for pivotal tensor functors is an actual monoidal
natural isomorphism for the canonical strong monoidal double-dual functors. -/
instance doubleDualComparison_isMonoidal :
    NatTrans.IsMonoidal (doubleDualComparisonNatIso F).hom where
  unit := doubleDualComparison_unit F
  tensor X Y := doubleDualComparison_tensor F X Y

/-- The canonical comparisons also preserve the braided four-dual map.
This is derived from preservation of Drinfeld's map and actual dual mates. -/
lemma doubleDualComparison_radford (X : C) :
    F.map (braidedFourDualIso X).hom ≫
      (doubleDualComparison F ((doubleDualFunctor C).obj X)).hom ≫
        (doubleDualFunctor D).map (doubleDualComparison F X).hom =
      (braidedFourDualIso (F.obj X)).hom := by
  have h₀ : F.map (drinfeldIso X).hom ≫ (dualComparison F (dual C X)).hom =
      (drinfeldIso (F.obj X)).hom ≫ dualMap D (dualComparison F X).hom := by
    have h := congrArg (fun f => f ≫ dualMap D (dualComparison F X).hom)
      (doubleDualComparison_drinfeld F X)
    dsimp only [doubleDualComparison, Iso.trans_hom, Iso.symm_hom, dualMapIso] at h
    simpa only [assoc, ← comp_rightAdjointMate, Iso.hom_inv_id,
      rightAdjointMate_id, comp_id] using h
  have hi : F.mapIso (drinfeldIso (dual C X)) ≪≫
      doubleDualComparison F (dual C X) ≪≫
        (doubleDualFunctor D).mapIso (dualComparison F X) =
      dualComparison F X ≪≫ drinfeldIso (dual D (F.obj X)) := by
    apply Iso.ext
    simp only [Iso.trans_hom, Functor.mapIso_hom]
    rw [← assoc, doubleDualComparison_drinfeld]
    exact ((drinfeldNatIso (C := D)).hom.naturality (dualComparison F X).hom).symm
  have hh := congrArg (fun e => e.inv ≫ (dualComparison F X).hom) hi
  simp only [Iso.trans_inv, Functor.mapIso_inv, assoc, Iso.inv_hom_id,
    comp_id] at hh
  have hd := congrArg (dualMap D) hh
  dsimp only [doubleDualComparison, Iso.trans_inv, Iso.symm_inv,
    dualMapIso, doubleDualFunctor, dualMap] at hd
  simp only [comp_rightAdjointMate, assoc] at hd
  dsimp only [braidedFourDualIso, Iso.trans_hom, Iso.symm_hom,
    doubleDualComparison, dualMapIso]
  rw [F.map_comp]
  simp only [Functor.map_comp, assoc]
  have hn := dualComparison_naturality F (drinfeldIso (dual C X)).inv
  dsimp only [doubleDualFunctor] at hn ⊢
  rw [reassoc_of% hn]
  rw [reassoc_of% h₀]
  dsimp only [doubleDualFunctor, dualMap]
  rw [hd]

end Paper18.Category
