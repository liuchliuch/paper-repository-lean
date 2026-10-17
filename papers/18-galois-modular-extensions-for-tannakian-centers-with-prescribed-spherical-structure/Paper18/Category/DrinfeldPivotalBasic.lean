import Paper18.Category.DrinfeldPivotalDual

/-! # Pivotal identifications are actual central morphisms -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u
namespace Paper18.Category.Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [LeftRigidCategory C]

/-- Double transposition of a half-braiding is the canonical double-dual
image of that half-braiding, including its actual tensor comparisons. -/
lemma doubleDualTensor_halfBraiding (Z : Center C) (U : C) :
    doubleDualTensorHom C Z.1 U ≫ (doubleDualFunctor C).map (Z.2.β U).hom =
      ((rightDualObj (rightDualObj Z)).2.β ((doubleDualFunctor C).obj U)).hom ≫
        doubleDualTensorHom C U Z.1 := by
  have h := congrArg (fun f => dualMap C f) (dualTensorIso_halfBraiding Z U)
  have hd := dualTensorIso_halfBraiding (rightDualObj Z) Uᘁ
  simp only [rightDualObj_fst, rightDualObj_halfBraiding] at hd
  simp only [dualMap, comp_rightAdjointMate] at h
  change doubleDualTensorHom C Z.1 U ≫ (doubleDualFunctor C).map (Z.2.β U).hom =
    dualHalfBraidingHom (rightDualObj Z) Uᘁᘁ ≫ doubleDualTensorHom C U Z.1
  dsimp only [doubleDualTensorHom]
  rw [← dualTensorIso_inv, ← dualTensorIso_hom,
    ← dualTensorIso_inv, ← dualTensorIso_hom]
  apply (cancel_epi (dualTensorIso Uᘁ Z.1ᘁ).hom).mp
  simp only [← assoc, Iso.hom_inv_id, id_comp]
  rw [← hd]
  simp only [assoc, Iso.hom_inv_id_assoc]
  exact h

/-- Monoidality and naturality of the ambient pivotal isomorphism imply
that each component commutes with every actual half-braiding. -/
lemma pivotalMap_central (J : PivotalStructure C) (Z : Center C) (U : C) :
    J.j.hom.app Z.1 ▷ U ≫ ((rightDualObj (rightDualObj Z)).2.β U).hom =
      (Z.2.β U).hom ≫ U ◁ J.j.hom.app Z.1 := by
  letI := J.doubleDualTensorHom_isIso U Z.1
  have hn := J.j.hom.naturality (Z.2.β U).hom
  change (Z.2.β U).hom ≫ J.j.hom.app (U ⊗ Z.1) =
    J.j.hom.app (Z.1 ⊗ U) ≫ (doubleDualFunctor C).map (Z.2.β U).hom at hn
  rw [J.tensor, J.tensor] at hn
  have ht : (J.j.hom.app Z.1 ⊗ₘ J.j.hom.app U) ≫
      ((rightDualObj (rightDualObj Z)).2.β ((doubleDualFunctor C).obj U)).hom =
        (Z.2.β U).hom ≫ (J.j.hom.app U ⊗ₘ J.j.hom.app Z.1) := by
    apply (cancel_mono (doubleDualTensorHom C U Z.1)).mp
    rw [assoc, ← doubleDualTensor_halfBraiding]
    simpa only [assoc] using hn.symm
  apply (cancel_mono (J.j.hom.app U ▷ ((rightDualObj (rightDualObj Z)).1))).mp
  calc
    _ = (J.j.hom.app Z.1 ⊗ₘ J.j.hom.app U) ≫
        ((rightDualObj (rightDualObj Z)).2.β ((doubleDualFunctor C).obj U)).hom := by
      dsimp only [Functor.id_obj]
      rw [tensorHom_def, assoc]
      have hb := congrArg (fun t => J.j.hom.app Z.1 ▷ U ≫ t)
        ((rightDualObj (rightDualObj Z)).2.naturality (J.j.hom.app U))
      simpa only [Functor.id_obj, rightDualObj_fst, assoc] using hb.symm
    _ = _ := ht
    _ = _ := by
      rw [tensorHom_def']
      simp only [assoc]
      rfl

end Paper18.Category.Drinfeld
