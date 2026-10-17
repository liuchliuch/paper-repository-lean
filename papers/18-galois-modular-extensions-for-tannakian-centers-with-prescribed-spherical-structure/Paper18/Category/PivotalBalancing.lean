import Paper18.Category.PivotalBalancingTensor

/-!
# Actual pivotal structures and actual balanced twists

The tensor law of the twist induced by a pivotal structure is derived from
the proved Drinfeld tensor comparison. Conversely an actual natural twist
whose component equations have been proved gives a coherent pivotal structure.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory
universe v u
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C]

@[reassoc] lemma doubleBraiding_naturality {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    (f ⊗ₘ g) ≫ (doubleBraiding X' Y').hom =
      (doubleBraiding X Y).hom ≫ (f ⊗ₘ g) := by
  simp only [doubleBraiding, Iso.trans_hom, assoc]
  rw [braiding_naturality_assoc, braiding_naturality]

namespace PivotalStructure
variable (J : PivotalStructure C)

lemma twist_unit : (J.twistIso (𝟙_ C)).hom = 𝟙 (𝟙_ C) := by
  rw [J.twistIso_hom, J.unit, ← drinfeldIso_unit]
  exact (drinfeldIso (𝟙_ C)).hom_inv_id

/-- The balancing law is derived for the actual induced twist. -/
lemma twist_tensor (X Y : C) :
    (J.twistIso (X ⊗ Y)).hom =
      (doubleBraiding X Y).hom ≫ ((J.twistIso X).hom ⊗ₘ (J.twistIso Y).hom) := by
  apply (cancel_mono (drinfeldIso (X ⊗ Y)).hom).1
  rw [J.twist_comp_drinfeld]
  calc
    _ = (J.j.hom.app X ⊗ₘ J.j.hom.app Y) ≫ doubleDualTensorHom C X Y := J.tensor X Y
    _ = (((J.twistIso X).hom ≫ (drinfeldIso X).hom) ⊗ₘ
        ((J.twistIso Y).hom ≫ (drinfeldIso Y).hom)) ≫ doubleDualTensorHom C X Y := by
      rw [J.twist_comp_drinfeld, J.twist_comp_drinfeld]
    _ = ((J.twistIso X).hom ⊗ₘ (J.twistIso Y).hom) ≫
        (((drinfeldIso X).hom ⊗ₘ (drinfeldIso Y).hom) ≫ doubleDualTensorHom C X Y) := by
      rw [tensorHom_comp_tensorHom_assoc]
    _ = ((J.twistIso X).hom ⊗ₘ (J.twistIso Y).hom) ≫
        (doubleBraiding X Y).hom ≫ (drinfeldIso (X ⊗ Y)).hom := by rw [drinfeldIso_tensor]
    _ = _ := by rw [doubleBraiding_naturality_assoc]; simp only [assoc]

end PivotalStructure

/-- A natural twist with proved categorical unit and balancing equations
induces the actual pivotal structure `j = θ u`. -/
def pivotalOfBalancing (θ : 𝟭 C ≅ 𝟭 C)
    (hunit : θ.hom.app (𝟙_ C) = 𝟙 (𝟙_ C))
    (htensor : ∀ X Y, θ.hom.app (X ⊗ Y) =
      (doubleBraiding X Y).hom ≫ (θ.hom.app X ⊗ₘ θ.hom.app Y)) : PivotalStructure C where
  j := θ ≪≫ drinfeldNatIso
  unit := by
    change θ.hom.app (𝟙_ C) ≫ (drinfeldIso (𝟙_ C)).hom = _
    rw [hunit]
    exact (Category.id_comp _).trans drinfeldIso_unit
  tensor X Y := by
    change θ.hom.app (X ⊗ Y) ≫ (drinfeldIso (X ⊗ Y)).hom =
      ((θ.hom.app X ≫ (drinfeldIso X).hom) ⊗ₘ
        (θ.hom.app Y ≫ (drinfeldIso Y).hom)) ≫ doubleDualTensorHom C X Y
    rw [htensor]
    calc
      _ = (θ.hom.app X ⊗ₘ θ.hom.app Y) ≫
          (doubleBraiding X Y).hom ≫ (drinfeldIso (X ⊗ Y)).hom := by
        simpa only [assoc] using congrArg (fun f => f ≫ (drinfeldIso (X ⊗ Y)).hom)
          (doubleBraiding_naturality (θ.hom.app X) (θ.hom.app Y)).symm
      _ = (θ.hom.app X ⊗ₘ θ.hom.app Y) ≫
          (((drinfeldIso X).hom ⊗ₘ (drinfeldIso Y).hom) ≫ doubleDualTensorHom C X Y) := by
        rw [drinfeldIso_tensor]
      _ = _ := by rw [tensorHom_comp_tensorHom_assoc]

@[simp] lemma pivotalOfBalancing_j (θ : 𝟭 C ≅ 𝟭 C) (hu ht) :
    (pivotalOfBalancing θ hu ht).j = θ ≪≫ drinfeldNatIso := rfl

/-- Recovering the twist from the constructed pivotal structure returns
the original actual natural isomorphism. -/
@[simp] lemma pivotalOfBalancing_twist (θ : 𝟭 C ≅ 𝟭 C) (hu ht) :
    (pivotalOfBalancing θ hu ht).twistNatIso = θ := by
  ext X
  simp [PivotalStructure.twistNatIso, pivotalOfBalancing, assoc]

end Paper18.Category
