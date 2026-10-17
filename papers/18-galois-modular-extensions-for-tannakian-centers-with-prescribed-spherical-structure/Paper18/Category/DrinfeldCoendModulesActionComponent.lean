import Paper18.Category.DrinfeldCoendModulesBasic

/-! # Actual annular action components and detection of central morphisms

The component is the genuine rigid transpose of the difference between
an object's half-braiding and the ambient braiding. No module law is assumed.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory
universe v u
namespace Paper18.Category.DrinfeldCoendModules
attribute [local instance 2000] RightRigidCategory.rightDual
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D]

/-- The actual annular crossing, normalized to be the identity for the
negative ambient central embedding. -/
def holonomy (Z : Center D) (T : D) : T ⊗ Z.1 ≅ T ⊗ Z.1 :=
  (Z.2.β T).symm ≪≫ (β_ T Z.1).symm

/-- Commuting with the actual annular crossings is exactly commuting
with the actual half-braidings. -/
lemma holonomy_comm_iff {Z W : Center D} (f : Z.1 ⟶ W.1) (T : D) :
    T ◁ f ≫ (holonomy W T).hom = (holonomy Z T).hom ≫ T ◁ f ↔
      f ▷ T ≫ (W.2.β T).hom = (Z.2.β T).hom ≫ T ◁ f := by
  dsimp only [holonomy, Iso.trans_hom, Iso.symm_hom]
  constructor
  · intro h
    have hi : T ◁ f ≫ (W.2.β T).inv = (Z.2.β T).inv ≫ f ▷ T := by
      apply (cancel_mono (β_ T W.1).inv).mp
      simpa only [assoc, braiding_inv_naturality_left] using h
    apply (cancel_mono (W.2.β T).inv).mp
    simp only [assoc, Iso.hom_inv_id, comp_id]
    rw [hi, Iso.hom_inv_id_assoc]
  · intro h
    have hi : T ◁ f ≫ (W.2.β T).inv = (Z.2.β T).inv ≫ f ▷ T := by
      apply (cancel_epi (Z.2.β T).hom).mp
      simp only [← assoc, Iso.hom_inv_id, id_comp]
      rw [← h, assoc, Iso.hom_inv_id, comp_id]
    rw [← assoc, hi, assoc, braiding_inv_naturality_left]
    rw [assoc]

/-- Naturality of the actual annular crossing in the coend label. -/
lemma holonomy_naturality (Z : Center D) {T U : D} (f : T ⟶ U) :
    f ▷ Z.1 ≫ (holonomy Z U).hom = (holonomy Z T).hom ≫ f ▷ Z.1 := by
  have hi : f ▷ Z.1 ≫ (Z.2.β U).inv = (Z.2.β T).inv ≫ Z.1 ◁ f := by
    apply (cancel_epi (Z.2.β T).hom).mp
    simp only [Iso.hom_inv_id_assoc]
    rw [← reassoc_of% (Z.2.naturality f), Iso.hom_inv_id, comp_id]
  dsimp only [holonomy, Iso.trans_hom, Iso.symm_hom]
  rw [← assoc, hi, assoc, braiding_inv_naturality_right, assoc]

/-- The actual cap component is the actual left rigid transpose of the
annular crossing, including the specified associator. -/
def actionComponent (Z : Center D) (T : D) : (dual D T ⊗ T) ⊗ Z.1 ⟶ Z.1 :=
  (α_ (dual D T) T Z.1).hom ≫
    (tensorLeftHomEquiv (T ⊗ Z.1) T (dual D T) Z.1).symm (holonomy Z T).hom

lemma actionComponent_def (Z : Center D) (T : D) :
    actionComponent Z T = (α_ (dual D T) T Z.1).hom ≫
      dual D T ◁ (holonomy Z T).hom ≫ (α_ (dual D T) T Z.1).inv ≫
        ε_ T (dual D T) ▷ Z.1 ≫ (λ_ Z.1).hom := rfl

/-- Pulling the actual cap component back across the cup recovers its
specified annular crossing exactly. -/
lemma actionComponent_transpose (Z : Center D) (T : D) :
    tensorLeftHomEquiv (T ⊗ Z.1) T (dual D T) Z.1
      ((α_ (dual D T) T Z.1).inv ≫ actionComponent Z T) = (holonomy Z T).hom := by
  dsimp only [actionComponent]
  rw [Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]

/-- The actual cap components are dinatural in the coend label. -/
lemma actionComponent_dinaturality (Z : Center D) {T U : D} (f : T ⟶ U) :
    (dualMap D f ▷ T) ▷ Z.1 ≫ actionComponent Z T =
      (dual D U ◁ f) ▷ Z.1 ≫ actionComponent Z U := by
  calc
    _ = (α_ (dual D U) T Z.1).hom ≫
        dual D U ◁ (holonomy Z T).hom ≫ (α_ (dual D U) T Z.1).inv ≫
          ((dualMap D f ▷ T) ≫ ε_ T (dual D T)) ▷ Z.1 ≫ (λ_ Z.1).hom := by
      rw [actionComponent_def]
      rw [associator_naturality_left_assoc, ← whisker_exchange_assoc,
        associator_inv_naturality_left_assoc, ← comp_whiskerRight_assoc]
    _ = (α_ (dual D U) T Z.1).hom ≫
        dual D U ◁ (holonomy Z T).hom ≫ (α_ (dual D U) T Z.1).inv ≫
          ((dual D U ◁ f) ≫ ε_ U (dual D U)) ▷ Z.1 ≫ (λ_ Z.1).hom := by
      rw [rightAdjointMate_comp_evaluation]
    _ = (α_ (dual D U) T Z.1).hom ≫
        dual D U ◁ ((holonomy Z T).hom ≫ f ▷ Z.1) ≫
          (α_ (dual D U) U Z.1).inv ≫ ε_ U (dual D U) ▷ Z.1 ≫ (λ_ Z.1).hom := by
      monoidal
    _ = (α_ (dual D U) T Z.1).hom ≫
        dual D U ◁ (f ▷ Z.1 ≫ (holonomy Z U).hom) ≫
          (α_ (dual D U) U Z.1).inv ≫ ε_ U (dual D U) ▷ Z.1 ≫ (λ_ Z.1).hom := by
      rw [holonomy_naturality]
    _ = _ := by
      rw [actionComponent_def]
      monoidal

/-- Naturality of the actual rigid transpose in its source. -/
lemma transpose_source_naturality {X X' Z : D} (T : D) (f : X ⟶ X')
    (g : dual D T ⊗ X' ⟶ Z) :
    tensorLeftHomEquiv X T (dual D T) Z (dual D T ◁ f ≫ g) =
      f ≫ tensorLeftHomEquiv X' T (dual D T) Z g := by
  apply (tensorLeftHomEquiv X T (dual D T) Z).symm.injective
  rw [Equiv.symm_apply_apply, tensorLeftHomEquiv_symm_naturality,
    Equiv.symm_apply_apply]

/-- The rigid cap components detect precisely the actual central
morphism equation. -/
lemma actionComponent_comm_iff {Z W : Center D} (f : Z.1 ⟶ W.1) (T : D) :
    actionComponent Z T ≫ f = (dual D T ⊗ T) ◁ f ≫ actionComponent W T ↔
      f ▷ T ≫ (W.2.β T).hom = (Z.2.β T).hom ≫ T ◁ f := by
  rw [← holonomy_comm_iff f T]
  let E := tensorLeftHomEquiv (T ⊗ Z.1) T (dual D T) W.1
  have hL : E ((α_ (dual D T) T Z.1).inv ≫ (actionComponent Z T ≫ f)) =
      (holonomy Z T).hom ≫ T ◁ f := by
    dsimp only [E]
    rw [← assoc, tensorLeftHomEquiv_naturality, actionComponent_transpose]
  have hR : E ((α_ (dual D T) T Z.1).inv ≫
      ((dual D T ⊗ T) ◁ f ≫ actionComponent W T)) =
      T ◁ f ≫ (holonomy W T).hom := by
    dsimp only [E]
    rw [← associator_inv_naturality_right_assoc]
    rw [transpose_source_naturality, actionComponent_transpose]
  constructor
  · intro h
    have hh := congrArg (fun k => E ((α_ (dual D T) T Z.1).inv ≫ k)) h
    dsimp only at hh
    rw [hL, hR] at hh
    exact hh.symm
  · intro h
    apply (cancel_epi (α_ (dual D T) T Z.1).inv).mp
    apply E.injective
    rw [hL, hR]
    exact h.symm

end Paper18.Category.DrinfeldCoendModules
