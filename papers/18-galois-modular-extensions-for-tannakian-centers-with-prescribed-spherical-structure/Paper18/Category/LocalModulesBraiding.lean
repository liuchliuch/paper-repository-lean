import Paper18.Category.LocalModulesBasic

/-! # Actual descent of the ambient braiding to local modules -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open CategoryTheory.BraidedCategory
open scoped MonObj
universe v u
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  {A : C} [MonObj A]

@[reassoc]
private theorem braid_first_action (M N : Mod_ C A) :
    γ[A,M.X] ▷ N.X ≫ (β_ M.X N.X).hom =
      (α_ A M.X N.X).hom ≫ (A ◁ (β_ M.X N.X).hom) ≫
        (α_ A N.X M.X).inv ≫ (β_ A N.X).hom ▷ M.X ≫
          (α_ N.X A M.X).hom ≫ (N.X ◁ γ[A,M.X]) := by
  rw [braiding_naturality_left]
  change (β_ (A ⊗ M.X) N.X).hom ≫ (N.X ◁ γ[A,M.X]) = _
  rw [braiding_tensor_left_hom]
  simp only [Category.assoc]

@[reassoc]
private theorem braid_second_action (M N : Mod_ C A) :
    (α_ M.X A N.X).hom ≫ (M.X ◁ γ[A,N.X]) ≫ (β_ M.X N.X).hom =
      (β_ M.X A).hom ▷ N.X ≫ (α_ A M.X N.X).hom ≫
        (A ◁ (β_ M.X N.X).hom) ≫ (α_ A N.X M.X).inv ≫ γ[A,N.X] ▷ M.X := by
  rw [braiding_naturality_right]
  change (α_ M.X A N.X).hom ≫ (β_ M.X (A ⊗ N.X)).hom ≫ γ[A,N.X] ▷ M.X = _
  rw [braiding_tensor_right_hom]
  simp

open RelativeTensor

@[reassoc]
private theorem braid_action_balanced {M N : Mod_ C A} {Z : C}
    (q : N.X ⊗ M.X ⟶ Z) (hq : RelativeTensor.Balanced N M q) (hN : IsLocalModule N) :
    (β_ A N.X).hom ▷ M.X ≫ (α_ N.X A M.X).hom ≫
      (N.X ◁ γ[A,M.X]) ≫ q = γ[A,N.X] ▷ M.X ≫ q := by
  have hb : rightAction N ▷ M.X ≫ q =
      (α_ N.X A M.X).hom ≫ (N.X ◁ γ[A,M.X]) ≫ q := by
    simpa only [RelativeTensor.Balanced, parallelLeft, parallelRight, Category.assoc] using hq
  have hn : (β_ A N.X).hom ≫ rightAction N = γ[A,N.X] := by
    have h := (isLocalModule_iff N).mp hN
    simpa only [doubleBraiding, Iso.trans_hom, rightAction, Category.assoc] using h
  rw [← hb, ← comp_whiskerRight_assoc, hn]

/-- The ambient braiding followed by a balanced map is balanced whenever
the second module is local. -/
theorem balanced_braiding {M N : Mod_ C A} {Z : C}
    (q : N.X ⊗ M.X ⟶ Z) (hq : RelativeTensor.Balanced N M q) (hN : IsLocalModule N) :
    RelativeTensor.Balanced M N ((β_ M.X N.X).hom ≫ q) := by
  unfold RelativeTensor.Balanced parallelLeft parallelRight rightAction
  simp only [comp_whiskerRight, Category.assoc]
  rw [braid_first_action_assoc, braid_action_balanced q hq hN]
  simpa only [Category.assoc] using
    congrArg (fun k => k ≫ q) (braid_second_action M N).symm

/-- Braiding preserves module linearity for a balanced map whose second
input is local. -/
theorem linear_braiding {M N P : Mod_ C A}
    (q : N.X ⊗ M.X ⟶ P.X) (hq : RelativeTensor.Balanced N M q)
    (hN : IsLocalModule N)
    (hlin : (A ◁ q) ≫ γ[A,P.X] =
      (α_ A N.X M.X).inv ≫ γ[A,N.X] ▷ M.X ≫ q) :
    (α_ A M.X N.X).inv ≫ γ[A,M.X] ▷ N.X ≫ (β_ M.X N.X).hom ≫ q =
      (A ◁ ((β_ M.X N.X).hom ≫ q)) ≫ γ[A,P.X] := by
  rw [braid_first_action_assoc]
  simp only [Iso.inv_hom_id_assoc]
  rw [braid_action_balanced q hq hN]
  rw [whiskerLeft_comp]
  simp only [Category.assoc]
  rw [hlin]

section Relative
variable [RightRigidCategory C] [HasCoequalizers C] [IsCommMonObj A]

/-- The ambient braiding descends to an actual module morphism into the
opposite relative tensor when its second input is local. -/
def localBraidingHom (M N : Mod_ C A) (hN : IsLocalModule N) : M ⊗ N ⟶ N ⊗ M :=
  descModule M N (N ⊗ M) ((β_ M.X N.X).hom ≫ π N M)
    (balanced_braiding (π N M) (condition N M) hN)
    (linear_braiding (π N M) (condition N M) hN (π_action N M))

@[reassoc (attr := simp)]
theorem π_localBraidingHom (M N : Mod_ C A) (hN : IsLocalModule N) :
    π M N ≫ (localBraidingHom M N hN).hom = (β_ M.X N.X).hom ≫ π N M :=
  π_desc M N _ _

/-- The inverse ambient braiding also descends when both modules are local. -/
def localBraidingInv (M N : Mod_ C A) (hM : IsLocalModule M) (hN : IsLocalModule N) :
    N ⊗ M ⟶ M ⊗ N := by
  have hbal : @RelativeTensor.Balanced C _ _ (reverseBraiding C) A _ M N _ (π M N) := by
    change ((β_ A M.X).inv ≫ γ[A,M.X]) ▷ N.X ≫ π M N = _
    rw [← hM]
    exact condition M N
  have hlocal : @IsLocalModule C _ _ (reverseBraiding C) A _ M := by
    exact hM.symm
  have hb := @balanced_braiding C _ _ (reverseBraiding C) A _ N M _ (π M N) hbal hlocal
  have hl := @linear_braiding C _ _ (reverseBraiding C) A _ N M (M ⊗ N)
    (π M N) hbal hlocal (π_action M N)
  apply descModule N M (M ⊗ N) ((β_ M.X N.X).inv ≫ π M N)
  · change (rightAction N ▷ M.X) ≫ _ = _
    rw [hN]
    exact hb
  · exact hl

@[reassoc (attr := simp)]
theorem π_localBraidingInv (M N : Mod_ C A) (hM : IsLocalModule M) (hN : IsLocalModule N) :
    π N M ≫ (localBraidingInv M N hM hN).hom = (β_ M.X N.X).inv ≫ π M N :=
  π_desc N M _ _

/-- The ambient braiding induces an actual isomorphism of local modules. -/
def localBraidingIso (M N : Mod_ C A) (hM : IsLocalModule M) (hN : IsLocalModule N) :
    M ⊗ N ≅ N ⊗ M where
  hom := localBraidingHom M N hN
  inv := localBraidingInv M N hM hN
  hom_inv_id := by
    apply module_hom_ext
    change π M N ≫ (localBraidingHom M N hN).hom ≫
      (localBraidingInv M N hM hN).hom = π M N ≫ 𝟙 _
    simp
  inv_hom_id := by
    apply module_hom_ext
    change π N M ≫ (localBraidingInv M N hM hN).hom ≫
      (localBraidingHom M N hN).hom = π N M ≫ 𝟙 _
    simp

end Relative
end Paper18.Category
