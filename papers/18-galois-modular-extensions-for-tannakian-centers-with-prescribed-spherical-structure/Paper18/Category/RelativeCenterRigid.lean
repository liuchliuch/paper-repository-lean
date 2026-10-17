import Paper18.Category.RelativeCenterRigidLax
import Paper18.Category.RelativeCenterKernels
import Paper18.Category.PivotalFunctor
import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence

/-!
# Actual right duals in the Drinfeld center

The dual half-braiding is obtained by partial transposition and its
invertibility has been proved from rigidity. Evaluation and coevaluation
are the actual underlying cups and caps, and their centrality is derived.
-/
noncomputable section
universe v u w
namespace Paper18.Category.RelativeCenter
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
attribute [local instance 2000] RightRigidCategory.rightDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C]
  {P : ObjectProperty C} [P.IsMonoidal] (Z : RelativeCenter P)

/-- The partial transpose as a cup-and-cap diagram. -/
lemma dualHalfBraidingHom_eq (U : C) (hU : P U) : dualHalfBraidingHom Z U hU =
    𝟙 (Z.1ᘁ ⊗ U) ⊗≫ (Z.1ᘁ ⊗ U) ◁ η_ Z.1 Z.1ᘁ ⊗≫
      (Z.1ᘁ : C) ◁ (Z.2.β U hU).inv ▷ Z.1ᘁ ⊗≫
        ε_ Z.1 Z.1ᘁ ▷ (U ⊗ Z.1ᘁ) ⊗≫ 𝟙 (U ⊗ Z.1ᘁ) := by
  dsimp [dualHalfBraidingHom, tensorRightHomEquiv, dualHalfBraidingCap]
  monoidal

/-- The same partial transpose also intertwines the actual coevaluation. -/
@[reassoc]
lemma dualHalfBraidingHom_cup (U : C) (hU : P U) :
    η_ Z.1 Z.1ᘁ ▷ U ≫ (α_ Z.1 Z.1ᘁ U).hom ≫
      Z.1 ◁ dualHalfBraidingHom Z U hU =
    (λ_ U).hom ≫ (ρ_ U).inv ≫ U ◁ η_ Z.1 Z.1ᘁ ≫
      (α_ U Z.1 Z.1ᘁ).inv ≫ (Z.2.β U hU).inv ▷ Z.1ᘁ ≫ (α_ Z.1 U Z.1ᘁ).hom := by
  calc
    _ = 𝟙 ((𝟙_ C) ⊗ U) ⊗≫
        (η_ Z.1 Z.1ᘁ ▷ (U ⊗ 𝟙_ C) ≫ (Z.1 ⊗ Z.1ᘁ) ◁ (U ◁ η_ Z.1 Z.1ᘁ)) ⊗≫
        Z.1 ◁ (Z.1ᘁ : C) ◁ (Z.2.β U hU).inv ▷ Z.1ᘁ ⊗≫
        Z.1 ◁ ε_ Z.1 Z.1ᘁ ▷ (U ⊗ Z.1ᘁ) ⊗≫ 𝟙 (Z.1 ⊗ (U ⊗ Z.1ᘁ)) := by
      rw [dualHalfBraidingHom_eq (hU := hU)]
      monoidal
    _ = 𝟙 ((𝟙_ C) ⊗ U) ⊗≫ U ◁ η_ Z.1 Z.1ᘁ ⊗≫
        (η_ Z.1 Z.1ᘁ ▷ (U ⊗ Z.1) ≫ (Z.1 ⊗ Z.1ᘁ) ◁ (Z.2.β U hU).inv) ▷ Z.1ᘁ ⊗≫
        Z.1 ◁ ε_ Z.1 Z.1ᘁ ▷ (U ⊗ Z.1ᘁ) ⊗≫ 𝟙 (Z.1 ⊗ (U ⊗ Z.1ᘁ)) := by
      rw [← whisker_exchange]
      monoidal
    _ = 𝟙 ((𝟙_ C) ⊗ U) ⊗≫ U ◁ η_ Z.1 Z.1ᘁ ⊗≫
        (Z.2.β U hU).inv ▷ Z.1ᘁ ⊗≫
        (η_ Z.1 Z.1ᘁ ▷ Z.1 ⊗≫ Z.1 ◁ ε_ Z.1 Z.1ᘁ) ▷ (U ⊗ Z.1ᘁ) ⊗≫
        𝟙 (Z.1 ⊗ (U ⊗ Z.1ᘁ)) := by
      rw [← whisker_exchange]
      monoidal
    _ = _ := by
      rw [ExactPairing.evaluation_coevaluation'']
      monoidal

variable [LeftRigidCategory C] [Preadditive C] [Linear ℂ C]
  [CategoryTheory.Limits.HasKernels C] [CategoryTheory.Limits.HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [Simple (𝟙_ C)]
  [IsAdditiveFullProperty P] {ι : Type w} [Fintype ι]
  (S : FiniteSemisimpleSkeleton C ι) (J : PivotalStructure C)

include S J in
lemma property_leftDual (U : C) (hU : P U) : P (ᘁU) :=
  IsAdditiveFullProperty.of_iso P
    (leftDualIso (inferInstanceAs (ExactPairing (ᘁU) U)) (J.leftExactPairing U))
      (S.property_rightDual P hU)


include S J in
/-- The actual right dual central object, with constructed half-braiding. -/
def rightDualObj : RelativeCenter P := ⟨Z.1ᘁ, (dualLaxHalfBraiding Z).toHalfBraiding (property_leftDual S J)⟩

@[simp] lemma rightDualObj_fst : (rightDualObj Z S J).1 = Z.1ᘁ := rfl

@[simp] lemma rightDualObj_halfBraiding (U : C) (hU : P U) :
    ((rightDualObj Z S J).2.β U hU).hom = dualHalfBraidingHom Z U hU := rfl

/-- The actual underlying evaluation is a morphism in the center. -/
def rightEvaluation : rightDualObj Z S J ⊗ Z ⟶ 𝟙_ (RelativeCenter P) where
  f := ε_ Z.1 Z.1ᘁ
  comm U hU := by
    simp only [tensor_β, tensorUnit_β, Iso.trans_hom, Iso.symm_hom,
      whiskerLeftIso_hom, whiskerRightIso_hom, rightDualObj_halfBraiding (hU := hU), rightDualObj_fst]
    simp only [assoc]
    change (ε_ Z.1 Z.1ᘁ ▷ U) ≫ (λ_ U).hom ≫ (ρ_ U).inv =
      (α_ Z.1ᘁ Z.1 U).hom ≫ (Z.1ᘁ : C) ◁ (Z.2.β U hU).hom ≫
        (α_ Z.1ᘁ U Z.1).inv ≫ dualHalfBraidingHom Z U hU ▷ Z.1 ≫
          (α_ U Z.1ᘁ Z.1).hom ≫ U ◁ ε_ Z.1 Z.1ᘁ
    apply (cancel_mono (ρ_ U).hom).mp
    simp only [assoc, Iso.inv_hom_id, comp_id]
    rw [dualHalfBraidingHom_cap (hU := hU)]
    simp [dualHalfBraidingCap, ← whiskerLeft_comp_assoc]

/-- The actual underlying coevaluation is a morphism in the center. -/
def rightCoevaluation : 𝟙_ (RelativeCenter P) ⟶ Z ⊗ rightDualObj Z S J where
  f := η_ Z.1 Z.1ᘁ
  comm U hU := by
    simp only [tensor_β, tensorUnit_β, Iso.trans_hom, Iso.symm_hom,
      whiskerLeftIso_hom, whiskerRightIso_hom, rightDualObj_halfBraiding (hU := hU), rightDualObj_fst]
    simp only [assoc]
    change (η_ Z.1 Z.1ᘁ ▷ U) ≫ (α_ Z.1 Z.1ᘁ U).hom ≫
      (Z.1 ◁ dualHalfBraidingHom Z U hU) ≫ (α_ Z.1 U Z.1ᘁ).inv ≫
        (Z.2.β U hU).hom ▷ Z.1ᘁ ≫ (α_ U Z.1 Z.1ᘁ).hom =
      (λ_ U).hom ≫ (ρ_ U).inv ≫ U ◁ η_ Z.1 Z.1ᘁ
    rw [dualHalfBraidingHom_cup_assoc (hU := hU)]
    simp

/-- The two central cups and caps satisfy both triangle identities because
their actual underlying maps do and the forgetful functor is faithful. -/
def rightExactPairing : ExactPairing Z (rightDualObj Z S J) := by
  letI : (forget P).Faithful := ⟨fun h => ext P _ _ h⟩
  letI : ExactPairing ((forget P).obj Z)
      ((forget P).obj (rightDualObj Z S J)) := by
    change ExactPairing Z.1 Z.1ᘁ
    infer_instance
  apply exactPairingOfFaithful (forget P) (rightEvaluation Z S J) (rightCoevaluation Z S J)
  · simp only [forget_δ, forget_ε]
    erw [id_comp, comp_id]
    rfl
  · simp only [forget_η, forget_μ]
    erw [id_comp, comp_id]
    rfl

def rightRigidCategory : RightRigidCategory (RelativeCenter P) where
  rightDual Z := { rightDual := rightDualObj Z S J, exact := rightExactPairing Z S J }

end Paper18.Category.RelativeCenter
