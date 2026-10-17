import Paper18.Category.LocalModulesPivotalFrobenius
import Paper18.Category.SeparableModules

/-! # Actual Frobenius comultiplication from a perfect multiplication pairing -/
noncomputable section
set_option maxHeartbeats 1000000
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped MonObj
universe v u
namespace Paper18.Category.DiagonalAlgebra
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {A : C} [MonObj A] (P : ModuleBalancing.MultiplicationPairing A)

/-- The actual right transpose of multiplication. -/
def frobeniusComultiplication : A ⟶ A ⊗ A :=
  letI := P.pairing
  tensorLeftHomEquiv A A A A μ[A]

/-- The actual left transpose of multiplication. -/
def frobeniusComultiplicationLeft : A ⟶ A ⊗ A :=
  letI := P.pairing
  tensorRightHomEquiv A A A A μ[A]

lemma multiplicationCap_assoc :
    (A ◁ μ[A]) ≫ (@ExactPairing.evaluation C _ _ A A P.pairing) =
      (α_ A A A).inv ≫ (μ[A] ▷ A) ≫ (@ExactPairing.evaluation C _ _ A A P.pairing) := by
  rw [P.evaluation]
  rw [← assoc, MonObj.mul_assoc_flip]
  simp only [assoc]

/-- Associativity of the actual multiplication cap identifies its two
actual rigid transposes. -/
lemma frobeniusComultiplication_eq_left :
    frobeniusComultiplication P = frobeniusComultiplicationLeft P := by
  letI := P.pairing
  apply (tensorLeftHomEquiv A A A A).symm.injective
  change (tensorLeftHomEquiv A A A A).symm (tensorLeftHomEquiv A A A A μ[A]) = _
  rw [Equiv.symm_apply_apply]
  symm
  change A ◁ frobeniusComultiplicationLeft P ≫ (α_ A A A).inv ≫
    ε_ A A ▷ A ≫ (λ_ A).hom = μ[A]
  calc
    _ = 𝟙 (A ⊗ A) ⊗≫ ((A ⊗ A) ◁ η_ A A) ⊗≫
        ((A ◁ μ[A]) ≫ ε_ A A) ▷ A ⊗≫ 𝟙 A := by
      dsimp [frobeniusComultiplicationLeft, tensorRightHomEquiv]
      monoidal
    _ = 𝟙 (A ⊗ A) ⊗≫ ((A ⊗ A) ◁ η_ A A) ⊗≫
        ((α_ A A A).inv ≫ μ[A] ▷ A ≫ ε_ A A) ▷ A ⊗≫ 𝟙 A := by
      rw [multiplicationCap_assoc P]
    _ = μ[A] ≫ ((ρ_ A).inv ≫ A ◁ η_ A A ≫ (α_ A A A).inv ≫ ε_ A A ▷ A ≫ (λ_ A).hom) := by
      calc
        _ = (ρ_ (A ⊗ A)).inv ≫ ((A ⊗ A) ◁ η_ A A) ≫
            μ[A] ▷ (A ⊗ A) ≫ (α_ A A A).inv ≫ ε_ A A ▷ A ≫ (λ_ A).hom := by monoidal
        _ = _ := by
          rw [whisker_exchange_assoc, ← rightUnitor_inv_naturality_assoc]
    _ = μ[A] := by
      rw [ExactPairing.coevaluation_evaluation_assoc]
      monoidal

/-- The actual Frobenius comultiplication is a morphism of right modules. -/
lemma frobeniusComultiplication_right_linear :
    μ[A] ≫ frobeniusComultiplication P =
      (frobeniusComultiplication P ▷ A) ≫ (α_ A A A).hom ≫ (A ◁ μ[A]) := by
  letI := P.pairing
  calc
    _ = (λ_ (A ⊗ A)).inv ≫ η_ A A ▷ (A ⊗ A) ≫
        (α_ A A (A ⊗ A)).hom ≫ A ◁ ((A ◁ μ[A]) ≫ μ[A]) := by
      dsimp [frobeniusComultiplication, tensorLeftHomEquiv]
      rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc,
        associator_naturality_right_assoc, ← whiskerLeft_comp]
    _ = _ := by
      rw [MonObj.mul_assoc_flip]
      dsimp [frobeniusComultiplication, tensorLeftHomEquiv]
      monoidal

/-- The actual Frobenius comultiplication is a morphism of left modules. -/
lemma frobeniusComultiplication_left_linear :
    μ[A] ≫ frobeniusComultiplication P =
      (A ◁ frobeniusComultiplication P) ≫ (α_ A A A).inv ≫ (μ[A] ▷ A) := by
  letI := P.pairing
  rw [frobeniusComultiplication_eq_left]
  calc
    _ = (ρ_ (A ⊗ A)).inv ≫ (A ⊗ A) ◁ η_ A A ≫
        (α_ (A ⊗ A) A A).inv ≫ ((μ[A] ▷ A) ≫ μ[A]) ▷ A := by
      dsimp [frobeniusComultiplicationLeft, tensorRightHomEquiv]
      rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc,
        associator_inv_naturality_left_assoc, ← comp_whiskerRight]
    _ = _ := by
      rw [MonObj.mul_assoc]
      dsimp [frobeniusComultiplicationLeft, tensorRightHomEquiv]
      monoidal

end Paper18.Category.DiagonalAlgebra
