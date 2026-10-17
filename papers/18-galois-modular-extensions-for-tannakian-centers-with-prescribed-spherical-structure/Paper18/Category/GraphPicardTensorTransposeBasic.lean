import Paper18.Category.GraphPicardCapTranspose

/-! # Tensor pairings for arbitrary specified exact pairings -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u
namespace Paper18.Category.GraphPicard
variable {E : Type u} [Category.{v} E] [MonoidalCategory E]

/-- The actual nested cap, in its original tensor order. -/
def nestedCap {U' V' P Q : E} (e : U' ⊗ P ⟶ 𝟙_ E) (f : V' ⊗ Q ⟶ 𝟙_ E) :
    (V' ⊗ U') ⊗ (P ⊗ Q) ⟶ 𝟙_ E :=
  (α_ V' U' (P ⊗ Q)).hom ≫
    V' ◁ ((α_ U' P Q).inv ≫ e ▷ Q ≫ (λ_ Q).hom) ≫ f

variable (U U' V V' : E) [ExactPairing U U'] [ExactPairing V V']

/-- A tensor pairing with the supplied duals, without any target rigid structure. -/
def specifiedTensorPairing : ExactPairing (U ⊗ V) (V' ⊗ U') where
  coevaluation' := η_ U U' ≫
    U ◁ ((λ_ U').inv ≫ η_ V V' ▷ U' ≫ (α_ V V' U').hom) ≫
      (α_ U V (V' ⊗ U')).inv
  evaluation' := nestedCap (ε_ U U') (ε_ V V')
  evaluation_coevaluation' := by
    calc
      _ = 𝟙 (𝟙_ E ⊗ (U ⊗ V)) ⊗≫ η_ U U' ▷ U ▷ V ⊗≫
          U ◁ (η_ V V' ▷ ((U' ⊗ U) ⊗ V) ≫
            (V ⊗ V') ◁ (ε_ U U' ▷ V)) ⊗≫
          U ◁ V ◁ ε_ V V' ⊗≫ 𝟙 ((U ⊗ V) ⊗ 𝟙_ E) := by
        dsimp [nestedCap]
        monoidal
      _ = 𝟙 (𝟙_ E ⊗ (U ⊗ V)) ⊗≫
          (η_ U U' ▷ U ⊗≫ U ◁ ε_ U U') ▷ V ⊗≫
          U ◁ (η_ V V' ▷ V ⊗≫ V ◁ ε_ V V') ⊗≫
          𝟙 ((U ⊗ V) ⊗ 𝟙_ E) := by
        rw [← whisker_exchange]
        monoidal
      _ = _ := by
        rw [ExactPairing.evaluation_coevaluation'', ExactPairing.evaluation_coevaluation'']
        monoidal
  coevaluation_evaluation' := by
    calc
      _ = 𝟙 ((V' ⊗ U') ⊗ 𝟙_ E) ⊗≫
          V' ◁ U' ◁ η_ U U' ⊗≫
          V' ◁ ((U' ⊗ U) ◁ η_ V V' ≫
            ε_ U U' ▷ (V ⊗ V')) ▷ U' ⊗≫
          ε_ V V' ▷ V' ▷ U' ⊗≫
          𝟙 (𝟙_ E ⊗ (V' ⊗ U')) := by
        dsimp [nestedCap]
        monoidal
      _ = 𝟙 ((V' ⊗ U') ⊗ 𝟙_ E) ⊗≫
          V' ◁ (U' ◁ η_ U U' ⊗≫ ε_ U U' ▷ U') ⊗≫
          (V' ◁ η_ V V' ⊗≫ ε_ V V' ▷ V') ▷ U' ⊗≫
          𝟙 (𝟙_ E ⊗ (V' ⊗ U')) := by
        rw [whisker_exchange]
        monoidal
      _ = _ := by
        rw [ExactPairing.coevaluation_evaluation'', ExactPairing.coevaluation_evaluation'']
        monoidal

end Paper18.Category.GraphPicard
