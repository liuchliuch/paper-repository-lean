import Paper18.Category.QuasiFusionMonoidal

/-! # Actual bilinear convolution after the associator twist -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
namespace Paper18.Category.QuasiFusion
variable {A : Type} [Fintype A] [AddGroup A]
local instance linearBaseMonoidal : MonoidalCategory (GradedObject A (FGModuleCat ℂ)) :=
  GradedObject.monoidalCategory

variable (r : A → A → A → ℂˣ)
  (hr : ∀ a b c d, r b c d * r a (b + c) d * r a b c =
    r (a + b) c d * r a b (c + d)) (h₀ : ∀ a c, r a 0 c = 1)

def scalarMonoidalPreadditive :
    letI := scalarMonoidalCategory r hr h₀
    MonoidalPreadditive (PointedVec A) := by
  have h₁ := @MonoidalPreadditive.whiskerLeft_zero (PointedVec A) _ _
    (inferInstance : MonoidalCategory (PointedVec A)) inferInstance
  have h₂ := @MonoidalPreadditive.zero_whiskerRight (PointedVec A) _ _
    (inferInstance : MonoidalCategory (PointedVec A)) inferInstance
  have h₃ := @MonoidalPreadditive.whiskerLeft_add (PointedVec A) _ _
    (inferInstance : MonoidalCategory (PointedVec A)) inferInstance
  have h₄ := @MonoidalPreadditive.add_whiskerRight (PointedVec A) _ _
    (inferInstance : MonoidalCategory (PointedVec A)) inferInstance
  letI := scalarMonoidalCategory r hr h₀
  exact ⟨h₁, h₂, h₃, h₄⟩

def scalarMonoidalLinear :
    letI := scalarMonoidalCategory r hr h₀
    letI := scalarMonoidalPreadditive r hr h₀
    MonoidalLinear ℂ (PointedVec A) := by
  have h₁ := @MonoidalLinear.whiskerLeft_smul ℂ _ (PointedVec A) _ _ _
    (inferInstance : MonoidalCategory (PointedVec A)) inferInstance inferInstance
  have h₂ := @MonoidalLinear.smul_whiskerRight ℂ _ (PointedVec A) _ _ _
    (inferInstance : MonoidalCategory (PointedVec A)) inferInstance inferInstance
  letI := scalarMonoidalCategory r hr h₀
  letI := scalarMonoidalPreadditive r hr h₀
  exact ⟨h₁, h₂⟩

end Paper18.Category.QuasiFusion
