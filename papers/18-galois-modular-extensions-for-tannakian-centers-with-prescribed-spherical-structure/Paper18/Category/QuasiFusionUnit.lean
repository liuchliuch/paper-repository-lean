import Paper18.Category.QuasiFusionAssociator

/-! # Actual normalized scalar associators satisfy the unit triangle -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
namespace Paper18.Category.QuasiFusion
variable {A : Type} [Fintype A] [AddGroup A]
open GradedObject.Monoidal
local instance unitBaseMonoidal : MonoidalCategory (GradedObject A (FGModuleCat ℂ)) :=
  GradedObject.monoidalCategory

lemma tripleScalar_middle_unit (r : A → A → A → ℂ)
    (hr : ∀ a c, r a 0 c = 1) (X Y : PointedVec A) :
    tripleScalar r X (𝟙_ (PointedVec A)) Y = 𝟙 ((X ⊗ (𝟙_ (PointedVec A))) ⊗ Y) := by
  apply GradedObject.hom_ext
  intro k
  apply tensorObj₃'_ext (X₁ := X) (X₂ := (𝟙_ (PointedVec A))) (X₃ := Y)
  intro a b c h
  change ιTensorObj₃' X (𝟙_ (PointedVec A)) Y a b c k h ≫
    tripleScalar r X (𝟙_ (PointedVec A)) Y k =
      ιTensorObj₃' X (𝟙_ (PointedVec A)) Y a b c k h ≫ 𝟙 _
  rw [inclusion_tripleScalar, comp_id]
  by_cases hb : b = 0
  · subst b
    rw [hr, one_smul]
  · have hu : IsZero ((𝟙_ (PointedVec A)) b) := (isInitialTensorUnitApply b hb).isZero
    have ht : 𝟙 ((X a ⊗ (𝟙_ (PointedVec A)) b) ⊗ Y c) = 0 := by
      rw [← MonoidalCategory.id_tensorHom_id, ← MonoidalCategory.id_tensorHom_id,
        (IsZero.iff_id_eq_zero _).mp hu, MonoidalPreadditive.tensor_zero,
        MonoidalPreadditive.zero_tensor]
    have hi : ιTensorObj₃' X (𝟙_ (PointedVec A)) Y a b c k h = 0 := by
      calc
        _ = 𝟙 _ ≫ ιTensorObj₃' X (𝟙_ (PointedVec A)) Y a b c k h := by rw [id_comp]
        _ = _ := by rw [ht, zero_comp]
    rw [hi, smul_zero]

lemma scalarAssociator_triangle (r : A → A → A → ℂˣ)
    (hr : ∀ a c, r a 0 c = 1) (X Y : PointedVec A) :
    (scalarAssociator r X (𝟙_ (PointedVec A)) Y).hom ≫ X ◁ (λ_ Y).hom =
      (ρ_ X).hom ▷ Y := by
  change (tripleScalar (fun a b c => (r a b c : ℂ)) X (𝟙_ (PointedVec A)) Y ≫
    (α_ X (𝟙_ (PointedVec A)) Y).hom) ≫ X ◁ (λ_ Y).hom = _
  rw [tripleScalar_middle_unit]
  · rw [id_comp, MonoidalCategory.triangle]
  · intro a c
    rw [hr, Units.val_one]

end Paper18.Category.QuasiFusion
