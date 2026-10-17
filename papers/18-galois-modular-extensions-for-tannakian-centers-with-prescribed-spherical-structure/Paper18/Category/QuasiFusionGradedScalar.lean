import Paper18.Category.PointedLinear

/-! # Actual scalar maps on homogeneous convolution triples -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
namespace Paper18.Category.QuasiFusion
variable {A : Type} [Fintype A] [AddGroup A]
open GradedObject.Monoidal

local instance scalarBaseMonoidal : MonoidalCategory (GradedObject A (FGModuleCat ℂ)) :=
  GradedObject.monoidalCategory

/-- The actual universal map from a left-associated convolution triple. -/
def tripleDesc (X Y Z : PointedVec A) {k : A} {Q : FGModuleCat ℂ}
    (f : ∀ a b c (_h : a + b + c = k), (X a ⊗ Y b) ⊗ Z c ⟶ Q) :
    ((X ⊗ Y) ⊗ Z) k ⟶ Q :=
  GradedObject.mapBifunctor₁₂BifunctorDesc
    (F₁₂ := curriedTensor (FGModuleCat ℂ)) (G := curriedTensor (FGModuleCat ℂ))
    (ρ₁₂ := GradedObject.Monoidal.ρ₁₂) (X₁ := X) (X₂ := Y) (X₃ := Z) f

@[simp]
lemma inclusion_tripleDesc (X Y Z : PointedVec A) {k : A} {Q : FGModuleCat ℂ}
    (f : ∀ a b c (_h : a + b + c = k), (X a ⊗ Y b) ⊗ Z c ⟶ Q)
    (a b c : A) (h : a + b + c = k) :
    ιTensorObj₃' X Y Z a b c k h ≫ tripleDesc X Y Z f = f a b c h :=
  GradedObject.ι_mapBifunctor₁₂BifunctorDesc
    (F₁₂ := curriedTensor (FGModuleCat ℂ)) (G := curriedTensor (FGModuleCat ℂ))
    (ρ₁₂ := GradedObject.Monoidal.ρ₁₂) (X₁ := X) (X₂ := Y) (X₃ := Z) f a b c h

/-- Multiplication by a degree-dependent scalar on every actual triple summand. -/
def tripleScalar (r : A → A → A → ℂ) (X Y Z : PointedVec A) :
    (X ⊗ Y) ⊗ Z ⟶ (X ⊗ Y) ⊗ Z :=
  fun k => tripleDesc X Y Z (fun a b c h => r a b c • ιTensorObj₃' X Y Z a b c k h)

@[simp]
lemma inclusion_tripleScalar (r : A → A → A → ℂ) (X Y Z : PointedVec A)
    (a b c k : A) (h : a + b + c = k) :
    ιTensorObj₃' X Y Z a b c k h ≫ tripleScalar r X Y Z k =
      r a b c • ιTensorObj₃' X Y Z a b c k h := by
  exact inclusion_tripleDesc X Y Z _ a b c h

lemma inclusion_tripleScalar_assoc (r : A → A → A → ℂ) (X Y Z : PointedVec A)
    (a b c k : A) (h : a + b + c = k) {Q : FGModuleCat ℂ}
    (q : ((X ⊗ Y) ⊗ Z) k ⟶ Q) :
    ιTensorObj₃' X Y Z a b c k h ≫ tripleScalar r X Y Z k ≫ q =
      r a b c • (ιTensorObj₃' X Y Z a b c k h ≫ q) := by
  rw [← assoc, inclusion_tripleScalar, Linear.smul_comp]

lemma tripleScalar_comp (r s : A → A → A → ℂ) (X Y Z : PointedVec A) :
    tripleScalar r X Y Z ≫ tripleScalar s X Y Z =
      tripleScalar (fun a b c => r a b c * s a b c) X Y Z := by
  apply GradedObject.hom_ext
  intro k
  apply tensorObj₃'_ext (X₁ := X) (X₂ := Y) (X₃ := Z)
  intro a b c h
  change ιTensorObj₃' X Y Z a b c k h ≫
    (tripleScalar r X Y Z k ≫ tripleScalar s X Y Z k) = _
  simp only [inclusion_tripleScalar_assoc, inclusion_tripleScalar, smul_smul]

lemma tripleScalar_one (X Y Z : PointedVec A) :
    tripleScalar (fun _ _ _ => 1) X Y Z = 𝟙 ((X ⊗ Y) ⊗ Z) := by
  apply GradedObject.hom_ext
  intro k
  apply tensorObj₃'_ext (X₁ := X) (X₂ := Y) (X₃ := Z)
  intro a b c h
  change ιTensorObj₃' X Y Z a b c k h ≫ tripleScalar (fun _ _ _ => 1) X Y Z k =
    ιTensorObj₃' X Y Z a b c k h ≫ 𝟙 _
  simp only [inclusion_tripleScalar, one_smul, comp_id]

lemma tripleScalar_naturality (r : A → A → A → ℂ)
    {X Y Z X' Y' Z' : PointedVec A} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    ((f ⊗ₘ g) ⊗ₘ h) ≫ tripleScalar r X' Y' Z' =
      tripleScalar r X Y Z ≫ ((f ⊗ₘ g) ⊗ₘ h) := by
  apply GradedObject.hom_ext
  intro k
  apply tensorObj₃'_ext (X₁ := X) (X₂ := Y) (X₃ := Z)
  intro a b c hi
  change ιTensorObj₃' X Y Z a b c k hi ≫
      (GradedObject.Monoidal.tensorHom (GradedObject.Monoidal.tensorHom f g) h k ≫
        tripleScalar r X' Y' Z' k) =
    ιTensorObj₃' X Y Z a b c k hi ≫
      (tripleScalar r X Y Z k ≫
        GradedObject.Monoidal.tensorHom (GradedObject.Monoidal.tensorHom f g) h k)
  rw [ιTensorObj₃'_tensorHom_assoc, inclusion_tripleScalar]
  rw [inclusion_tripleScalar_assoc, ιTensorObj₃'_tensorHom,
    Linear.comp_smul]

/-- Every unit-valued degree function yields an actual convolution-triple isomorphism. -/
def tripleScalarIso (r : A → A → A → ℂˣ) (X Y Z : PointedVec A) :
    (X ⊗ Y) ⊗ Z ≅ (X ⊗ Y) ⊗ Z where
  hom := tripleScalar (fun a b c => (r a b c : ℂ)) X Y Z
  inv := tripleScalar (fun a b c => ((r a b c)⁻¹ : ℂˣ)) X Y Z
  hom_inv_id := by
    rw [tripleScalar_comp]
    have hc : (fun a b c => (r a b c : ℂ) * (((r a b c)⁻¹ : ℂˣ) : ℂ)) =
        (fun _ _ _ => (1 : ℂ)) := by
      funext a b c
      simp
    rw [hc, tripleScalar_one]
  inv_hom_id := by
    rw [tripleScalar_comp]
    have hc : (fun a b c => (((r a b c)⁻¹ : ℂˣ) : ℂ) * (r a b c : ℂ)) =
        (fun _ _ _ => (1 : ℂ)) := by
      funext a b c
      simp
    rw [hc, tripleScalar_one]

end Paper18.Category.QuasiFusion
