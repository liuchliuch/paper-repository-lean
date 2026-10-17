import Paper18.Category.LinearMatMonoidal

/-! # Linearity and the strong monoidal singleton embedding -/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u
namespace Paper18.Category.LinearMat
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [MonoidalCategory C] [MonoidalPreadditive C]

instance monoidalPreadditive : MonoidalPreadditive (Mat_ C) where
  whiskerLeft_zero := by
    intro X Y Z
    ext p q
    simp only [whiskerLeft_apply]
    exact MonoidalPreadditive.tensor_zero _
  zero_whiskerRight := by
    intro X Y Z
    ext p q
    simp only [whiskerRight_apply]
    exact MonoidalPreadditive.zero_tensor _
  whiskerLeft_add := by
    intro X Y Z f g
    ext p q
    simp only [whiskerLeft_apply, Mat_.add_apply]
    exact MonoidalPreadditive.tensor_add _ _ _
  add_whiskerRight := by
    intro X Y Z f g
    ext p q
    simp only [whiskerRight_apply, Mat_.add_apply]
    exact MonoidalPreadditive.add_tensor _ _ _

instance [Linear ℂ C] [MonoidalLinear ℂ C] : MonoidalLinear ℂ (Mat_ C) where
  whiskerLeft_smul := by
    intros X Y Z r f
    ext p q
    change (𝟙 X) p.1 q.1 ⊗ₘ (r • f p.2 q.2) = r • ((𝟙 X) p.1 q.1 ⊗ₘ f p.2 q.2)
    simp [tensorHom_def]
  smul_whiskerRight := by
    intros r X Y f Z
    ext p q
    change (r • f p.1 q.1) ⊗ₘ (𝟙 Z) p.2 q.2 = r • (f p.1 q.1 ⊗ₘ (𝟙 Z) p.2 q.2)
    simp [tensorHom_def]

/-- The singleton embedding's tensor comparison is the actual one-by-one
identity matrix, with different actual finite index sets on the two sides. -/
def embeddingTensorIso (X Y : C) :
    (Mat_.embedding C).obj X ⊗ (Mat_.embedding C).obj Y ≅
      (Mat_.embedding C).obj (X ⊗ Y) where
  hom _ _ := 𝟙 _
  inv _ _ := 𝟙 _
  hom_inv_id := by ext ⟨⟨⟩,⟨⟩⟩ ⟨⟨⟩,⟨⟩⟩; simp [Mat_.comp_apply, Mat_.id_apply, Fintype.sum_prod_type]
  inv_hom_id := by ext ⟨⟩ ⟨⟩; simp [Mat_.comp_apply, Mat_.id_apply, Fintype.sum_prod_type]

/-- The original category embeds by a genuine strong monoidal functor. -/
def embeddingCoreMonoidal : (Mat_.embedding C).CoreMonoidal where
  εIso := Iso.refl _
  μIso := embeddingTensorIso
  μIso_hom_natural_left := by
    intro X Y f Z
    ext ⟨⟨⟩,⟨⟩⟩ ⟨⟩
    simp [embeddingTensorIso, Mat_.comp_apply, Mat_.embedding, tensorHom_def,
      monoidalCategory, monoidalStruct, tensorMap, indexEquivHom, Fintype.sum_prod_type]
  μIso_hom_natural_right := by
    intro X Y Z f
    ext ⟨⟨⟩,⟨⟩⟩ ⟨⟩
    simp [embeddingTensorIso, Mat_.comp_apply, Mat_.embedding, tensorHom_def,
      monoidalCategory, monoidalStruct, tensorMap, indexEquivHom, Fintype.sum_prod_type]
  associativity := by
    intro X Y Z
    ext ⟨⟨⟨⟩,⟨⟩⟩,⟨⟩⟩ ⟨⟩
    simp [embeddingTensorIso, Mat_.comp_apply, Mat_.embedding, tensorHom_def,
      monoidalCategory, monoidalStruct, tensorMap, associatorIso, indexEquivHom, Fintype.sum_prod_type]
  left_unitality := by
    intro X
    ext ⟨⟨⟩,⟨⟩⟩ ⟨⟩
    simp [embeddingTensorIso, Mat_.comp_apply, Mat_.embedding, tensorHom_def,
      monoidalStruct, tensorMap, leftUnitorIso, indexEquivHom, Mat_.id_apply, Fintype.sum_prod_type]
  right_unitality := by
    intro X
    ext ⟨⟨⟩,⟨⟩⟩ ⟨⟩
    simp [embeddingTensorIso, Mat_.comp_apply, Mat_.embedding, tensorHom_def,
      monoidalStruct, tensorMap, rightUnitorIso, indexEquivHom, Mat_.id_apply, Fintype.sum_prod_type]

instance embeddingMonoidal : (Mat_.embedding C).Monoidal := embeddingCoreMonoidal.toMonoidal

end Paper18.Category.LinearMat
