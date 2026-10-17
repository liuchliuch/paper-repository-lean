import Paper18.Category.PointedBasic

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory

namespace Paper18.Category.PointedVec

variable {A : Type} [Fintype A] [AddGroup A]

open GradedObject.Monoidal

instance monoidalPreadditive : MonoidalPreadditive (PointedVec A) where
  whiskerLeft_zero := by
    intro X Y Z
    apply GradedObject.hom_ext
    intro k
    apply tensorObj_ext
    intro i j h
    change ιTensorObj X Y i j k h ≫ GradedObject.Monoidal.whiskerLeft X 0 k =
      ιTensorObj X Y i j k h ≫ 0
    rw [ι_tensorHom]
    simp
  zero_whiskerRight := by
    intro X Y Z
    apply GradedObject.hom_ext
    intro k
    apply tensorObj_ext
    intro i j h
    change ιTensorObj Y X i j k h ≫ GradedObject.Monoidal.whiskerRight 0 X k =
      ιTensorObj Y X i j k h ≫ 0
    rw [ι_tensorHom]
    simp
  whiskerLeft_add := by
    intro X Y Z f g
    apply GradedObject.hom_ext
    intro k
    apply tensorObj_ext
    intro i j h
    change ιTensorObj X Y i j k h ≫ GradedObject.Monoidal.whiskerLeft X (f + g) k =
      ιTensorObj X Y i j k h ≫
        (GradedObject.Monoidal.whiskerLeft X f k + GradedObject.Monoidal.whiskerLeft X g k)
    rw [Preadditive.comp_add, ι_tensorHom, ι_tensorHom, ι_tensorHom]
    change (𝟙 (X i) ⊗ₘ (f j + g j)) ≫ _ = _
    rw [MonoidalPreadditive.tensor_add, Preadditive.add_comp]
    simp only [GradedObject.categoryOfGradedObjects_id]
  add_whiskerRight := by
    intro X Y Z f g
    apply GradedObject.hom_ext
    intro k
    apply tensorObj_ext
    intro i j h
    change ιTensorObj Y X i j k h ≫ GradedObject.Monoidal.whiskerRight (f + g) X k =
      ιTensorObj Y X i j k h ≫
        (GradedObject.Monoidal.whiskerRight f X k + GradedObject.Monoidal.whiskerRight g X k)
    rw [Preadditive.comp_add, ι_tensorHom, ι_tensorHom, ι_tensorHom]
    change ((f i + g i) ⊗ₘ 𝟙 (X j)) ≫ _ = _
    rw [MonoidalPreadditive.add_tensor, Preadditive.add_comp]
    simp only [GradedObject.categoryOfGradedObjects_id]

instance monoidalLinear : MonoidalLinear ℂ (PointedVec A) where
  whiskerLeft_smul := by
    intro X Y Z r f
    apply GradedObject.hom_ext
    intro k
    apply tensorObj_ext
    intro i j h
    change ιTensorObj X Y i j k h ≫ GradedObject.Monoidal.whiskerLeft X (r • f) k =
      ιTensorObj X Y i j k h ≫ (r • GradedObject.Monoidal.whiskerLeft X f k)
    rw [Linear.comp_smul, ι_tensorHom, ι_tensorHom]
    change (𝟙 (X i) ⊗ₘ (r • f j)) ≫ _ = _
    simp [MonoidalCategory.tensorHom_def]
  smul_whiskerRight := by
    intro r Y Z f X
    apply GradedObject.hom_ext
    intro k
    apply tensorObj_ext
    intro i j h
    change ιTensorObj Y X i j k h ≫ GradedObject.Monoidal.whiskerRight (r • f) X k =
      ιTensorObj Y X i j k h ≫ (r • GradedObject.Monoidal.whiskerRight f X k)
    rw [Linear.comp_smul, ι_tensorHom, ι_tensorHom]
    change ((r • f i) ⊗ₘ 𝟙 (X j)) ≫ _ = _
    simp [MonoidalCategory.tensorHom_def]

end Paper18.Category.PointedVec
