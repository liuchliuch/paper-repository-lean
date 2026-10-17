import Paper18.Category.QuasiFusionAssociator

/-! # The actual scalar-cocycle pentagon on convolution tensors -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
namespace Paper18.Category.QuasiFusion
variable {A : Type} [Fintype A] [AddGroup A]
open GradedObject.Monoidal

local instance pentagonBaseMonoidal : MonoidalCategory (GradedObject A (FGModuleCat ℂ)) :=
  GradedObject.monoidalCategory

set_option maxHeartbeats 1000000 in
lemma scalarAssociator_pentagon_inv (r : A → A → A → ℂˣ)
    (hr : ∀ a b c d, r b c d * r a (b + c) d * r a b c =
      r (a + b) c d * r a b (c + d)) (W X Y Z : PointedVec A) :
    W ◁ (scalarAssociator r X Y Z).inv ≫ (scalarAssociator r W (X ⊗ Y) Z).inv ≫
      (scalarAssociator r W X Y).inv ▷ Z =
        (scalarAssociator r W X (Y ⊗ Z)).inv ≫ (scalarAssociator r (W ⊗ X) Y Z).inv := by
  apply GradedObject.hom_ext
  intro j
  apply tensorObj₄_ext (X₁ := W) (X₂ := X) (X₃ := Y) (X₄ := Z)
  intro a b c d h
  change ιTensorObj₄ W X Y Z a b c d j h ≫
      (GradedObject.Monoidal.tensorHom (𝟙 W) (scalarAssociator r X Y Z).inv j ≫
        (scalarAssociator r W (GradedObject.Monoidal.tensorObj X Y) Z).inv j ≫
        GradedObject.Monoidal.tensorHom (scalarAssociator r W X Y).inv (𝟙 Z) j) =
    ιTensorObj₄ W X Y Z a b c d j h ≫
      ((scalarAssociator r W X (GradedObject.Monoidal.tensorObj Y Z)).inv j ≫
        (scalarAssociator r (GradedObject.Monoidal.tensorObj W X) Y Z).inv j)
  dsimp only [PointedVec.instMonoidalCategory, GradedObject.monoidalCategory]
  conv_lhs =>
    rw [ιTensorObj₄_eq W X Y Z a b c d j h _ rfl, assoc, ι_tensorHom_assoc]
    dsimp only [PointedVec.id_apply, GradedObject.categoryOfGradedObjects_id, id_eq, eq_mpr_eq_cast, cast_eq]
    rw [MonoidalCategory.id_tensorHom, ← MonoidalCategory.whiskerLeft_comp_assoc,
      inclusion_scalarAssociator_inv]
    simp only [MonoidalLinear.whiskerLeft_smul, Linear.smul_comp, Linear.comp_smul, assoc]
    rw [ιTensorObj₃'_eq X Y Z b c d _ rfl _ rfl,
      MonoidalCategory.whiskerLeft_comp_assoc, MonoidalCategory.whiskerLeft_comp_assoc]
    rw [← ιTensorObj₃_eq_assoc W (GradedObject.Monoidal.tensorObj X Y) Z a (b + c) d j
        (by simp only [← add_assoc, h]) (b + c + d) rfl
          ((scalarAssociator r W (GradedObject.Monoidal.tensorObj X Y) Z).inv j ≫
            GradedObject.Monoidal.tensorHom (scalarAssociator r W X Y).inv (𝟙 Z) j),
      inclusion_scalarAssociator_inv_assoc]
    simp only [Linear.smul_comp, Linear.comp_smul, assoc]
    rw [ιTensorObj₃'_eq_assoc W (GradedObject.Monoidal.tensorObj X Y) Z a (b + c) d j
        (by simp only [← add_assoc, h]) (a + b + c) (by rw [add_assoc]), ι_tensorHom]
    dsimp only [id_eq, eq_mpr_eq_cast, PointedVec.id_apply, GradedObject.categoryOfGradedObjects_id]
    rw [MonoidalCategory.tensorHom_id, whisker_assoc_symm_assoc, Iso.hom_inv_id_assoc,
      ← MonoidalCategory.comp_whiskerRight_assoc, ← MonoidalCategory.comp_whiskerRight_assoc,
      ← ιTensorObj₃_eq W X Y a b c _ rfl _ rfl, inclusion_scalarAssociator_inv]
    simp only [MonoidalLinear.smul_whiskerRight, Linear.smul_comp, Linear.comp_smul, assoc]
    rw [MonoidalCategory.comp_whiskerRight_assoc, MonoidalCategory.pentagon_inv_assoc]
  conv_rhs =>
    rw [ιTensorObj₄_eq W X Y Z a b c d _ _ _ rfl,
      ιTensorObj₃_eq X Y Z b c d _ rfl _ rfl, assoc,
      MonoidalCategory.whiskerLeft_comp_assoc,
      ← ιTensorObj₃_eq_assoc W X (GradedObject.Monoidal.tensorObj Y Z) a b (c + d) j
        (by rw [← add_assoc, h]) (b + c + d) (by rw [add_assoc]),
      inclusion_scalarAssociator_inv_assoc]
    simp only [Linear.smul_comp, Linear.comp_smul, assoc]
    rw [associator_inv_naturality_right_assoc,
      ιTensorObj₃'_eq_assoc W X (GradedObject.Monoidal.tensorObj Y Z) a b (c + d) j
        (by rw [← add_assoc, h]) _ rfl, whisker_exchange_assoc,
      ← ιTensorObj₃_eq_assoc (GradedObject.Monoidal.tensorObj W X) Y Z (a + b) c d j h _ rfl,
      inclusion_scalarAssociator_inv]
    simp only [Linear.smul_comp, Linear.comp_smul, assoc]
    rw [whiskerRight_tensor_assoc, Iso.hom_inv_id_assoc,
      ιTensorObj₃'_eq (GradedObject.Monoidal.tensorObj W X) Y Z (a + b) c d j h _ rfl,
      ← MonoidalCategory.comp_whiskerRight_assoc,
      ← ιTensorObj₃'_eq W X Y a b c _ rfl _ rfl]
  simp only [smul_smul]
  congr 1
  have hi := congrArg (fun z : ℂˣ => ((z⁻¹ : ℂˣ) : ℂ)) (hr a b c d)
  simpa only [mul_inv_rev, Units.val_mul, mul_comm, mul_left_comm, mul_assoc] using hi

lemma scalarAssociator_pentagon (r : A → A → A → ℂˣ)
    (hr : ∀ a b c d, r b c d * r a (b + c) d * r a b c =
      r (a + b) c d * r a b (c + d)) (W X Y Z : PointedVec A) :
    (scalarAssociator r W X Y).hom ▷ Z ≫ (scalarAssociator r W (X ⊗ Y) Z).hom ≫
      W ◁ (scalarAssociator r X Y Z).hom =
        (scalarAssociator r (W ⊗ X) Y Z).hom ≫ (scalarAssociator r W X (Y ⊗ Z)).hom := by
  let L : ((W ⊗ X) ⊗ Y) ⊗ Z ≅ W ⊗ (X ⊗ (Y ⊗ Z)) :=
    whiskerRightIso (scalarAssociator r W X Y) Z ≪≫
      scalarAssociator r W (X ⊗ Y) Z ≪≫ whiskerLeftIso W (scalarAssociator r X Y Z)
  let R : ((W ⊗ X) ⊗ Y) ⊗ Z ≅ W ⊗ (X ⊗ (Y ⊗ Z)) :=
    scalarAssociator r (W ⊗ X) Y Z ≪≫ scalarAssociator r W X (Y ⊗ Z)
  have hi : L.inv = R.inv := by
    exact scalarAssociator_pentagon_inv r hr W X Y Z
  have he : L.symm = R.symm := Iso.ext hi
  have hm := congrArg (fun e => e.inv) he
  change L.hom = R.hom at hm
  exact hm

end Paper18.Category.QuasiFusion
