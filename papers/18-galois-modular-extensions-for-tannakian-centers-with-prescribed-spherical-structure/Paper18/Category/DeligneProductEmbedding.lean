import Paper18.Category.DeligneProductEmbeddingMonoidal

/-! # Actual fully faithful braided tensor embeddings into the Deligne product -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped TensorProduct
universe v u v' u'
namespace Paper18.Category.DeligneProduct
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]

/-- An actual external pair object of the actual additive linear tensor product. -/
def externalObject (X : C) (Y : D) : DeligneProduct C D :=
  (Mat_.embedding (LinearTensor C D)).obj ⟨X, Y⟩

/-- External pair Hom spaces are the actual tensor products of actual factor Hom spaces. -/
def externalHomEquiv (X X' : C) (Y Y' : D) :
    (externalObject X Y ⟶ externalObject X' Y') ≃ₗ[ℂ]
      ((X ⟶ X') ⊗[ℂ] (Y ⟶ Y')) where
  toFun f := f PUnit.unit PUnit.unit
  invFun f _ _ := f
  left_inv f := by ext ⟨⟩ ⟨⟩; rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]

/-- The actual left unit-factor embedding `X ↦ X ⊠ 1`. -/
def left : C ⥤ DeligneProduct C D := rawLeft ⋙ Mat_.embedding _
/-- The actual right unit-factor embedding `Y ↦ 1 ⊠ Y`. -/
def right : D ⥤ DeligneProduct C D := rawRight ⋙ Mat_.embedding _

@[simp] lemma left_obj (X : C) : (left (D := D)).obj X = externalObject X (𝟙_ D) := rfl
@[simp] lemma right_obj (Y : D) : (right (C := C)).obj Y = externalObject (𝟙_ C) Y := rfl
@[simp] lemma left_map_apply {X Y : C} (f : X ⟶ Y) :
    (left (D := D)).map f PUnit.unit PUnit.unit = f ⊗ₜ[ℂ] 𝟙 (𝟙_ D) := rfl
@[simp] lemma right_map_apply {X Y : D} (f : X ⟶ Y) :
    (right (C := C)).map f PUnit.unit PUnit.unit = 𝟙 (𝟙_ C) ⊗ₜ[ℂ] f := rfl

instance left_additive : (left (C := C) (D := D)).Additive := by
  dsimp [left]; infer_instance
instance right_additive : (right (C := C) (D := D)).Additive := by
  dsimp [right]; infer_instance
instance left_linear : (left (C := C) (D := D)).Linear ℂ := by
  dsimp [left]; infer_instance
instance right_linear : (right (C := C) (D := D)).Linear ℂ := by
  dsimp [right]; infer_instance
instance left_monoidal : (left (C := C) (D := D)).Monoidal := by
  dsimp [left]; infer_instance
instance right_monoidal : (right (C := C) (D := D)).Monoidal := by
  dsimp [right]; infer_instance
instance left_braided [BraidedCategory C] [BraidedCategory D] :
    (left (C := C) (D := D)).Braided := by dsimp [left]; infer_instance
instance right_braided [BraidedCategory C] [BraidedCategory D] :
    (right (C := C) (D := D)).Braided := by dsimp [right]; infer_instance

/-- The canonical comparison for actual external pair tensor products. -/
def externalTensorIso (X X' : C) (Y Y' : D) :
    externalObject X Y ⊗ externalObject X' Y' ≅ externalObject (X ⊗ X') (Y ⊗ Y') :=
  LinearMat.embeddingTensorIso _ _

/-- Tensoring the two actual unit-factor images recovers the actual external pair. -/
def leftTensorRightIso (X : C) (Y : D) :
    (left (D := D)).obj X ⊗ (right (C := C)).obj Y ≅ externalObject X Y :=
  externalTensorIso X (𝟙_ C) (𝟙_ D) Y ≪≫
    (Mat_.embedding (LinearTensor C D)).mapIso
      (LinearTensor.isoOfPair (ρ_ X) (λ_ Y))

lemma left_right_centralizes [BraidedCategory C] [BraidedCategory D] (X : C) (Y : D) :
    Centralizes ((left (D := D)).obj X) ((right (C := C)).obj Y) :=
  (raw_centralizes (centralizes_unit_right X) (centralizes_unit_left Y)).map
    (Mat_.embedding (LinearTensor C D))

section LeftHom
variable [Limits.HasKernels D] [Simple (𝟙_ D)]
  [FiniteDimensional ℂ ((𝟙_ D) ⟶ (𝟙_ D))]

def leftHomEquiv (X Y : C) :
    ((left (D := D)).obj X ⟶ (left (D := D)).obj Y) ≃ₗ[ℂ] (X ⟶ Y) :=
  externalHomEquiv X Y (𝟙_ D) (𝟙_ D) ≪≫ₗ rawLeftHomEquiv (D := D) X Y

@[simp] lemma leftHomEquiv_map {X Y : C} (f : X ⟶ Y) :
    leftHomEquiv (D := D) X Y ((left (D := D)).map f) = f :=
  rawLeftHomEquiv_map f

instance left_full : (left (C := C) (D := D)).Full := by dsimp [left]; infer_instance
instance left_faithful : (left (C := C) (D := D)).Faithful := by dsimp [left]; infer_instance
end LeftHom

section RightHom
variable [Limits.HasKernels C] [Simple (𝟙_ C)]
  [FiniteDimensional ℂ ((𝟙_ C) ⟶ (𝟙_ C))]

def rightHomEquiv (X Y : D) :
    ((right (C := C)).obj X ⟶ (right (C := C)).obj Y) ≃ₗ[ℂ] (X ⟶ Y) :=
  externalHomEquiv (𝟙_ C) (𝟙_ C) X Y ≪≫ₗ rawRightHomEquiv (C := C) X Y

@[simp] lemma rightHomEquiv_map {X Y : D} (f : X ⟶ Y) :
    rightHomEquiv (C := C) X Y ((right (C := C)).map f) = f :=
  rawRightHomEquiv_map f

instance right_full : (right (C := C) (D := D)).Full := by dsimp [right]; infer_instance
instance right_faithful : (right (C := C) (D := D)).Faithful := by dsimp [right]; infer_instance
end RightHom

end Paper18.Category.DeligneProduct
