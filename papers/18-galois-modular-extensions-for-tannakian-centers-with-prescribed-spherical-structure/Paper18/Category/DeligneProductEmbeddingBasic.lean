import Paper18.Category.DeligneProductNondegenerateBasic
import Paper18.Category.TensorCharacters

/-! # Actual unit-factor embeddings and their Hom linear equivalences -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped TensorProduct
universe v u v' u'
namespace Paper18.Category.DeligneProduct
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]

/-- The actual pair functor `X ↦ (X,1)`. -/
def rawLeft : C ⥤ LinearTensor C D where
  obj X := ⟨X, 𝟙_ D⟩
  map f := f ⊗ₜ[ℂ] 𝟙 (𝟙_ D)
  map_id _ := rfl
  map_comp {X Y Z} f g := by
    change ((f ≫ g) ⊗ₜ[ℂ] 𝟙 (𝟙_ D)) =
      LinearTensor.compLinear (⟨X, 𝟙_ D⟩ : LinearTensor C D) ⟨Y, 𝟙_ D⟩ ⟨Z, 𝟙_ D⟩
        (f ⊗ₜ[ℂ] 𝟙 (𝟙_ D)) (g ⊗ₜ[ℂ] 𝟙 (𝟙_ D))
    rw [LinearTensor.compLinear_tmul, Category.id_comp]

/-- The actual pair functor `Y ↦ (1,Y)`. -/
def rawRight : D ⥤ LinearTensor C D where
  obj Y := ⟨𝟙_ C, Y⟩
  map f := 𝟙 (𝟙_ C) ⊗ₜ[ℂ] f
  map_id _ := rfl
  map_comp {X Y Z} f g := by
    change (𝟙 (𝟙_ C) ⊗ₜ[ℂ] (f ≫ g)) =
      LinearTensor.compLinear (⟨𝟙_ C, X⟩ : LinearTensor C D) ⟨𝟙_ C, Y⟩ ⟨𝟙_ C, Z⟩
        (𝟙 (𝟙_ C) ⊗ₜ[ℂ] f) (𝟙 (𝟙_ C) ⊗ₜ[ℂ] g)
    rw [LinearTensor.compLinear_tmul, Category.id_comp]

instance rawLeft_additive : (rawLeft (C := C) (D := D)).Additive where
  map_add := by intros; exact TensorProduct.add_tmul _ _ _
instance rawRight_additive : (rawRight (C := C) (D := D)).Additive where
  map_add := by intros; exact TensorProduct.tmul_add _ _ _
instance rawLeft_linear : (rawLeft (C := C) (D := D)).Linear ℂ where
  map_smul := by intros; exact (TensorProduct.smul_tmul' _ _ _).symm
instance rawRight_linear : (rawRight (C := C) (D := D)).Linear ℂ where
  map_smul := by intros; simp [rawRight]

section LeftHom
variable [Limits.HasKernels D] [Simple (𝟙_ D)]
  [FiniteDimensional ℂ ((𝟙_ D) ⟶ (𝟙_ D))]

/-- The actual Hom comparison for `X ↦ (X,1)` is tensor contraction with
Schur's actual scalar linear equivalence on the tensor unit. -/
def rawLeftHomEquiv (X Y : C) :
    ((rawLeft (D := D)).obj X ⟶ (rawLeft (D := D)).obj Y) ≃ₗ[ℂ] (X ⟶ Y) :=
  TensorProduct.congr (LinearEquiv.refl ℂ (X ⟶ Y)) (simpleScalarEquiv (𝟙_ D)) ≪≫ₗ
    TensorProduct.rid ℂ (X ⟶ Y)

omit [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] in
@[simp] lemma rawLeftHomEquiv_map {X Y : C} (f : X ⟶ Y) :
    rawLeftHomEquiv (D := D) X Y ((rawLeft (D := D)).map f) = f := by
  have h : simpleScalarEquiv (𝟙_ D) (𝟙 (𝟙_ D)) = 1 := by
    simpa using simpleScalarEquiv_smul_id (𝟙_ D) (1 : ℂ)
  change (TensorProduct.rid ℂ (X ⟶ Y)) (f ⊗ₜ[ℂ] simpleScalarEquiv (𝟙_ D) (𝟙 (𝟙_ D))) = f
  simp [h]

instance rawLeft_faithful : (rawLeft (C := C) (D := D)).Faithful where
  map_injective {X Y} f g h := by
    simpa using congrArg (rawLeftHomEquiv (D := D) X Y) h
instance rawLeft_full : (rawLeft (C := C) (D := D)).Full where
  map_surjective {X Y} f := ⟨rawLeftHomEquiv (D := D) X Y f,
    (rawLeftHomEquiv (D := D) X Y).injective (by simp)⟩
end LeftHom

section RightHom
variable [Limits.HasKernels C] [Simple (𝟙_ C)]
  [FiniteDimensional ℂ ((𝟙_ C) ⟶ (𝟙_ C))]

def rawRightHomEquiv (X Y : D) :
    ((rawRight (C := C)).obj X ⟶ (rawRight (C := C)).obj Y) ≃ₗ[ℂ] (X ⟶ Y) :=
  TensorProduct.congr (simpleScalarEquiv (𝟙_ C)) (LinearEquiv.refl ℂ (X ⟶ Y)) ≪≫ₗ
    TensorProduct.lid ℂ (X ⟶ Y)

omit [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D] in
@[simp] lemma rawRightHomEquiv_map {X Y : D} (f : X ⟶ Y) :
    rawRightHomEquiv (C := C) X Y ((rawRight (C := C)).map f) = f := by
  have h : simpleScalarEquiv (𝟙_ C) (𝟙 (𝟙_ C)) = 1 := by
    simpa using simpleScalarEquiv_smul_id (𝟙_ C) (1 : ℂ)
  change (TensorProduct.lid ℂ (X ⟶ Y)) (simpleScalarEquiv (𝟙_ C) (𝟙 (𝟙_ C)) ⊗ₜ[ℂ] f) = f
  simp [h]

instance rawRight_faithful : (rawRight (C := C) (D := D)).Faithful where
  map_injective {X Y} f g h := by
    simpa using congrArg (rawRightHomEquiv (C := C) X Y) h
instance rawRight_full : (rawRight (C := C) (D := D)).Full where
  map_surjective {X Y} f := ⟨rawRightHomEquiv (C := C) X Y f,
    (rawRightHomEquiv (C := C) X Y).injective (by simp)⟩
end RightHom

end Paper18.Category.DeligneProduct
