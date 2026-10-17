import Paper18.Category.SphericalizationKernelUnitSums

/-! # The actual tensor product of unit-point spaces of unit sums -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators TensorProduct
universe v u
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasFiniteBiproducts C] [HasKernels C] [Simple (𝟙_ C)]
  [FiniteDimensional ℂ (𝟙_ C ⟶ 𝟙_ C)]

/-- Tensoring actual maps out of the unit, with its canonical diagonal. -/
def unitPointTensor {X Y : C} (f : 𝟙_ C ⟶ X) (g : 𝟙_ C ⟶ Y) : 𝟙_ C ⟶ X ⊗ Y :=
  (λ_ (𝟙_ C)).inv ≫ (f ⊗ₘ g)

def unitPointTensorBilinear (X Y : C) :
    (𝟙_ C ⟶ X) →ₗ[ℂ] (𝟙_ C ⟶ Y) →ₗ[ℂ] (𝟙_ C ⟶ X ⊗ Y) where
  toFun f :=
    { toFun := unitPointTensor f
      map_add' g h := by simp [unitPointTensor, tensorHom_def]
      map_smul' c g := by simp [unitPointTensor, tensorHom_def] }
  map_add' f g := by ext h; simp [unitPointTensor, tensorHom_def]
  map_smul' c f := by ext h; simp [unitPointTensor, tensorHom_def]

def unitPointTensorMap (X Y : C) :
    ((𝟙_ C ⟶ X) ⊗[ℂ] (𝟙_ C ⟶ Y)) →ₗ[ℂ] (𝟙_ C ⟶ X ⊗ Y) :=
  TensorProduct.lift (unitPointTensorBilinear X Y)

omit [HasFiniteBiproducts C] [HasKernels C] [Simple (𝟙_ C)]
  [FiniteDimensional ℂ (𝟙_ C ⟶ 𝟙_ C)] in
@[simp] lemma unitPointTensorMap_tmul {X Y : C} (f : 𝟙_ C ⟶ X) (g : 𝟙_ C ⟶ Y) :
    unitPointTensorMap X Y (f ⊗ₜ[ℂ] g) = unitPointTensor f g := rfl

namespace IsUnitSum

def projection {X : C} (hX : IsUnitSum X) (a : Fin hX.length) : X ⟶ 𝟙_ C :=
  hX.decomposition.hom ≫ biproduct.π (fun _ : Fin hX.length => 𝟙_ C) a

def inclusion {X : C} (hX : IsUnitSum X) (a : Fin hX.length) : 𝟙_ C ⟶ X :=
  biproduct.ι (fun _ : Fin hX.length => 𝟙_ C) a ≫ hX.decomposition.inv

omit [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [Simple (𝟙_ C)] [FiniteDimensional ℂ (𝟙_ C ⟶ 𝟙_ C)] in
lemma resolution {X : C} (hX : IsUnitSum X) :
    ∑ a : Fin hX.length, hX.projection a ≫ hX.inclusion a = 𝟙 X := by
  calc
    _ = hX.decomposition.hom ≫ (∑ a : Fin hX.length,
        biproduct.π (fun _ : Fin hX.length => 𝟙_ C) a ≫
          biproduct.ι (fun _ : Fin hX.length => 𝟙_ C) a) ≫ hX.decomposition.inv := by
      simp only [projection, inclusion, Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
    _ = 𝟙 X := by rw [biproduct.total]; simp

omit [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
lemma point_resolution {X : C} (hX : IsUnitSum X) (f : 𝟙_ C ⟶ X) :
    ∑ a : Fin hX.length, unitScalarEquiv (f ≫ hX.projection a) • hX.inclusion a = f := by
  have ht (a : Fin hX.length) : unitScalarEquiv (f ≫ hX.projection a) • hX.inclusion a =
      f ≫ hX.projection a ≫ hX.inclusion a := by
    calc
      _ = (unitScalarEquiv (f ≫ hX.projection a) • 𝟙 (𝟙_ C)) ≫ hX.inclusion a := by simp
      _ = _ := by rw [unitScalarEquiv_spec, Category.assoc]
  simp only [ht, ← Preadditive.comp_sum, hX.resolution, Category.comp_id]

end IsUnitSum

omit [HasFiniteBiproducts C] in
lemma unitPointTensor_scalar (f g : 𝟙_ C ⟶ 𝟙_ C) :
    unitScalarEquiv (unitPointTensor f g ≫ (λ_ (𝟙_ C)).hom) =
      unitScalarEquiv f * unitScalarEquiv g := by
  obtain ⟨c, rfl⟩ := CategoryTheory.endomorphism_simple_eq_smul_id ℂ f
  obtain ⟨d, rfl⟩ := CategoryTheory.endomorphism_simple_eq_smul_id ℂ g
  simp [unitPointTensor, tensorHom_def, smul_smul, mul_comm]

def unitPointTensorCoefficient {X Y : C} (hX : IsUnitSum X) (hY : IsUnitSum Y)
    (a : Fin hX.length) (b : Fin hY.length) : (𝟙_ C ⟶ X ⊗ Y) →ₗ[ℂ] ℂ :=
  (unitScalarEquiv (C := C)).toLinearMap ∘ₗ
    CategoryTheory.Linear.rightComp ℂ (𝟙_ C)
      ((hX.projection a ⊗ₘ hY.projection b) ≫ (λ_ (𝟙_ C)).hom)

def unitPointTensorInverse {X Y : C} (hX : IsUnitSum X) (hY : IsUnitSum Y) :
    (𝟙_ C ⟶ X ⊗ Y) →ₗ[ℂ] ((𝟙_ C ⟶ X) ⊗[ℂ] (𝟙_ C ⟶ Y)) :=
  ∑ p : Fin hX.length × Fin hY.length,
    (LinearMap.toSpanSingleton ℂ _ (hX.inclusion p.1 ⊗ₜ[ℂ] hY.inclusion p.2)).comp
      (unitPointTensorCoefficient hX hY p.1 p.2)

omit [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
lemma unitPointTensorInverse_apply {X Y : C} (hX : IsUnitSum X) (hY : IsUnitSum Y)
    (g : 𝟙_ C ⟶ X ⊗ Y) :
    unitPointTensorInverse hX hY g = ∑ p : Fin hX.length × Fin hY.length,
      unitScalarEquiv (g ≫ (hX.projection p.1 ⊗ₘ hY.projection p.2) ≫ (λ_ (𝟙_ C)).hom) •
        (hX.inclusion p.1 ⊗ₜ[ℂ] hY.inclusion p.2) := by
  simp [unitPointTensorInverse, unitPointTensorCoefficient]

lemma unitPointTensorInverse_tmul {X Y : C} (hX : IsUnitSum X) (hY : IsUnitSum Y)
    (f : 𝟙_ C ⟶ X) (g : 𝟙_ C ⟶ Y) :
    unitPointTensorInverse hX hY (unitPointTensor f g) = f ⊗ₜ[ℂ] g := by
  rw [unitPointTensorInverse_apply]
  have hc (a : Fin hX.length) (b : Fin hY.length) :
      unitScalarEquiv (unitPointTensor f g ≫ (hX.projection a ⊗ₘ hY.projection b) ≫
        (λ_ (𝟙_ C)).hom) =
      unitScalarEquiv (f ≫ hX.projection a) * unitScalarEquiv (g ≫ hY.projection b) := by
    rw [unitPointTensor, Category.assoc, tensorHom_comp_tensorHom_assoc]
    simpa only [unitPointTensor, Category.assoc] using
      unitPointTensor_scalar (C := C) (f ≫ hX.projection a) (g ≫ hY.projection b)
  simp only [hc, Fintype.sum_prod_type]
  calc
    _ = (∑ a : Fin hX.length, unitScalarEquiv (f ≫ hX.projection a) • hX.inclusion a) ⊗ₜ[ℂ]
        (∑ b : Fin hY.length, unitScalarEquiv (g ≫ hY.projection b) • hY.inclusion b) := by
      simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum, TensorProduct.smul_tmul',
        TensorProduct.tmul_smul, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [mul_comm]
    _ = f ⊗ₜ[ℂ] g := by rw [hX.point_resolution, hY.point_resolution]

lemma unitPointTensorMap_inverse {X Y : C} (hX : IsUnitSum X) (hY : IsUnitSum Y)
    (g : 𝟙_ C ⟶ X ⊗ Y) :
    unitPointTensorMap X Y (unitPointTensorInverse hX hY g) = g := by
  rw [unitPointTensorInverse_apply, map_sum]
  simp only [map_smul, unitPointTensorMap_tmul]
  have ht (a : Fin hX.length) (b : Fin hY.length) :
      unitScalarEquiv (g ≫ (hX.projection a ⊗ₘ hY.projection b) ≫ (λ_ (𝟙_ C)).hom) •
          unitPointTensor (hX.inclusion a) (hY.inclusion b) =
        g ≫ ((hX.projection a ≫ hX.inclusion a) ⊗ₘ (hY.projection b ≫ hY.inclusion b)) := by
    calc
      _ = ((unitScalarEquiv (g ≫ (hX.projection a ⊗ₘ hY.projection b) ≫
          (λ_ (𝟙_ C)).hom) • 𝟙 (𝟙_ C)) ≫ (λ_ (𝟙_ C)).inv) ≫
            (hX.inclusion a ⊗ₘ hY.inclusion b) := by
        simp only [unitPointTensor, Linear.smul_comp, Category.id_comp]
      _ = _ := by
        rw [unitScalarEquiv_spec]
        simp only [Category.assoc, Iso.hom_inv_id_assoc, tensorHom_comp_tensorHom]
  simp only [ht, Fintype.sum_prod_type, ← Preadditive.comp_sum,
    ← CategoryTheory.tensor_sum, hY.resolution, MonoidalCategory.tensorHom_id]
  rw [← sum_whiskerRight, hX.resolution, id_whiskerRight, Category.comp_id]

/-- The canonical map on actual unit points is an actual linear isomorphism
for actual finite unit sums. Both inverse laws follow from their categorical
inclusion/projection resolutions. -/
def unitPointTensorEquiv {X Y : C} (hX : IsUnitSum X) (hY : IsUnitSum Y) :
    ((𝟙_ C ⟶ X) ⊗[ℂ] (𝟙_ C ⟶ Y)) ≃ₗ[ℂ] (𝟙_ C ⟶ X ⊗ Y) where
  toLinearMap := unitPointTensorMap X Y
  invFun := unitPointTensorInverse hX hY
  left_inv x := by
    have hi : (unitPointTensorInverse hX hY).comp (unitPointTensorMap X Y) = LinearMap.id := by
      apply TensorProduct.ext
      apply LinearMap.ext
      intro f
      apply LinearMap.ext
      intro g
      exact unitPointTensorInverse_tmul hX hY f g
    exact LinearMap.congr_fun hi x
  right_inv := unitPointTensorMap_inverse hX hY

end Paper18.Category
