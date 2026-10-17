import Paper18.Category.SphericalizationKernelEssential
import Paper18.Category.SphericalizationKernelMonoidalBasic
import Paper18.Category.SphericalizationKernelTensorPoints

/-! # The actual braided tensor comparison on the sphericalization kernel -/
noncomputable section
set_option maxHeartbeats 1600000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal
open scoped TensorProduct
universe v u
namespace Paper18.Category.Sphericalized
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasFiniteBiproducts C] [HasKernels C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]

omit [HasFiniteBiproducts C] [HasKernels C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)] in
lemma unitHomInvolution_tensor (X Y : Sphericalized C)
    (f : 𝟙_ C ⟶ X.obj.obj) (g : 𝟙_ C ⟶ Y.obj.obj) :
    unitHomInvolution (X ⊗ Y) (unitPointTensor f g) =
      unitPointTensor (unitHomInvolution X f) (unitHomInvolution Y g) := by
  apply (cancel_mono (X ⊗ Y).obj.phi.hom).mp
  change (ε (doubleDualFunctor C) ≫ (doubleDualFunctor C).map (unitPointTensor f g) ≫
      (X ⊗ Y).obj.phi.inv) ≫ (X ⊗ Y).obj.phi.hom =
    unitPointTensor (unitHomInvolution X f) (unitHomInvolution Y g) ≫
      ((X.obj.phi.hom ⊗ₘ Y.obj.phi.hom) ≫ μ (doubleDualFunctor C) X.obj.obj Y.obj.obj)
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [unitPointTensor, Category.assoc]
  rw [tensorHom_comp_tensorHom_assoc]
  change ε (doubleDualFunctor C) ≫ (doubleDualFunctor C).map (unitPointTensor f g) =
    (λ_ (𝟙_ C)).inv ≫
      (((ε (doubleDualFunctor C) ≫ (doubleDualFunctor C).map f ≫ X.obj.phi.inv) ≫ X.obj.phi.hom) ⊗ₘ
        ((ε (doubleDualFunctor C) ≫ (doubleDualFunctor C).map g ≫ Y.obj.phi.inv) ≫ Y.obj.phi.hom)) ≫
      μ (doubleDualFunctor C) X.obj.obj Y.obj.obj
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simpa only [unitPointTensor, Category.assoc] using
    (unitPointTensor_map (doubleDualFunctor C) f g).symm

def kernelTensorLinearEquiv (X Y : Kernel (C := C)) :
    (UnitHomVector X.obj ⊗[ℂ] UnitHomVector Y.obj) ≃ₗ[ℂ] UnitHomVector (X.obj ⊗ Y.obj) :=
  (TensorProduct.congr (unitHomCoordinate X.obj).symm (unitHomCoordinate Y.obj).symm).trans
    ((unitPointTensorEquiv X.property Y.property).trans (unitHomCoordinate (X.obj ⊗ Y.obj)))

@[simp] lemma kernelTensorLinearEquiv_tmul (X Y : Kernel (C := C))
    (x : UnitHomVector X.obj) (y : UnitHomVector Y.obj) :
    kernelTensorLinearEquiv X Y (x ⊗ₜ[ℂ] y) =
      unitHomCoordinate (X.obj ⊗ Y.obj)
        (unitPointTensor ((unitHomCoordinate X.obj).symm x) ((unitHomCoordinate Y.obj).symm y)) := rfl

def kernelTensorIso (X Y : Kernel (C := C)) :
    kernelRepresentation.obj X ⊗ kernelRepresentation.obj Y ≅ kernelRepresentation.obj (X ⊗ Y) :=
  Action.mkIso (kernelTensorLinearEquiv X Y).toFGModuleCatIso (fun g => by
    rcases RepresentationZ2.eq_one_or_generator g with rfl | rfl
    · simp
    · apply ModuleCat.hom_ext
      apply TensorProduct.ext
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      change kernelTensorLinearEquiv X Y
          (((unitHomRepresentation.obj X.obj).ρ RepresentationZ2.generator x) ⊗ₜ[ℂ]
            ((unitHomRepresentation.obj Y.obj).ρ RepresentationZ2.generator y)) =
        (unitHomRepresentation.obj (X.obj ⊗ Y.obj)).ρ RepresentationZ2.generator
          (kernelTensorLinearEquiv X Y (x ⊗ₜ[ℂ] y))
      rw [kernelTensorLinearEquiv_tmul, kernelTensorLinearEquiv_tmul,
        unitHomRepresentation_generator]
      have hx := unitHomRepresentation_generator X.obj ((unitHomCoordinate X.obj).symm x)
      have hy := unitHomRepresentation_generator Y.obj ((unitHomCoordinate Y.obj).symm y)
      rw [LinearEquiv.apply_symm_apply] at hx hy
      rw [hx, hy, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply,
        unitHomInvolution_tensor])

def kernelUnitLinearEquiv : ℂ ≃ₗ[ℂ] UnitHomVector (𝟙_ (Sphericalized C)) :=
  (unitScalarEquiv (C := C)).symm.trans (unitHomCoordinate (𝟙_ (Sphericalized C)))

def kernelUnitIso : 𝟙_ (FDRep ℂ RepresentationZ2.H) ≅ kernelRepresentation.obj (𝟙_ (Kernel (C := C))) :=
  Action.mkIso (kernelUnitLinearEquiv (C := C)).toFGModuleCatIso (fun g => by
    rcases RepresentationZ2.eq_one_or_generator g with rfl | rfl
    · simp
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change unitHomCoordinate (𝟙_ (Sphericalized C)) ((unitScalarEquiv (C := C)).symm x) =
        (unitHomRepresentation.obj (𝟙_ (Sphericalized C))).ρ RepresentationZ2.generator
          (unitHomCoordinate (𝟙_ (Sphericalized C)) ((unitScalarEquiv (C := C)).symm x))
      rw [unitHomRepresentation_generator, unitHomInvolution_unit])

lemma kernelUnitIso_hom_apply (c : ℂ) :
    (kernelUnitIso (C := C)).hom.hom.hom c =
      unitHomCoordinate (𝟙_ (Sphericalized C)) (c • 𝟙 (𝟙_ C)) := by
  rfl

def kernelRepresentationCoreMonoidal : (kernelRepresentation (C := C)).CoreMonoidal where
  εIso := kernelUnitIso
  μIso := kernelTensorIso
  μIso_hom_natural_left {X Y} f Z := by
    apply Action.Hom.ext
    apply FGModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro z
    simp only [Action.comp_hom, Action.whiskerRight_hom]
    change unitHomCoordinate (Y.obj ⊗ Z.obj)
        (unitPointTensor ((unitHomCoordinate Y.obj).symm
          (unitHomCoordinate Y.obj ((unitHomCoordinate X.obj).symm x ≫ f.hom)))
            ((unitHomCoordinate Z.obj).symm z)) =
      unitHomCoordinate (Y.obj ⊗ Z.obj)
        ((unitHomCoordinate (X.obj ⊗ Z.obj)).symm
          (unitHomCoordinate (X.obj ⊗ Z.obj)
            (unitPointTensor ((unitHomCoordinate X.obj).symm x)
              ((unitHomCoordinate Z.obj).symm z))) ≫ (f.hom ⊗ₘ 𝟙 Z.obj.obj.obj))
    simp only [LinearEquiv.symm_apply_apply]
    congr 1
    simp only [unitPointTensor, Category.assoc, tensorHom_comp_tensorHom, Category.comp_id]
  μIso_hom_natural_right {X Y} Z f := by
    apply Action.Hom.ext
    apply FGModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro z
    apply LinearMap.ext
    intro x
    simp only [Action.comp_hom, Action.whiskerLeft_hom]
    change unitHomCoordinate (Z.obj ⊗ Y.obj)
        (unitPointTensor ((unitHomCoordinate Z.obj).symm z)
          ((unitHomCoordinate Y.obj).symm
            (unitHomCoordinate Y.obj ((unitHomCoordinate X.obj).symm x ≫ f.hom)))) =
      unitHomCoordinate (Z.obj ⊗ Y.obj)
        ((unitHomCoordinate (Z.obj ⊗ X.obj)).symm
          (unitHomCoordinate (Z.obj ⊗ X.obj)
            (unitPointTensor ((unitHomCoordinate Z.obj).symm z)
              ((unitHomCoordinate X.obj).symm x))) ≫ (𝟙 Z.obj.obj.obj ⊗ₘ f.hom))
    simp only [LinearEquiv.symm_apply_apply]
    congr 1
    simp only [unitPointTensor, Category.assoc, tensorHom_comp_tensorHom, Category.comp_id]
  associativity X Y Z := by
    apply Action.Hom.ext
    apply FGModuleCat.hom_ext
    apply TensorProduct.ext_threefold
    intro x y z
    change unitHomCoordinate (X.obj ⊗ (Y.obj ⊗ Z.obj))
        ((unitHomCoordinate ((X.obj ⊗ Y.obj) ⊗ Z.obj)).symm
          (unitHomCoordinate ((X.obj ⊗ Y.obj) ⊗ Z.obj)
            (unitPointTensor ((unitHomCoordinate (X.obj ⊗ Y.obj)).symm
              (unitHomCoordinate (X.obj ⊗ Y.obj)
                (unitPointTensor ((unitHomCoordinate X.obj).symm x)
                  ((unitHomCoordinate Y.obj).symm y)))) ((unitHomCoordinate Z.obj).symm z))) ≫
          (α_ X.obj.obj.obj Y.obj.obj.obj Z.obj.obj.obj).hom) =
      unitHomCoordinate (X.obj ⊗ (Y.obj ⊗ Z.obj))
        (unitPointTensor ((unitHomCoordinate X.obj).symm x)
          ((unitHomCoordinate (Y.obj ⊗ Z.obj)).symm
            (unitHomCoordinate (Y.obj ⊗ Z.obj)
              (unitPointTensor ((unitHomCoordinate Y.obj).symm y)
                ((unitHomCoordinate Z.obj).symm z)))))
    simp only [LinearEquiv.symm_apply_apply, unitPointTensor_assoc]
  left_unitality X := by
    apply Action.Hom.ext
    apply FGModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro c
    apply LinearMap.ext
    intro x
    change c • x = unitHomCoordinate X.obj
      ((unitHomCoordinate ((𝟙_ (Sphericalized C)) ⊗ X.obj)).symm
        (unitHomCoordinate ((𝟙_ (Sphericalized C)) ⊗ X.obj)
          (unitPointTensor ((unitHomCoordinate (𝟙_ (Sphericalized C))).symm
            ((kernelUnitIso (C := C)).hom.hom.hom c)) ((unitHomCoordinate X.obj).symm x))) ≫
        (λ_ X.obj.obj.obj).hom)
    rw [kernelUnitIso_hom_apply]
    simp only [LinearEquiv.symm_apply_apply]
    simp [unitPointTensor, tensorHom_def]
  right_unitality X := by
    apply Action.Hom.ext
    apply FGModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro c
    change c • x = unitHomCoordinate X.obj
      ((unitHomCoordinate (X.obj ⊗ (𝟙_ (Sphericalized C)))).symm
        (unitHomCoordinate (X.obj ⊗ (𝟙_ (Sphericalized C)))
          (unitPointTensor ((unitHomCoordinate X.obj).symm x)
            ((unitHomCoordinate (𝟙_ (Sphericalized C))).symm
              ((kernelUnitIso (C := C)).hom.hom.hom c)))) ≫ (ρ_ X.obj.obj.obj).hom)
    rw [kernelUnitIso_hom_apply]
    simp only [LinearEquiv.symm_apply_apply]
    simp [unitPointTensor, tensorHom_def, unitors_inv_equal]

instance kernelRepresentation_monoidal : (kernelRepresentation (C := C)).Monoidal :=
  kernelRepresentationCoreMonoidal.toMonoidal

instance kernelRepresentation_braided : (kernelRepresentation (C := C)).Braided where
  toMonoidal := kernelRepresentation_monoidal
  braided X Y := by
    apply Action.Hom.ext
    apply FGModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change unitHomCoordinate (Y.obj ⊗ X.obj)
        ((unitHomCoordinate (X.obj ⊗ Y.obj)).symm
          (unitHomCoordinate (X.obj ⊗ Y.obj)
            (unitPointTensor ((unitHomCoordinate X.obj).symm x)
              ((unitHomCoordinate Y.obj).symm y))) ≫ (β_ X.obj.obj.obj Y.obj.obj.obj).hom) =
      unitHomCoordinate (Y.obj ⊗ X.obj)
        (unitPointTensor ((unitHomCoordinate Y.obj).symm y) ((unitHomCoordinate X.obj).symm x))
    rw [LinearEquiv.symm_apply_apply, unitPointTensor_braiding]

end Paper18.Category.Sphericalized
