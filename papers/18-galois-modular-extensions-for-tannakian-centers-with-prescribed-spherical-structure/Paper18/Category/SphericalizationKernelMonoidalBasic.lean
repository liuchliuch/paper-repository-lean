import Paper18.Category.SphericalizationKernelFull

/-! # The inherited actual braided tensor structure on the forgetful kernel -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u
namespace Paper18.Category.Sphericalized
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [CategoryTheory.Limits.HasFiniteBiproducts C]

instance kernelProperty_isMonoidal : (kernelProperty (C := C)).IsMonoidal where
  prop_unit := IsUnitSum.unit
  prop_tensor _ _ hX hY := hX.tensor hY

instance kernelInclusion_monoidal : (kernelInclusion (C := C)).Monoidal :=
  inferInstanceAs (kernelProperty (C := C)).ι.Monoidal

instance kernelInclusion_braided : (kernelInclusion (C := C)).Braided :=
  inferInstanceAs (kernelProperty (C := C)).ι.Braided

instance kernel_symmetric : SymmetricCategory (Kernel (C := C)) where
  symmetry X Y := by
    change (β_ X.obj Y.obj).hom ≫ (β_ Y.obj X.obj).hom = 𝟙 _
    exact (centralizes_map_iff (forget (C := C)) X.obj Y.obj).mp
      (unitSum_mem_mugerCenter X.property Y.obj.obj.obj (Set.mem_univ _))

end Paper18.Category.Sphericalized
