import Paper18.Category.SphericalizationKernelMonoidal
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-! # The actual braided tensor equivalence of the sphericalization kernel with Rep(C₂) -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal
universe v u
namespace Paper18.Category.Sphericalized
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [CategoryTheory.Limits.HasFiniteBiproducts C] [CategoryTheory.Limits.HasKernels C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]

instance kernelEquivalence_functor_additive : (kernelEquivalence (C := C)).functor.Additive :=
  kernelRepresentation_additive
instance kernelEquivalence_functor_linear : (kernelEquivalence (C := C)).functor.Linear ℂ :=
  kernelRepresentation_linear
instance kernelEquivalence_functor_braided : (kernelEquivalence (C := C)).functor.Braided :=
  kernelRepresentation_braided

instance kernelEquivalence_inverse_monoidal : (kernelEquivalence (C := C)).inverse.Monoidal :=
  (kernelEquivalence (C := C)).inverseMonoidal
instance kernelEquivalence_isMonoidal : (kernelEquivalence (C := C)).IsMonoidal := inferInstance

instance kernelEquivalence_unit_monoidal :
    NatTrans.IsMonoidal (kernelEquivalence (C := C)).unitIso.hom :=
  inferInstanceAs (NatTrans.IsMonoidal (kernelEquivalence (C := C)).unit)
instance kernelEquivalence_counit_monoidal :
    NatTrans.IsMonoidal (kernelEquivalence (C := C)).counitIso.hom :=
  inferInstanceAs (NatTrans.IsMonoidal (kernelEquivalence (C := C)).counit)

instance kernelEquivalence_inverse_additive : (kernelEquivalence (C := C)).inverse.Additive :=
  Equivalence.inverse_additive (kernelEquivalence (C := C))
instance kernelEquivalence_inverse_linear : (kernelEquivalence (C := C)).inverse.Linear ℂ :=
  Equivalence.inverseLinear ℂ (kernelEquivalence (C := C))

instance kernelEquivalence_inverse_braided : (kernelEquivalence (C := C)).inverse.Braided where
  toMonoidal := kernelEquivalence_inverse_monoidal
  braided X Y := by
    let e := kernelEquivalence (C := C)
    letI : NatTrans.IsMonoidal e.counitIso.symm.hom :=
      inferInstanceAs (NatTrans.IsMonoidal e.counitIso.inv)
    letI : (e.inverse ⋙ e.functor).LaxBraided := Functor.LaxBraided.ofNatIso e.counitIso.symm
    have h := Functor.LaxBraided.braided (F := e.inverse ⋙ e.functor) X Y
    apply e.functor.map_injective
    apply (cancel_epi (μ e.functor (e.inverse.obj X) (e.inverse.obj Y))).1
    simp only [CategoryTheory.Functor.map_comp]
    rw [Functor.LaxBraided.braided_assoc]
    simpa only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.comp_obj,
      Functor.LaxMonoidal.comp_μ, Category.assoc] using h

end Paper18.Category.Sphericalized
