import Paper18.Category.DrinfeldBiproducts
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Kernels in the actual Drinfeld center

In a rigid category both tensor functors are right adjoints.
They therefore preserve kernels. A central morphism's underlying kernel gains
its half-braiding from the universal property, and this gives the kernel in
the center. No exactness of the center is assumed.
-/
noncomputable section
universe v u

namespace Paper18.Category.Drinfeld

open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory CategoryTheory.Limits
attribute [local instance 2000] RightRigidCategory.rightDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [LeftRigidCategory C]

instance tensorLeft_isRightAdjoint (U : C) : (tensorLeft U).IsRightAdjoint :=
  (tensorLeftAdjunction U Uᘁ).isRightAdjoint

instance tensorRight_isRightAdjoint (U : C) : (tensorRight U).IsRightAdjoint :=
  (tensorRightAdjunction (ᘁU) U).isRightAdjoint

instance whiskerLeft_mono (U : C) {A B : C} (k : A ⟶ B) [Mono k] : Mono (U ◁ k) :=
  inferInstanceAs (Mono ((tensorLeft U).map k))

variable [Preadditive C] [MonoidalPreadditive C]
  [HasKernels C] {X Y : Center C} (f : X ⟶ Y)

/-- The underlying kernel half-braiding comes from the isomorphism of the
two tensor-translated kernel diagrams. -/
def kernelHalfBraidingIso (U : C) : kernel f.f ⊗ U ≅ U ⊗ kernel f.f :=
  PreservesKernel.iso (tensorRight U) f.f ≪≫
    kernel.mapIso ((tensorRight U).map f.f) ((tensorLeft U).map f.f)
      (X.2.β U) (Y.2.β U) (f.comm U) ≪≫
        (PreservesKernel.iso (tensorLeft U) f.f).symm

@[reassoc (attr := simp)]
lemma kernelHalfBraidingIso_hom_ι (U : C) :
    (kernelHalfBraidingIso f U).hom ≫ (U ◁ kernel.ι f.f) =
      (kernel.ι f.f ▷ U) ≫ (X.2.β U).hom := by
  have h := PreservesKernel.iso_inv_ι (tensorLeft U) f.f
  change (PreservesKernel.iso (tensorLeft U) f.f).inv ≫ (U ◁ kernel.ι f.f) = _ at h
  simp only [kernelHalfBraidingIso, Iso.trans_hom, Iso.symm_hom, assoc]
  rw [h]
  simp only [kernel.mapIso, kernel.map, kernel.lift_ι,
    PreservesKernel.iso_hom]
  simpa only [assoc] using congrArg (fun k => k ≫ (X.2.β U).hom)
    (kernelComparison_comp_ι f.f (tensorRight U))

/-- Coherence of the induced half-braiding follows by cancelling the
tensor-translated kernel inclusion. -/
def kernelHalfBraiding : HalfBraiding (kernel f.f) where
  β := kernelHalfBraidingIso f
  monoidal U V := by
    apply (cancel_mono ((U ⊗ V) ◁ kernel.ι f.f)).mp
    rw [kernelHalfBraidingIso_hom_ι]
    simp only [assoc]
    rw [← associator_inv_naturality_right]
    rw [← whiskerLeft_comp_assoc, kernelHalfBraidingIso_hom_ι]
    rw [whiskerLeft_comp]
    simp only [assoc]
    rw [← associator_naturality_middle_assoc]
    rw [← comp_whiskerRight_assoc, kernelHalfBraidingIso_hom_ι]
    rw [comp_whiskerRight]
    simp only [assoc]
    rw [← associator_inv_naturality_left_assoc]
    simp only [HalfBraiding.monoidal]
  naturality {U V} g := by
    apply (cancel_mono (V ◁ kernel.ι f.f)).mp
    simp only [assoc, kernelHalfBraidingIso_hom_ι]
    rw [whisker_exchange_assoc]
    rw [← whisker_exchange g (kernel.ι f.f)]
    rw [kernelHalfBraidingIso_hom_ι_assoc]
    rw [HalfBraiding.naturality]

/-- The actual central object on the underlying kernel. -/
def kernelObj : Center C := ⟨_, kernelHalfBraiding f⟩

/-- The underlying kernel inclusion is a central morphism. -/
def kernelι : kernelObj f ⟶ X :=
  ⟨kernel.ι f.f, fun U => (kernelHalfBraidingIso_hom_ι f U).symm⟩

@[simp] lemma kernelι_f : (kernelι f).f = kernel.ι f.f := rfl

variable [Linear ℂ C] [MonoidalLinear ℂ C]

@[reassoc (attr := simp)]
lemma kernelι_condition : kernelι f ≫ f = 0 := by
  apply Center.ext
  exact kernel.condition f.f

/-- The underlying kernel's universal lift respects half-braidings by
uniqueness, so it is an actual central morphism. -/
def kernelLift {Z : Center C} (k : Z ⟶ X) (hk : k ≫ f = 0) : Z ⟶ kernelObj f where
  f := kernel.lift f.f k.f (by simpa using congrArg Center.Hom.f hk)
  comm U := by
    apply (cancel_mono (U ◁ kernel.ι f.f)).mp
    simp only [assoc, kernelObj, kernelHalfBraiding, kernelHalfBraidingIso_hom_ι]
    rw [← comp_whiskerRight_assoc, kernel.lift_ι]
    rw [← whiskerLeft_comp, kernel.lift_ι]
    exact k.comm U

@[reassoc (attr := simp)]
lemma kernelLift_ι {Z : Center C} (k : Z ⟶ X) (hk : k ≫ f = 0) :
    kernelLift f k hk ≫ kernelι f = k := by
  apply Center.ext
  exact kernel.lift_ι _ _ _

instance kernelι_mono : Mono (kernelι f) :=
  (Center.forget C).mono_of_mono_map (inferInstance : Mono (kernel.ι f.f))

/-- The actual universal kernel fork in the center. -/
def kernelIsLimit : IsLimit (KernelFork.ofι (kernelι f) (kernelι_condition f)) :=
  KernelFork.IsLimit.ofι' _ _ (fun k hk => ⟨kernelLift f k hk, kernelLift_ι f k hk⟩)

instance hasKernel : HasKernel f where
  exists_limit := ⟨⟨KernelFork.ofι (kernelι f) (kernelι_condition f), kernelIsLimit f⟩⟩

instance hasKernels : HasKernels (Center C) where
  has_limit f := hasKernel f

/-- The constructed kernel remains universal after forgetting. -/
instance forget_preservesKernel : PreservesLimit (parallelPair f 0) (Center.forget C) := by
  apply preservesLimit_of_preserves_limit_cone (kernelIsLimit f)
  exact (KernelFork.isLimitMapConeEquiv
    (KernelFork.ofι (kernelι f) (kernelι_condition f)) (Center.forget C)).symm
      (kernelIsKernel f.f)

end Paper18.Category.Drinfeld
