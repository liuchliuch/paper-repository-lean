import Paper18.Category.RelativeCenterBiproducts
import Paper18.Category.DrinfeldKernels
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

namespace Paper18.Category.RelativeCenter

open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory CategoryTheory.Limits
attribute [local instance 2000] RightRigidCategory.rightDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [LeftRigidCategory C]
  {P : ObjectProperty C} [P.IsMonoidal]

variable [Preadditive C] [MonoidalPreadditive C]
  [HasKernels C] {X Y : RelativeCenter P} (f : X ⟶ Y)

/-- The underlying kernel half-braiding comes from the isomorphism of the
two tensor-translated kernel diagrams. -/
def kernelHalfBraidingIso (U : C) (hU : P U) : kernel f.f ⊗ U ≅ U ⊗ kernel f.f :=
  PreservesKernel.iso (tensorRight U) f.f ≪≫
    kernel.mapIso ((tensorRight U).map f.f) ((tensorLeft U).map f.f)
      (X.2.β U hU) (Y.2.β U hU) (f.comm U hU) ≪≫
        (PreservesKernel.iso (tensorLeft U) f.f).symm

@[reassoc (attr := simp)]
lemma kernelHalfBraidingIso_hom_ι (U : C) (hU : P U) :
    (kernelHalfBraidingIso f U hU).hom ≫ (U ◁ kernel.ι f.f) =
      (kernel.ι f.f ▷ U) ≫ (X.2.β U hU).hom := by
  have h := PreservesKernel.iso_inv_ι (tensorLeft U) f.f
  change (PreservesKernel.iso (tensorLeft U) f.f).inv ≫ (U ◁ kernel.ι f.f) = _ at h
  simp only [kernelHalfBraidingIso, Iso.trans_hom, Iso.symm_hom, assoc]
  rw [h]
  simp only [kernel.mapIso, kernel.map, kernel.lift_ι,
    PreservesKernel.iso_hom]
  simpa only [assoc] using congrArg (fun k => k ≫ (X.2.β U hU).hom)
    (kernelComparison_comp_ι f.f (tensorRight U))

/-- Coherence of the induced half-braiding follows by cancelling the
tensor-translated kernel inclusion. -/
def kernelHalfBraiding : RelativeHalfBraiding P (kernel f.f) where
  β := kernelHalfBraidingIso f
  monoidal U V hU hV := by
    apply (cancel_mono ((U ⊗ V) ◁ kernel.ι f.f)).mp
    rw [kernelHalfBraidingIso_hom_ι (hU := ObjectProperty.prop_tensor hU hV)]
    simp only [assoc]
    rw [← associator_inv_naturality_right]
    rw [← whiskerLeft_comp_assoc, kernelHalfBraidingIso_hom_ι (hU := hV)]
    rw [whiskerLeft_comp]
    simp only [assoc]
    rw [← associator_naturality_middle_assoc]
    rw [← comp_whiskerRight_assoc, kernelHalfBraidingIso_hom_ι (hU := hU)]
    rw [comp_whiskerRight]
    simp only [assoc]
    rw [← associator_inv_naturality_left_assoc]
    rw [X.2.monoidal U V hU hV]
  naturality {U V} hU hV g := by
    apply (cancel_mono (V ◁ kernel.ι f.f)).mp
    simp only [assoc, kernelHalfBraidingIso_hom_ι (hU := hV)]
    rw [whisker_exchange_assoc]
    rw [← whisker_exchange g (kernel.ι f.f)]
    rw [kernelHalfBraidingIso_hom_ι_assoc (hU := hU)]
    rw [X.2.naturality hU hV g]

/-- The actual central object on the underlying kernel. -/
def kernelObj : RelativeCenter P := ⟨_, kernelHalfBraiding f⟩

/-- The underlying kernel inclusion is a central morphism. -/
def kernelι : kernelObj f ⟶ X :=
  ⟨kernel.ι f.f, fun U hU => (kernelHalfBraidingIso_hom_ι f U hU).symm⟩

@[simp] lemma kernelι_f : (kernelι f).f = kernel.ι f.f := rfl

variable [Linear ℂ C] [MonoidalLinear ℂ C]

@[reassoc (attr := simp)]
lemma kernelι_condition : kernelι f ≫ f = 0 := by
  apply ext P
  exact kernel.condition f.f

/-- The underlying kernel's universal lift respects half-braidings by
uniqueness, so it is an actual central morphism. -/
def kernelLift {Z : RelativeCenter P} (k : Z ⟶ X) (hk : k ≫ f = 0) : Z ⟶ kernelObj f where
  f := kernel.lift f.f k.f (by simpa using congrArg Hom.f hk)
  comm U hU := by
    apply (cancel_mono (U ◁ kernel.ι f.f)).mp
    simp only [assoc, kernelObj, kernelHalfBraiding, kernelHalfBraidingIso_hom_ι (hU := hU)]
    rw [← comp_whiskerRight_assoc, kernel.lift_ι]
    rw [← whiskerLeft_comp, kernel.lift_ι]
    exact k.comm U hU

@[reassoc (attr := simp)]
lemma kernelLift_ι {Z : RelativeCenter P} (k : Z ⟶ X) (hk : k ≫ f = 0) :
    kernelLift f k hk ≫ kernelι f = k := by
  apply ext P
  exact kernel.lift_ι _ _ _

instance kernelι_mono : Mono (kernelι f) :=
  (forget P).mono_of_mono_map (inferInstance : Mono (kernel.ι f.f))

/-- The actual universal kernel fork in the center. -/
def kernelIsLimit : IsLimit (KernelFork.ofι (kernelι f) (kernelι_condition f)) :=
  KernelFork.IsLimit.ofι' _ _ (fun k hk => ⟨kernelLift f k hk, kernelLift_ι f k hk⟩)

instance hasKernel : HasKernel f where
  exists_limit := ⟨⟨KernelFork.ofι (kernelι f) (kernelι_condition f), kernelIsLimit f⟩⟩

instance hasKernels : HasKernels (RelativeCenter P) where
  has_limit f := hasKernel f

/-- The constructed kernel remains universal after forgetting. -/
instance forget_preservesKernel : PreservesLimit (parallelPair f 0) (forget P) := by
  apply preservesLimit_of_preserves_limit_cone (kernelIsLimit f)
  exact (KernelFork.isLimitMapConeEquiv
    (KernelFork.ofι (kernelι f) (kernelι_condition f)) (forget P)).symm
      (kernelIsKernel f.f)

end Paper18.Category.RelativeCenter
