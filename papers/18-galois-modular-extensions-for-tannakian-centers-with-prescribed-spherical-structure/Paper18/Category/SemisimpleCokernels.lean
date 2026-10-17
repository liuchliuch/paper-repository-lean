import Paper18.Category.SemisimpleSplitting
import Paper18.Category.SemisimpleComplement
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-!
# Cokernels in finite semisimple complex-linear categories

The complement of the kernel of a morphism maps monomorphically into its
target. Splitting that monomorphism gives an actual cokernel, with its
universal property. Thus an actual finite semisimple skeleton supplies all
cokernels, coequalizers, and finite colimits.
-/

noncomputable section
open Classical CategoryTheory CategoryTheory.Limits
universe v u w
namespace Paper18.Category

section KernelComplement
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasKernels C]
  {X Y : C} (f : X ⟶ Y) (s : SplitMono (kernel.ι f))

/-- Restrict a morphism to the actual complement of its kernel. -/
def kernelComplementMap : kernel s.retraction ⟶ Y := kernel.ι s.retraction ≫ f

/-- The restriction to the complement of the kernel is monic. -/
theorem kernelComplementMap_mono : Mono (kernelComplementMap f s) := by
  apply Preadditive.mono_of_cancel_zero
  intro Z a ha
  rw [kernelComplementMap, ← Category.assoc] at ha
  let b := kernel.lift f (a ≫ kernel.ι s.retraction) ha
  have hb : b = 0 := by
    calc
      b = (b ≫ kernel.ι f) ≫ s.retraction := by
        rw [Category.assoc, s.id, Category.comp_id]
      _ = (a ≫ kernel.ι s.retraction) ≫ s.retraction := by
        rw [kernel.lift_ι]
      _ = 0 := by simp
  apply (cancel_mono (kernel.ι s.retraction)).mp
  rw [zero_comp, ← kernel.lift_ι f (a ≫ kernel.ι s.retraction) ha]
  change b ≫ kernel.ι f = 0
  rw [hb, zero_comp]

@[reassoc]
theorem kernelComplementMap_factor :
    splitMonoComplementProjection (kernel.ι f) s ≫ kernelComplementMap f s = f := by
  unfold kernelComplementMap
  rw [← Category.assoc, splitMonoComplementProjection_ι,
    Preadditive.sub_comp, Category.id_comp, Category.assoc,
    kernel.condition, comp_zero, sub_zero]

end KernelComplement

namespace FiniteSemisimpleSkeleton
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {X Y : C} (f : X ⟶ Y)

/-- The monomorphism obtained by restricting to a chosen kernel complement. -/
def imageInclusion : kernel (S.splitMono (kernel.ι f)).retraction ⟶ Y :=
  kernelComplementMap f (S.splitMono (kernel.ι f))

instance imageInclusion_mono : Mono (S.imageInclusion f) :=
  kernelComplementMap_mono _ _

/-- An actual cokernel object, the complement of the image inclusion. -/
def splitCokernelObj : C := kernel (S.splitMono (S.imageInclusion f)).retraction

/-- The quotient projection onto the chosen actual cokernel. -/
def splitCokernelπ : Y ⟶ S.splitCokernelObj f :=
  splitMonoComplementProjection (S.imageInclusion f) (S.splitMono (S.imageInclusion f))

/-- The cokernel projection is split by the complement inclusion. -/
def splitCokernelπSplitting : SplitEpi (S.splitCokernelπ f) where
  section_ := kernel.ι (S.splitMono (S.imageInclusion f)).retraction
  id := ι_splitMonoComplementProjection _ _

@[reassoc (attr := simp)]
theorem splitCokernel_condition : f ≫ S.splitCokernelπ f = 0 := by
  calc
    f ≫ S.splitCokernelπ f =
        (splitMonoComplementProjection (kernel.ι f) (S.splitMono (kernel.ι f)) ≫
          S.imageInclusion f) ≫ S.splitCokernelπ f :=
      congrArg (fun a => a ≫ S.splitCokernelπ f)
        (kernelComplementMap_factor f (S.splitMono (kernel.ι f))).symm
    _ = 0 := by
      rw [Category.assoc]
      change splitMonoComplementProjection _ _ ≫
        (S.imageInclusion f ≫ splitMonoComplementProjection _ _) = 0
      rw [comp_splitMonoComplementProjection, comp_zero]

/-- The explicit cokernel cocone. -/
def splitCokernelCofork : CokernelCofork f :=
  CokernelCofork.ofπ (S.splitCokernelπ f) (S.splitCokernel_condition f)

/-- The complement projection satisfies the actual cokernel universal property. -/
def splitCokernelIsColimit : IsColimit (S.splitCokernelCofork f) := by
  refine CokernelCofork.IsColimit.ofπ (S.splitCokernelπ f) (S.splitCokernel_condition f)
    (fun {_} a _ => kernel.ι (S.splitMono (S.imageInclusion f)).retraction ≫ a) ?_ ?_
  · intro Z a ha
    change splitMonoComplementProjection (S.imageInclusion f)
      (S.splitMono (S.imageInclusion f)) ≫ _ = a
    rw [← Category.assoc, splitMonoComplementProjection_ι,
      Preadditive.sub_comp, Category.id_comp, Category.assoc]
    have hia : S.imageInclusion f ≫ a = 0 := by
      change (kernel.ι _ ≫ f) ≫ a = 0
      rw [Category.assoc, ha, comp_zero]
    rw [hia, comp_zero, sub_zero]
  · intro Z a ha m hm
    calc
      m = (kernel.ι (S.splitMono (S.imageInclusion f)).retraction ≫
          S.splitCokernelπ f) ≫ m := by
        change m = (kernel.ι _ ≫ splitMonoComplementProjection _ _) ≫ m
        rw [ι_splitMonoComplementProjection, Category.id_comp]
      _ = kernel.ι (S.splitMono (S.imageInclusion f)).retraction ≫ a := by
        rw [Category.assoc, hm]

/-- Cokernels are derived from the finite semisimple skeleton and actual kernels. -/
def hasCokernels : HasCokernels C :=
  ⟨fun {_ _} f => HasColimit.mk
    { cocone := S.splitCokernelCofork f
      isColimit := S.splitCokernelIsColimit f }⟩

/-- Actual coequalizers, obtained as cokernels of differences. -/
def hasCoequalizers : HasCoequalizers C := by
  letI := S.hasCokernels
  exact Preadditive.hasCoequalizers_of_hasCokernels

/-- All finite colimits follow from the actual coequalizers and biproducts. -/
def hasFiniteColimits : HasFiniteColimits C := by
  letI := S.hasCoequalizers
  exact hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts

end FiniteSemisimpleSkeleton
end Paper18.Category
