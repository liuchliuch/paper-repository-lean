import Paper18.Category.SemisimpleCokernels
import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
# Additive functors preserve actual semisimple cokernels

The chosen actual semisimple cokernel is a split complement projection.
Its actual universal property is preserved by every additive functor,
using the mapped split identities. Coequalizer preservation follows from
the cokernel-of-a-difference construction.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe v u w v' u'
namespace Paper18.Category.FiniteSemisimpleSkeleton
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {D : Type u'} [Category.{v'} D] [Preadditive D]
  (F : C ⥤ D) [F.Additive] {X Y : C} (f : X ⟶ Y)

/-- The mapped actual semisimple cokernel has its actual universal
property, with the mapped complement inclusion as the descent map. -/
def mapSplitCokernelIsColimit :
    IsColimit (CokernelCofork.ofπ (F.map (S.splitCokernelπ f)) (by
      rw [← F.map_comp, S.splitCokernel_condition, F.map_zero])) := by
  refine CokernelCofork.IsColimit.ofπ (F.map (S.splitCokernelπ f)) _
    (fun {_} a _ => F.map (kernel.ι (S.splitMono (S.imageInclusion f)).retraction) ≫ a) ?_ ?_
  · intro Z a ha
    have hia : F.map (S.imageInclusion f) ≫ a = 0 := by
      change F.map (kernel.ι _ ≫ f) ≫ a = 0
      rw [F.map_comp, Category.assoc, ha, comp_zero]
    change F.map (splitMonoComplementProjection (S.imageInclusion f)
      (S.splitMono (S.imageInclusion f))) ≫ _ = a
    rw [← F.map_comp_assoc, splitMonoComplementProjection_ι, F.map_sub, F.map_id,
      Preadditive.sub_comp, Category.id_comp, F.map_comp, Category.assoc, hia,
      comp_zero, sub_zero]
  · intro Z a ha m hm
    calc
      m = (F.map (kernel.ι (S.splitMono (S.imageInclusion f)).retraction) ≫
          F.map (S.splitCokernelπ f)) ≫ m := by
        rw [← F.map_comp]
        change m = F.map (kernel.ι _ ≫ splitMonoComplementProjection _ _) ≫ m
        rw [ι_splitMonoComplementProjection, F.map_id, Category.id_comp]
      _ = F.map (kernel.ι (S.splitMono (S.imageInclusion f)).retraction) ≫ a := by
        rw [Category.assoc, hm]

/-- Every actual cokernel is preserved; the result is derived from the
split cokernel, not included as an exactness assumption. -/
def preservesCokernel : PreservesColimit (parallelPair f 0) F := by
  apply preservesColimit_of_preserves_colimit_cocone (S.splitCokernelIsColimit f)
  exact (isColimitMapCoconeCoforkEquiv' F (S.splitCokernel_condition f)).symm
    (S.mapSplitCokernelIsColimit F f)

/-- Actual coequalizer preservation for every additive functor from the
given finite semisimple category. -/
def preservesCoequalizers : PreservesColimitsOfShape WalkingParallelPair F := by
  letI : ∀ {X Y : C} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) F :=
    fun {_ _} f => S.preservesCokernel F f
  exact Functor.preservesCoequalizers_of_preservesCokernels F

end Paper18.Category.FiniteSemisimpleSkeleton
