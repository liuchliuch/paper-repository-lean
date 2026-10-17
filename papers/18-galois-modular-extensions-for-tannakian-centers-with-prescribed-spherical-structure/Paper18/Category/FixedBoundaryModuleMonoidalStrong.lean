import Paper18.Category.FixedBoundaryModuleMonoidalBasic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-!
# Tensor transport is strong when the ambient functor preserves coequalizers

The actual tensor comparison identifies two actual colimiting coforks.
This proves invertibility from preservation of the defining balancing
coequalizer, rather than including it as transport data.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj Obj
universe v u v' u'
namespace Paper18.Category.InternalModule
open RelativeTensor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [HasCoequalizers C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [HasCoequalizers D]
  (F : C ⥤ D) [F.Braided] [PreservesColimitsOfShape WalkingParallelPair F]
  {A : C} [MonObj A] [IsCommMonObj A]

instance balancingTensorator_isIso (M N : Mod_ C A) : IsIso (balancingTensorator F M N) := by
  unfold balancingTensorator
  infer_instance

/-- The transported balancing quotient is itself a colimit of the actual
balancing diagram in the target category. -/
def mapModuleTensor_isColimit (M N : Mod_ C A) :
    IsColimit (Cofork.ofπ (Functor.LaxMonoidal.μ F M.X N.X ≫ F.map (π M N))
      (mapModuleTensor_balanced F M N)) := by
  let c : Cofork (F.map (parallelLeft M N)) (F.map (parallelRight M N)) :=
    Cofork.ofπ (F.map (π M N)) (by rw [← F.map_comp, ← F.map_comp, condition M N])
  have hc : IsColimit c :=
    isColimitOfHasCoequalizerOfPreservesColimit F (parallelLeft M N) (parallelRight M N)
  refine Cofork.isColimitOfIsos c hc _
    (asIso (balancingTensorator F M N)).symm
    (Functor.Monoidal.μIso F M.X N.X).symm (Iso.refl _) ?_ ?_ ?_
  · apply (cancel_mono (Functor.LaxMonoidal.μ F M.X N.X)).mp
    simp only [Iso.symm_hom, Iso.symm_inv, Functor.Monoidal.μIso_inv,
      Category.assoc, Functor.Monoidal.δ_μ, Category.comp_id]
    rw [mapModule_parallelLeft]
    simp
  · apply (cancel_mono (Functor.LaxMonoidal.μ F M.X N.X)).mp
    simp only [Iso.symm_hom, Iso.symm_inv, Functor.Monoidal.μIso_inv,
      Category.assoc, Functor.Monoidal.δ_μ, Category.comp_id]
    rw [mapModule_parallelRight]
    simp
  · simp [c]

/-- Preservation of the balancing coequalizer makes the actual transported
tensor map invertible. -/
instance mapModulesTensorHom_isIso (M N : Mod_ C A) : IsIso (mapModulesTensorHom F M N) := by
  let hc := mapModuleTensor_isColimit F M N
  let hd := coequalizerIsCoequalizer (parallelLeft (mapModuleObj F M) (mapModuleObj F N))
    (parallelRight (mapModuleObj F M) (mapModuleObj F N))
  let e := hd.coconePointUniqueUpToIso hc
  have he : (mapModulesTensorHom F M N).hom = e.hom := by
    apply hom_ext (mapModuleObj F M) (mapModuleObj F N)
    rw [π_mapModulesTensorHom]
    exact (IsColimit.comp_coconePointUniqueUpToIso_hom hd hc WalkingParallelPair.one).symm
  letI : IsIso (mapModulesTensorHom F M N).hom := he ▸ e.isIso_hom
  exact internalModule_isIso_of_underlying (mapModulesTensorHom F M N)

end Paper18.Category.InternalModule
