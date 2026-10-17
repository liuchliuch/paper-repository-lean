import Paper18.Category.FixedBoundaryNeutralBraiding
import Paper18.Category.RelativeTensorCentralImage

/-!
# The actual neutral equivalence preserves the actual braiding

Both braidings are computed on the actual balancing quotient. The tensor
comparison of module transport and the original ambient braided functor
identify those formulas. This also transports actual nondegeneracy from
the boundary de-equivariantization to the neutral category.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj Obj
universe v u w v' u'
namespace Paper18.Category.FixedBoundary
open RelativeTensor
variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℂ A]
  [MonoidalCategory A] [BraidedCategory A] [MonoidalPreadditive A] [MonoidalLinear ℂ A]
  [HasKernels A] [HasFiniteBiproducts A] [RightRigidCategory A] [HasCoequalizers A]
  [∀ X Y : A, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι]
  {N : Type u'} [Category.{v'} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N] [MonoidalPreadditive N] [MonoidalLinear ℂ N]
  [RightRigidCategory N] [HasCoequalizers N] [HasFiniteBiproducts N]
  (i : A ⥤ N) [i.Braided] [i.Full] [i.Faithful] [i.Additive] [i.Linear ℂ]
  (R : A) [MonObj R] [IsCommMonObj R]
  {T : N} (B : TensorInverse T)
  (himage : ∀ X : A, Centralizes T (i.obj X))
  (S : SeparableAlgebra R)
  (hfull : ∀ Y : N, Centralizes T Y → ∃ X : A, Nonempty (i.obj X ≅ Y))
  (hR : R ∈ mugerCenter (C := A))

@[reassoc] theorem π_neutralBraiding
    (M L : SignKernel.Positive (neutralModuleCharacter i R B himage)) :
    letI := neutralModuleBraided i R B himage S hfull hR
    π M.obj L.obj ≫ ((SignKernel.inclusion (neutralModuleCharacter i R B himage)).map
      (β_ M L).hom).hom =
      (β_ M.obj.X L.obj.X).hom ≫ π L.obj M.obj := by
  letI := neutralModuleBraided i R B himage S hfull hR
  exact π_localModulesBraiding
    ((neutralToLocal i R B himage S hfull hR).obj M)
    ((neutralToLocal i R B himage S hfull hR).obj L)

/-- Actual braiding compatibility of the actual neutral module equivalence. -/
def neutralModuleLiftBraided (SA : FiniteSemisimpleSkeleton A ι) :
    letI := moduleBraidedOfTransparent hR
    letI := neutralModuleBraided i R B himage S hfull hR
    letI : PreservesColimitsOfShape WalkingParallelPair i := SA.preservesCoequalizers i
    letI := neutralModuleLiftMonoidal i R B himage SA
    (neutralModuleLift i R B himage).Braided := by
  letI := moduleBraidedOfTransparent hR
  letI := neutralModuleBraided i R B himage S hfull hR
  letI : PreservesColimitsOfShape WalkingParallelPair i := SA.preservesCoequalizers i
  letI := neutralModuleLiftMonoidal i R B himage SA
  refine { braided := ?_ }
  intro M L
  apply (SignKernel.inclusion (neutralModuleCharacter i R B himage)).map_injective
  apply module_hom_ext
  change π ((InternalModule.mapModules i).obj M) ((InternalModule.mapModules i).obj L) ≫
      (Functor.LaxMonoidal.μ (InternalModule.mapModules i) M L).hom ≫
      i.map (β_ M L).hom.hom =
    π ((InternalModule.mapModules i).obj M) ((InternalModule.mapModules i).obj L) ≫
      ((SignKernel.inclusion (neutralModuleCharacter i R B himage)).map
        (β_ ((neutralModuleLift i R B himage).obj M)
          ((neutralModuleLift i R B himage).obj L)).hom).hom ≫
      (Functor.LaxMonoidal.μ (InternalModule.mapModules i) L M).hom
  have hb := π_neutralBraiding i R B himage S hfull hR
    ((neutralModuleLift i R B himage).obj M)
    ((neutralModuleLift i R B himage).obj L)
  change π ((InternalModule.mapModules i).obj M) ((InternalModule.mapModules i).obj L) ≫
      ((SignKernel.inclusion (neutralModuleCharacter i R B himage)).map
        (β_ ((neutralModuleLift i R B himage).obj M)
          ((neutralModuleLift i R B himage).obj L)).hom).hom = _ at hb
  rw [reassoc_of% hb]
  erw [InternalModule.π_mapModules_μ_assoc, InternalModule.π_mapModules_μ]
  rw [← i.map_comp]
  erw [π_moduleBraidingOfTransparent hR, i.map_comp]
  rw [Functor.LaxBraided.braided_assoc]
  rfl

/-- Actual nondegeneracy is transported across the constructed actual
braided equivalence, by mapping actual unit decompositions. -/
theorem neutralNondegenerate (SA : FiniteSemisimpleSkeleton A ι)
    (hsource : letI := moduleBraidedOfTransparent hR; IsNondegenerate (C := Mod_ A R)) :
    letI := neutralModuleBraided i R B himage S hfull hR
    IsNondegenerate (C := SignKernel.Positive (neutralModuleCharacter i R B himage)) := by
  letI := moduleBraidedOfTransparent hR
  letI := neutralModuleBraided i R B himage S hfull hR
  letI : PreservesColimitsOfShape WalkingParallelPair i := SA.preservesCoequalizers i
  letI := neutralModuleLiftMonoidal i R B himage SA
  letI := neutralModuleLiftBraided i R B himage S hfull hR SA
  letI := neutralModuleLift_essSurj i R B himage S hfull
  let K := neutralModuleLift i R B himage
  letI : K.Additive := by
    refine { map_add := ?_ }
    intro M L f g
    apply Mod_.hom_ext
    exact i.map_add
  intro X hX
  let Y := K.objPreimage X
  let q := K.objObjPreimageIso X
  have hy : Y ∈ mugerCenter := by
    intro Z _
    apply (centralizes_map_iff K Y Z).mp
    exact (hX (K.obj Z) (Set.mem_univ _)).of_iso_left q
  exact (unitSum_map K (hsource Y hy)).of_iso q.symm

end Paper18.Category.FixedBoundary
