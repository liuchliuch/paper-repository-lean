import Paper18.Category.FixedBoundaryNeutralComparison
import Paper18.Category.FixedBoundaryHomogeneousBoundary
import Paper18.Category.FixedBoundaryModuleAutoequivalence
import Paper18.Category.ModuleFunctorFiniteHomogeneous

/-!
# The actual odd module autoequivalence of a specified boundary pair

The original braided boundary pair acts on the actual internal modules,
preserves the actual monodromy grading, and has the specified monoidal
comparison on the entire neutral component. These proved constructions
give an actual complex-linear strong neutral-module autoequivalence of
the actual odd component.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj Obj
universe v u w v' u'
namespace Paper18.Category.FixedBoundary
variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℂ A]
  [MonoidalCategory A] [BraidedCategory A] [MonoidalPreadditive A] [MonoidalLinear ℂ A]
  [HasKernels A] [HasFiniteBiproducts A] [RightRigidCategory A] [HasCoequalizers A]
  [∀ X Y : A, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (SA : FiniteSemisimpleSkeleton A ι)
  {N : Type u'} [Category.{v'} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N] [MonoidalPreadditive N] [MonoidalLinear ℂ N]
  [RightRigidCategory N] [HasCoequalizers N] [HasKernels N] [HasFiniteBiproducts N]
  (i : A ⥤ N) [i.Braided] [i.Full] [i.Faithful] [i.Additive] [i.Linear ℂ]
  (P : BoundaryAutoequivalence i) (R : A) [MonObj R] [IsCommMonObj R]
  {T : N} (B : TensorInverse T)
  (himage : ∀ X : A, Centralizes T (i.obj X))
  (S : SeparableAlgebra R)
  (hfull : ∀ Y : N, Centralizes T Y → ∃ X : A, Nonempty (i.obj X ≅ Y))
  (e : P.functor.obj T ≅ T)

/-- The ordinary restricted functor uses the derived specified comparison. -/
def oddBoundaryModuleFunctor :
    HomogeneousCategory (neutralModuleCharacter i R B himage) 1 ⥤
      HomogeneousCategory (neutralModuleCharacter i R B himage) 1 :=
  homogeneousBoundaryFunctor (neutralModuleCharacter i R B himage) (P.moduleFunctor R)
    (neutralComparisonUnderlying i P R B himage S hfull e) 1
    (fun _ hM => P.moduleFunctor_homogeneous_map R B (himage R) e hM)

private def moduleFunctorIsEquivalence : (P.moduleFunctor R).IsEquivalence := by
  change (P.moduleEquivalence R (S.map i)).functor.IsEquivalence
  infer_instance

instance oddBoundaryModuleFunctorFaithful :
    (oddBoundaryModuleFunctor i P R B himage S hfull e).Faithful := by
  letI := moduleFunctorIsEquivalence i P R S
  dsimp only [oddBoundaryModuleFunctor]
  infer_instance

instance oddBoundaryModuleFunctorFull :
    (oddBoundaryModuleFunctor i P R B himage S hfull e).Full := by
  letI := moduleFunctorIsEquivalence i P R S
  dsimp only [oddBoundaryModuleFunctor]
  infer_instance

instance oddBoundaryModuleFunctorAdditive :
    (oddBoundaryModuleFunctor i P R B himage S hfull e).Additive := by
  letI := moduleFunctorIsEquivalence i P R S
  dsimp only [oddBoundaryModuleFunctor]
  infer_instance

instance oddBoundaryModuleFunctorLinear :
    (oddBoundaryModuleFunctor i P R B himage S hfull e).Linear ℂ := by
  letI := moduleFunctorIsEquivalence i P R S
  dsimp only [oddBoundaryModuleFunctor]
  infer_instance

/-- The actual inverse-algebra comparison and the original α determine
all eight strong native module-functor coherence laws. -/
def oddBoundaryModuleLeftLinear :
    (oddBoundaryModuleFunctor i P R B himage S hfull e).LeftLinear
      (SignKernel.Positive (neutralModuleCharacter i R B himage)) := by
  letI := moduleFunctorIsEquivalence i P R S
  letI := neutralComparisonUnderlyingMonoidal SA i P R B himage S hfull e
  exact homogeneousFunctor_leftLinear (neutralModuleCharacter i R B himage) (P.moduleFunctor R)
    (neutralComparisonUnderlying i P R B himage S hfull e) 1 _

/-- Preservation and reflection of actual degree make the restriction an
actual equivalence of categories. -/
def oddBoundaryModuleEquivalence :
    HomogeneousCategory (neutralModuleCharacter i R B himage) 1 ≌
      HomogeneousCategory (neutralModuleCharacter i R B himage) 1 := by
  letI := moduleFunctorIsEquivalence i P R S
  letI : (oddBoundaryModuleFunctor i P R B himage S hfull e).EssSurj := by
    dsimp only [oddBoundaryModuleFunctor]
    exact homogeneousFunctor_essSurj (neutralModuleCharacter i R B himage) (P.moduleFunctor R)
      (neutralComparisonUnderlying i P R B himage S hfull e) 1
      (fun _ hM => P.moduleFunctor_homogeneous_map R B (himage R) e hM)
      (fun M hM => (P.moduleFunctor_homogeneous_map_iff R B (himage R) e 1 M).mp hM)
  letI : (oddBoundaryModuleFunctor i P R B himage S hfull e).IsEquivalence := {}
  exact (oddBoundaryModuleFunctor i P R B himage S hfull e).asEquivalence

/-- The actual object of the native complex-linear module-endofunctor
category to which alpha-induction classification is applied. -/
def oddBoundaryModuleEnd :
    ModuleFunctor.Bundled (SignKernel.Positive (neutralModuleCharacter i R B himage))
      (HomogeneousCategory (neutralModuleCharacter i R B himage) 1)
      (HomogeneousCategory (neutralModuleCharacter i R B himage) 1) := by
  letI := moduleFunctorIsEquivalence i P R S
  letI := oddBoundaryModuleLeftLinear SA i P R B himage S hfull e
  exact
    { toFunctor := oddBoundaryModuleFunctor i P R B himage S hfull e
      leftLinear := inferInstance
      additive := inferInstance
      linear := inferInstance }

end Paper18.Category.FixedBoundary
