import Paper18.Category.FixedBoundaryNeutralModules
import Paper18.Category.FixedBoundaryNeutralMonoidal
import Paper18.Category.FixedBoundaryModuleGradingTransport
import Paper18.Category.FixedBoundaryEssentialComparison

/-!
# The specified boundary comparison on the entire actual neutral component

The actual boundary-module equivalence extends the original comparison to
every neutral module. The extension is monoidal and agrees with the given
α on each boundary module. No neutral-triviality assertion is included as
an input field.
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
  [RightRigidCategory N] [HasCoequalizers N]
  (i : A ⥤ N) [i.Braided] [i.Full] [i.Faithful] [i.Additive] [i.Linear ℂ]
  (P : BoundaryAutoequivalence i) (R : A) [MonObj R] [IsCommMonObj R]
  {T : N} (B : TensorInverse T)
  (himage : ∀ X : A, Centralizes T (i.obj X))
  (S : SeparableAlgebra R)
  (hfull : ∀ Y : N, Centralizes T Y → ∃ X : A, Nonempty (i.obj X ≅ Y))
  (e : P.functor.obj T ≅ T)

/-- The actual module functor restricts to the whole actual neutral category. -/
def neutralBoundaryFunctor :
    SignKernel.Positive (neutralModuleCharacter i R B himage) ⥤
      SignKernel.Positive (neutralModuleCharacter i R B himage) :=
  fullSubcategoryFunctor _ _ (P.moduleFunctor R) (fun _ hM =>
    P.moduleFunctor_homogeneous_map R B (himage R) e hM)

instance neutralBoundaryFunctorMonoidal : (neutralBoundaryFunctor i P R B himage e).Monoidal := by
  dsimp only [neutralBoundaryFunctor]
  infer_instance

/-- The original α components, lifted on the actual neutral module image. -/
def neutralBoundaryOnImage :
    neutralModuleLift i R B himage ⋙ neutralBoundaryFunctor i P R B himage e ≅
      neutralModuleLift i R B himage :=
  NatIso.ofComponents (fun M => ObjectProperty.isoMk _ ((P.moduleBoundaryNatIso R).app M))
    (fun f => (P.moduleBoundaryNatIso R).hom.naturality f)

/-- The lifted comparison retains the actual original tensor coherence. -/
def neutralBoundaryOnImageMonoidal :
    letI : PreservesColimitsOfShape WalkingParallelPair i := SA.preservesCoequalizers i
    letI := neutralModuleLiftMonoidal i R B himage SA
    NatTrans.IsMonoidal (neutralBoundaryOnImage i P R B himage e).hom := by
  letI : PreservesColimitsOfShape WalkingParallelPair i := SA.preservesCoequalizers i
  letI := neutralModuleLiftMonoidal i R B himage SA
  refine { unit := ?_, tensor := ?_ }
  · exact NatTrans.IsMonoidal.unit (τ := (P.moduleBoundaryNatIso R).hom)
  · intro M L
    exact NatTrans.IsMonoidal.tensor (τ := (P.moduleBoundaryNatIso R).hom) M L

/-- Actual full-faithful lifting along the boundary module equivalence
constructs a comparison on every actual neutral module. -/
def neutralComparison : neutralBoundaryFunctor i P R B himage e ≅
    𝟭 (SignKernel.Positive (neutralModuleCharacter i R B himage)) := by
  letI := neutralModuleLift_essSurj i R B himage S hfull
  letI : (neutralModuleLift i R B himage).IsEquivalence := {}
  exact comparisonOfEquivalence (neutralModuleLift i R B himage)
    (neutralBoundaryFunctor i P R B himage e) (neutralBoundaryOnImage i P R B himage e)

/-- The actual neutral comparison is monoidal, derived from the actual
boundary and actual equivalence rather than assumed triviality. -/
def neutralComparisonMonoidal :
    NatTrans.IsMonoidal (neutralComparison i P R B himage S hfull e).hom := by
  letI : PreservesColimitsOfShape WalkingParallelPair i := SA.preservesCoequalizers i
  letI := neutralModuleLiftMonoidal i R B himage SA
  letI := neutralModuleLift_essSurj i R B himage S hfull
  letI : (neutralModuleLift i R B himage).IsEquivalence := {}
  letI := neutralBoundaryOnImageMonoidal SA i P R B himage e
  change NatTrans.IsMonoidal (comparisonOfEquivalence (neutralModuleLift i R B himage)
    (neutralBoundaryFunctor i P R B himage e) (neutralBoundaryOnImage i P R B himage e)).hom
  infer_instance

/-- Equality on the actual image keeps every specified α component. -/
theorem neutralComparison_component (M : Mod_ A R) :
    ((neutralComparison i P R B himage S hfull e).hom.app
      ((neutralModuleLift i R B himage).obj M)).hom = P.boundary.hom.app M.X := by
  letI := neutralModuleLift_essSurj i R B himage S hfull
  letI : (neutralModuleLift i R B himage).IsEquivalence := {}
  have h := comparisonOfEquivalence_component (neutralModuleLift i R B himage)
    (neutralBoundaryFunctor i P R B himage e) (neutralBoundaryOnImage i P R B himage e) M
  exact congrArg (fun f => f.hom) h

/-- Forgetting the actual neutral comparison gives the actual specified
boundary comparison required by the native odd module-functor construction. -/
def neutralComparisonUnderlying :
    SignKernel.inclusion (neutralModuleCharacter i R B himage) ⋙ P.moduleFunctor R ≅
      SignKernel.inclusion (neutralModuleCharacter i R B himage) :=
  NatIso.ofComponents (fun M => (SignKernel.inclusion (neutralModuleCharacter i R B himage)).mapIso
    ((neutralComparison i P R B himage S hfull e).app M))
    (fun f => (neutralComparison i P R B himage S hfull e).hom.naturality f)

/-- The underlying comparison is monoidal for the original module tensor
product, not only for the restricted full-category notation. -/
def neutralComparisonUnderlyingMonoidal :
    NatTrans.IsMonoidal (neutralComparisonUnderlying i P R B himage S hfull e).hom := by
  letI := neutralComparisonMonoidal SA i P R B himage S hfull e
  refine { unit := ?_, tensor := ?_ }
  · have h := NatTrans.IsMonoidal.unit
      (τ := (neutralComparison i P R B himage S hfull e).hom)
    simp only [Functor.LaxMonoidal.comp_ε, Category.assoc]
    change Functor.LaxMonoidal.ε (P.moduleFunctor R) ≫
      (P.moduleFunctor R).map (𝟙 _) ≫ _ = 𝟙 _
    rw [(P.moduleFunctor R).map_id, Category.id_comp]
    exact h
  · intro M L
    have h := NatTrans.IsMonoidal.tensor
      (τ := (neutralComparison i P R B himage S hfull e).hom) M L
    change (Functor.LaxMonoidal.μ (P.moduleFunctor R) M.obj L.obj ≫
      (P.moduleFunctor R).map (𝟙 _)) ≫ _ = _
    rw [(P.moduleFunctor R).map_id, Category.comp_id]
    exact h

end Paper18.Category.FixedBoundary
