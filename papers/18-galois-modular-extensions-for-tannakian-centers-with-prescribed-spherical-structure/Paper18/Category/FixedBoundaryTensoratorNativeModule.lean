import Paper18.Category.FixedBoundaryTensoratorCorrection
import Paper18.Category.FixedBoundaryOrdinaryExtraction
import Paper18.Category.FixedBoundaryOddBoundaryModules
import Paper18.Category.FixedBoundaryNeutralCenter
import Paper18.Category.FixedBoundaryModuleMixed

/-! # Actual monoidal correction of (neutralComparisonUnderlying i P R B himage s hfull eT) native odd module comparison

The actual odd module isomorphism glues with the specified neutral alpha.
Its left mixed equation follows from native module naturality. The actual
local central crossing proves the right mixed equation. Rigid scalar
extraction and H² then construct the actual monoidal comparison on all
modules, without (neutralComparisonUnderlying i P R B himage s hfull eT) braiding on the category of all modules.
-/
set_option maxHeartbeats 4000000
set_option maxRecDepth 3000
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj Obj
universe v u w v' u' w'
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
  (s : SeparableAlgebra R)
  (hfull : ∀ Y : N, Centralizes T Y → ∃ X : A, Nonempty (i.obj X ≅ Y))
  (hR : R ∈ mugerCenter (C := A))
  (eT : P.functor.obj T ≅ T)

private def nativeModuleFunctorIsEquivalence : ((P.moduleFunctor R)).IsEquivalence := by
  change (P.moduleEquivalence R (s.map i)).functor.IsEquivalence
  infer_instance
private def nativeNeutralComparisonMonoidal : NatTrans.IsMonoidal ((neutralComparisonUnderlying i P R B himage s hfull eT)).hom :=
  neutralComparisonUnderlyingMonoidal SA i P R B himage s hfull eT

/-- Native module naturality for the actual odd boundary functor. -/
def NativeOddComparisonNatural
    (b : oddBoundaryModuleFunctor i P R B himage s hfull eT ≅
      𝟭 (HomogeneousCategory (neutralModuleCharacter i R B himage) 1)) : Prop := by
  letI := oddBoundaryModuleLeftLinear SA i P R B himage s hfull eT
  exact ModuleFunctor.IsModuleNatural (SignKernel.Positive (neutralModuleCharacter i R B himage)) b.hom

/-- The actual odd comparison and prescribed neutral alpha construct the
ordinary comparison on every actual module. -/
def nativeModuleOrdinaryComparison
    (hchi : ∀ X : (Mod_ N (i.obj R)), ((neutralModuleCharacter i R B himage)).hom.app X ≫ ((neutralModuleCharacter i R B himage)).hom.app X = 𝟙 X)
    (b : oddBoundaryModuleFunctor i P R B himage s hfull eT ≅
      𝟭 (HomogeneousCategory (neutralModuleCharacter i R B himage) 1)) : (P.moduleFunctor R) ≅ 𝟭 (Mod_ N (i.obj R)) :=
  ordinaryComparisonFromOdd (neutralModuleCharacter i R B himage) hchi (P.moduleFunctor R) (neutralComparisonUnderlying i P R B himage s hfull eT) (fun _ hX => P.moduleFunctor_homogeneous_map R B (himage R) eT hX) b

variable (hchi : ∀ X : (Mod_ N (i.obj R)), ((neutralModuleCharacter i R B himage)).hom.app X ≫ ((neutralModuleCharacter i R B himage)).hom.app X = 𝟙 X)
variable (b : oddBoundaryModuleFunctor i P R B himage s hfull eT ≅
    𝟭 (HomogeneousCategory (neutralModuleCharacter i R B himage) 1))
variable (hb : NativeOddComparisonNatural SA i P R B himage s hfull eT b)

include SA hb hchi in
omit [i.Linear ℂ] in
/-- Native odd naturality proves the actual left mixed tensor equation. -/
lemma nativeModuleOrdinaryComparison_zero_left {g : ZMod 2} {X Y : (Mod_ N (i.obj R))}
    (hX : Homogeneous (neutralModuleCharacter i R B himage) 0 X) (hY : Homogeneous (neutralModuleCharacter i R B himage) g Y) :
    tensoratorDefect (P.moduleFunctor R) (nativeModuleOrdinaryComparison i P R B himage s hfull eT hchi b) X Y = 𝟙 _ := by
  letI := nativeModuleFunctorIsEquivalence i P R s
  letI := nativeNeutralComparisonMonoidal SA i P R B himage s hfull eT
  letI : (oddBoundaryModuleFunctor i P R B himage s hfull eT).LeftLinear
      (SignKernel.Positive (neutralModuleCharacter i R B himage)) := oddBoundaryModuleLeftLinear SA i P R B himage s hfull eT
  letI : ModuleFunctor.IsModuleNatural
      (SignKernel.Positive (neutralModuleCharacter i R B himage)) b.hom := hb
  let e := nativeModuleOrdinaryComparison i P R B himage s hfull eT hchi b
  letI : ModuleFunctor.IsModuleNatural (SignKernel.Positive (neutralModuleCharacter i R B himage))
      (comparisonRestriction (neutralModuleCharacter i R B himage) (P.moduleFunctor R) (neutralComparisonUnderlying i P R B himage s hfull eT) (fun _ hX => P.moduleFunctor_homogeneous_map R B (himage R) eT hX) e).hom :=
    ordinaryComparisonFromOdd_moduleNatural (neutralModuleCharacter i R B himage) (P.moduleFunctor R) (neutralComparisonUnderlying i P R B himage s hfull eT) (fun _ hX => P.moduleFunctor_homogeneous_map R B (himage R) eT hX) hchi b
  exact tensoratorDefect_zero_left (neutralModuleCharacter i R B himage) (P.moduleFunctor R) (neutralComparisonUnderlying i P R B himage s hfull eT) (fun _ hX => P.moduleFunctor_homogeneous_map R B (himage R) eT hX) e
    (ordinaryComparisonFromOdd_boundary (neutralModuleCharacter i R B himage) hchi (P.moduleFunctor R) (neutralComparisonUnderlying i P R B himage s hfull eT) (fun _ hX => P.moduleFunctor_homogeneous_map R B (himage R) eT hX) b) hX hY

include SA hb hchi hR in
/-- The actual local half-braiding proves the other mixed equation.
No all-module braiding is assumed. -/
lemma nativeModuleOrdinaryComparison_zero_right {g : ZMod 2} {X Y : (Mod_ N (i.obj R))}
    (hX : Homogeneous (neutralModuleCharacter i R B himage) g X) (hY : Homogeneous (neutralModuleCharacter i R B himage) 0 Y) :
    tensoratorDefect (P.moduleFunctor R) (nativeModuleOrdinaryComparison i P R B himage s hfull eT hchi b) X Y = 𝟙 _ := by
  letI := nativeModuleFunctorIsEquivalence i P R s
  letI := nativeNeutralComparisonMonoidal SA i P R B himage s hfull eT
  letI : (oddBoundaryModuleFunctor i P R B himage s hfull eT).LeftLinear
      (SignKernel.Positive (neutralModuleCharacter i R B himage)) := oddBoundaryModuleLeftLinear SA i P R B himage s hfull eT
  letI : ModuleFunctor.IsModuleNatural
      (SignKernel.Positive (neutralModuleCharacter i R B himage)) b.hom := hb
  let e := nativeModuleOrdinaryComparison i P R B himage s hfull eT hchi b
  apply tensoratorDefect_eq_id_of_tensor
  apply P.moduleComparison_tensor_right R (s.map i) e Y X
    (neutralModule_local i R B himage s hfull hR ⟨Y, hY⟩)
  exact (tensoratorDefect_eq_id_iff_tensor (P.moduleFunctor R) e Y X).mp
    (nativeModuleOrdinaryComparison_zero_left SA i P R B himage s hfull eT hchi b hb hY hX)

variable [RightRigidCategory (Mod_ N (i.obj R))] [Simple (𝟙_ (Mod_ N (i.obj R)))]
  [∀ X Y : (Mod_ N (i.obj R)), FiniteDimensional ℂ (X ⟶ Y)]
  {κ : Type w'} [Fintype κ] (SD : FiniteSemisimpleSkeleton (Mod_ N (i.obj R)) κ)
  (j : κ) (hj : Homogeneous (neutralModuleCharacter i R B himage) 1 (SD.simpleObject j))

include SA hb hchi hR SD hj in
/-- A genuine native odd comparison yields an actual normalized cochain
and a monoidal all-module comparison retaining the specified neutral alpha.
No tensorator scalars, cocycle, all-module braiding, or equivariance
conclusion is supplied as input. -/
theorem nativeModule_monoidal_gauge :
    ∃ uGauge : ZMod 2 → ℂˣ, uGauge 0 = 1 ∧
      NatTrans.IsMonoidal (correctedIso (P.moduleFunctor R)
        (nativeModuleOrdinaryComparison i P R B himage s hfull eT hchi b) (neutralModuleCharacter i R B himage) hchi uGauge).hom ∧
        ∀ X : SignKernel.Positive (neutralModuleCharacter i R B himage),
          (correctedIso (P.moduleFunctor R) (nativeModuleOrdinaryComparison i P R B himage s hfull eT hchi b)
            (neutralModuleCharacter i R B himage) hchi uGauge).hom.app X.obj = ((neutralComparisonUnderlying i P R B himage s hfull eT)).hom.app X := by
  letI := nativeModuleFunctorIsEquivalence i P R s
  letI := nativeNeutralComparisonMonoidal SA i P R B himage s hfull eT
  exact exists_monoidal_gauge_of_mixed SD (neutralModuleCharacter i R B himage) hchi (P.moduleFunctor R) (neutralComparisonUnderlying i P R B himage s hfull eT)
    (nativeModuleOrdinaryComparison i P R B himage s hfull eT hchi b)
    (ordinaryComparisonFromOdd_boundary (neutralModuleCharacter i R B himage) hchi (P.moduleFunctor R) (neutralComparisonUnderlying i P R B himage s hfull eT) (fun _ hX => P.moduleFunctor_homogeneous_map R B (himage R) eT hX) b)
    (fun hX hY => nativeModuleOrdinaryComparison_zero_left SA i P R B himage s hfull eT hchi b hb hX hY)
    (fun hX hY => nativeModuleOrdinaryComparison_zero_right SA i P R B himage s hfull hR eT hchi b hb hX hY)
    j hj

include SA hb hchi hR SD hj in
/-- The actual all-module monoidal comparison with the chosen boundary. -/
theorem nativeModule_monoidal_comparison :
    ∃ β : (P.moduleFunctor R) ≅ 𝟭 (Mod_ N (i.obj R)), NatTrans.IsMonoidal β.hom ∧
      ∀ X : SignKernel.Positive (neutralModuleCharacter i R B himage), β.hom.app X.obj = ((neutralComparisonUnderlying i P R B himage s hfull eT)).hom.app X := by
  obtain ⟨uGauge, _, hm, ha⟩ := nativeModule_monoidal_gauge SA i P R B himage s hfull hR eT hchi b hb SD j hj
  exact ⟨correctedIso (P.moduleFunctor R) (nativeModuleOrdinaryComparison i P R B himage s hfull eT hchi b)
    (neutralModuleCharacter i R B himage) hchi uGauge, hm, ha⟩


omit [HasKernels N] [HasFiniteBiproducts N]
  [RightRigidCategory (Mod_ N (i.obj R))] [Simple (𝟙_ (Mod_ N (i.obj R)))]
  [∀ X Y : Mod_ N (i.obj R), FiniteDimensional ℂ (X ⟶ Y)] in
/-- Exact neutral normalization retains the specified original alpha on
every actual boundary module, including every actual boundary free
module. -/
lemma moduleComparison_boundary_component
    (β : P.moduleFunctor R ≅ 𝟭 (Mod_ N (i.obj R)))
    (ha : ∀ X : SignKernel.Positive (neutralModuleCharacter i R B himage),
      β.hom.app X.obj =
        (neutralComparisonUnderlying i P R B himage s hfull eT).hom.app X)
    (M : Mod_ A R) :
    (β.hom.app ((InternalModule.mapModules i).obj M)).hom = P.boundary.hom.app M.X := by
  have h := congrArg (fun f => f.hom) (ha ((neutralModuleLift i R B himage).obj M))
  exact h.trans (neutralComparison_component i P R B himage s hfull eT M)

end Paper18.Category.FixedBoundary
