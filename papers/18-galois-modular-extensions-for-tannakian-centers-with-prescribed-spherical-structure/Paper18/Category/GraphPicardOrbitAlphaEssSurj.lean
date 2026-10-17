import Paper18.Category.GraphPicardOrbitAlphaEssSurjBasic
import Paper18.Category.GraphPicardOrbitAlphaEssSurjDimension

/-! # Essential surjectivity of the actual graph-orbit alpha inductions

The actual graph orbit End dimension has already been calculated. Once the
corresponding actual Full instance is proved, its established faithfulness,
actual simple-image injection and the objectwise dimension calculation give
actual essential surjectivity. Fullness is neither constructed nor postulated
here. The strong monoidal equivalences use exactly the native conventions:
`Dᴹᵒᵖ ≌ (End Dᴹᵒᵖ ModuleOrbit)ᴹᵒᵖ`.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u w
namespace Paper18.Category.GraphPicard
attribute [local instance 2000] RightRigidCategory.rightDual
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)
  (α : D ⥤ D) [α.Braided] [α.Additive] [α.Linear ℂ] [α.IsEquivalence]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
attribute [local instance] alphaEndKernels alphaEndFiniteHom alphaEndRightRigid alphaEndSimpleUnit
attribute [local instance] graphPositiveFaithful graphNegativeFaithful

/-- Actual positive alpha induction reaches every actual graph-orbit
module endofunctor, once its actual fullness has been proved. -/
instance graphPositiveEssSurj [(graphPositive S α).Full] :
    (graphPositive S α).EssSurj := by
  let F := mopFunctor D ⋙ graphPositive S α
  letI : F.EssSurj := S.essSurjOfFPdimEq (graphEndSkeleton S α) F
    (fun X => graphPositive_fpdim S α (mop X)) (graphEnd_totalFPdim S α).symm
  constructor
  intro Y
  obtain ⟨X, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := F) Y
  exact ⟨mop X, ⟨e⟩⟩

/-- The same actual dimension argument applies to negative alpha induction. -/
instance graphNegativeEssSurj [(graphNegative S α).Full] :
    (graphNegative S α).EssSurj := by
  let F := mopFunctor D ⋙ graphNegative S α
  letI : F.EssSurj := S.essSurjOfFPdimEq (graphEndSkeleton S α) F
    (fun X => graphNegative_fpdim S α (mop X)) (graphEnd_totalFPdim S α).symm
  constructor
  intro Y
  obtain ⟨X, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := F) Y
  exact ⟨mop X, ⟨e⟩⟩

/-- Positive alpha induction is an actual ordinary equivalence after
actual fullness is registered. -/
instance graphPositiveIsEquivalence [(graphPositive S α).Full] :
    (graphPositive S α).IsEquivalence where
  faithful := graphPositiveFaithful S α
  full := inferInstance
  essSurj := graphPositiveEssSurj S α

/-- Negative alpha induction is an actual ordinary equivalence after
actual fullness is registered. -/
instance graphNegativeIsEquivalence [(graphNegative S α).Full] :
    (graphNegative S α).IsEquivalence where
  faithful := graphNegativeFaithful S α
  full := inferInstance
  essSurj := graphNegativeEssSurj S α

/-- The actual positive strong monoidal functor, with its correct target
composition convention. -/
abbrev graphPositiveMop :=
  ModuleAlphaInduction.positiveMop Dᴹᵒᵖ (GraphLagrangian.ModuleOrbit S α)

/-- The actual negative strong monoidal functor uses the same monoidal
opposite convention in the target. -/
abbrev graphNegativeMop :=
  ModuleAlphaInduction.negativeMop Dᴹᵒᵖ (GraphLagrangian.ModuleOrbit S α)

instance graphPositiveMopIsEquivalence [(graphPositive S α).Full] :
    (graphPositiveMop S α).IsEquivalence := by
  change (graphPositive S α ⋙ mopFunctor _).IsEquivalence
  infer_instance

instance graphNegativeMopIsEquivalence [(graphNegative S α).Full] :
    (graphNegativeMop S α).IsEquivalence := by
  change (graphNegative S α ⋙ mopFunctor _).IsEquivalence
  infer_instance

/-- The actual positive equivalence retains the actual strong alpha
functor as its forward functor. -/
def graphPositiveMonoidalEquivalence [(graphPositive S α).Full] :
    Dᴹᵒᵖ ≌ (ModuleAlphaInduction.End Dᴹᵒᵖ (GraphLagrangian.ModuleOrbit S α))ᴹᵒᵖ :=
  (graphPositiveMop S α).asEquivalence

/-- The actual negative equivalence retains the actual strong alpha
functor as its forward functor. -/
def graphNegativeMonoidalEquivalence [(graphNegative S α).Full] :
    Dᴹᵒᵖ ≌ (ModuleAlphaInduction.End Dᴹᵒᵖ (GraphLagrangian.ModuleOrbit S α))ᴹᵒᵖ :=
  (graphNegativeMop S α).asEquivalence

instance graphPositiveEquivalenceFunctorMonoidal [(graphPositive S α).Full] :
    (graphPositiveMonoidalEquivalence S α).functor.Monoidal :=
  inferInstanceAs (graphPositiveMop S α).Monoidal

instance graphNegativeEquivalenceFunctorMonoidal [(graphNegative S α).Full] :
    (graphNegativeMonoidalEquivalence S α).functor.Monoidal :=
  inferInstanceAs (graphNegativeMop S α).Monoidal

/-- The actual inverse positive equivalence has the transported strong
monoidal structure. -/
def graphPositiveEquivalenceInverseMonoidal [(graphPositive S α).Full] :
    (graphPositiveMonoidalEquivalence S α).inverse.Monoidal :=
  (graphPositiveMonoidalEquivalence S α).inverseMonoidal

/-- The actual inverse negative equivalence has the transported strong
monoidal structure. -/
def graphNegativeEquivalenceInverseMonoidal [(graphNegative S α).Full] :
    (graphNegativeMonoidalEquivalence S α).inverse.Monoidal :=
  (graphNegativeMonoidalEquivalence S α).inverseMonoidal

/-- The positive unit and counit are actual monoidal natural isomorphisms. -/
def graphPositiveEquivalenceIsMonoidal [(graphPositive S α).Full] :
    letI := graphPositiveEquivalenceInverseMonoidal S α
    (graphPositiveMonoidalEquivalence S α).IsMonoidal := by
  letI := graphPositiveEquivalenceInverseMonoidal S α
  infer_instance

/-- The negative unit and counit are actual monoidal natural isomorphisms. -/
def graphNegativeEquivalenceIsMonoidal [(graphNegative S α).Full] :
    letI := graphNegativeEquivalenceInverseMonoidal S α
    (graphNegativeMonoidalEquivalence S α).IsMonoidal := by
  letI := graphNegativeEquivalenceInverseMonoidal S α
  infer_instance

end Paper18.Category.GraphPicard
