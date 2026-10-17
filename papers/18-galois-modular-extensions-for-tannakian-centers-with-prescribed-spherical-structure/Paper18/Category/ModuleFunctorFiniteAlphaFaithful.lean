import Paper18.Category.ModuleFunctorFiniteHomogeneous
import Paper18.Category.ModuleFunctorFiniteContraction
import Paper18.Category.ModuleAlphaInductionFunctor

/-! # Actual faithfulness of homogeneous alpha induction

The actual normalized rigid contraction retracts the action on any
actual homogeneous simple. Thus both actual alpha-induction functors are
faithful on every nonempty actual homogeneous component. Only the neutral
category is braided; the ambient graded category need not be braided.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.FixedBoundary
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [RightRigidCategory C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (χ : 𝟭 C ≅ 𝟭 C) [NatTrans.IsMonoidal χ.hom] (d : ZMod 2)
  [BraidedCategory (SignKernel.Positive χ)]

/-- Actual positive alpha induction is faithful, using an actual simple
in the component and the constructed rigid contraction. -/
def homogeneousPositiveFaithful (j : ι) (hj : Homogeneous χ d (S.simpleObject j)) :
    (ModuleAlphaInduction.positive (SignKernel.Positive χ) (HomogeneousCategory χ d)).Faithful where
  map_injective {X Y} f g h := by
    let n : HomogeneousCategory χ d := ⟨S.simpleObject j, hj⟩
    let a : X.obj ⟶ Y.obj := f
    let b : X.obj ⟶ Y.obj := g
    have he := congrArg (fun t => t.val.app n) h
    change a ▷ S.simpleObject j = b ▷ S.simpleObject j at he
    have ht := congrArg (ModuleFunctor.simpleContraction S (S.simpleObject j)) he
    simpa only [ModuleFunctor.simpleContraction_whiskerRight] using ht

/-- The same actual contraction proves faithfulness of negative alpha
induction, without any braiding on the contracted homogeneous simple. -/
def homogeneousNegativeFaithful (j : ι) (hj : Homogeneous χ d (S.simpleObject j)) :
    (ModuleAlphaInduction.negative (SignKernel.Positive χ) (HomogeneousCategory χ d)).Faithful where
  map_injective {X Y} f g h := by
    let n : HomogeneousCategory χ d := ⟨S.simpleObject j, hj⟩
    let a : X.obj ⟶ Y.obj := f
    let b : X.obj ⟶ Y.obj := g
    have he := congrArg (fun t => t.val.app n) h
    change a ▷ S.simpleObject j = b ▷ S.simpleObject j at he
    have ht := congrArg (ModuleFunctor.simpleContraction S (S.simpleObject j)) he
    simpa only [ModuleFunctor.simpleContraction_whiskerRight] using ht

end Paper18.Category.FixedBoundary
