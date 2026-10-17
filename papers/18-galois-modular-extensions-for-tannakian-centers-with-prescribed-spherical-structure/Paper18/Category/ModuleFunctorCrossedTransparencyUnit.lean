import Paper18.Category.ModuleFunctorCrossedTransparency
import Paper18.Category.ModuleAlphaInductionEquivalenceHomogeneous
import Paper18.Category.TannakianDeequivariantNondegenerateBasic

/-! # A transparent invertible alpha representative gives the actual unit comparison

The nondegenerate neutral category has only unit sums in its actual center.
Actual tensor invertibility implies simplicity, so the representative is
actually isomorphic to the unit. Strong alpha induction then turns this
isomorphism into a genuine module-natural comparison with the identity.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open MonoidalOpposite
universe v u w
namespace Paper18.Category.FixedBoundary
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [RightRigidCategory C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (χ : 𝟭 C ≅ 𝟭 C) [NatTrans.IsMonoidal χ.hom] (d : ZMod 2)
  [BraidedCategory (SignKernel.Positive χ)]
local notation "Pos" => SignKernel.Positive χ
local notation "Md" => HomogeneousCategory χ d
local notation "Alpha" => ModuleAlphaInduction.negative Pos Md

include S in
/-- Actual transparent tensor-invertible objects in the actual
nondegenerate neutral category are isomorphic to its actual unit. -/
theorem invertible_transparent_unit (hC : IsNondegenerate (C := Pos))
    (Z : Pos) (aZ : TensorInverse Z) (hZ : Z ∈ mugerCenter) : Nonempty (Z ≅ 𝟙_ Pos) := by
  letI : HasKernels Pos := SignKernel.hasKernels χ S
  letI : Simple (𝟙_ Pos) := SignKernel.simpleUnit χ S
  letI : Simple Z := aZ.simple (SignKernel.skeleton χ S)
  exact iso_unit_of_simple_retract_unitSum (Retract.refl Z) (hC Z hZ)

/-- Alpha induction's genuine strong unit comparison, as an actual
isomorphism in the native category of module endofunctors. -/
def negativeAlphaUnitIso : (Alpha).obj (𝟙_ Pos) ≅ 𝟙_ (ModuleAlphaInduction.End Pos Md) :=
  ((Functor.Monoidal.εIso (ModuleAlphaInduction.negativeMop Pos Md)).unmop).symm

/-- An actual unit isomorphism of the representative yields an actual
module-natural comparison of the represented functor with the identity. -/
def negativeRepresenterComparison
    (G : ModuleAlphaInduction.End Pos Md) (Z : Pos) (b : (Alpha).obj Z ≅ G)
    (q : Z ≅ 𝟙_ Pos) : G ≅ 𝟙_ (ModuleAlphaInduction.End Pos Md) :=
  b.symm ≪≫ (Alpha).mapIso q ≪≫ negativeAlphaUnitIso χ d

end Paper18.Category.FixedBoundary
