import Paper18.Category.ModuleAlphaInductionEquivalence
import Paper18.Category.ModuleFunctorFiniteRepresentable

/-! # Actual invertible neutral representers for homogeneous autoequivalences -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
universe v u w
namespace Paper18.Category.FixedBoundary
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [RightRigidCategory C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (χ : 𝟭 C ≅ 𝟭 C) [NatTrans.IsMonoidal χ.hom] (d : ZMod 2)
  [BraidedCategory (SignKernel.Positive χ)]
  (L : SignKernel.Positive χ ⥤ Center C)
  (e : SignKernel.inclusion χ ≅ L ⋙ Center.forget C)
  (hL : NegativeCentralCompatibility χ L e)
  (j : ι) (hj : Homogeneous χ d (S.simpleObject j))

local notation "Pos" => SignKernel.Positive χ
local notation "Md" => HomogeneousCategory χ d
local notation "Alpha" => ModuleAlphaInduction.negative Pos Md

/-- The actual homogeneous alpha equivalence with its correct tensor convention. -/
def homogeneousNegativeMonoidalEquivalence :
    Pos ≌ (ModuleAlphaInduction.End Pos Md)ᴹᵒᵖ := by
  letI : (Alpha).IsEquivalence :=
    (homogeneousNegativeEquivalence S χ d L e hL j hj).isEquivalence_functor
  exact ModuleAlphaInduction.negativeMonoidalEquivalence Pos Md

instance homogeneousNegativeMonoidalEquivalence_functor_monoidal :
    (homogeneousNegativeMonoidalEquivalence S χ d L e hL j hj).functor.Monoidal :=
  inferInstanceAs (ModuleAlphaInduction.negativeMop Pos Md).Monoidal

/-- The actual inverse has a genuine monoidal structure, derived from the
actual strong forward functor and actual equivalence unit and counit. -/
def homogeneousNegativeMonoidalEquivalence_inverse_monoidal :
    (homogeneousNegativeMonoidalEquivalence S χ d L e hL j hj).inverse.Monoidal :=
  (homogeneousNegativeMonoidalEquivalence S χ d L e hL j hj).inverseMonoidal

/-- The actual unit and counit also obey the monoidal equivalence laws. -/
def homogeneousNegativeMonoidalEquivalence_isMonoidal :
    letI := homogeneousNegativeMonoidalEquivalence_inverse_monoidal S χ d L e hL j hj
    (homogeneousNegativeMonoidalEquivalence S χ d L e hL j hj).IsMonoidal := by
  letI := homogeneousNegativeMonoidalEquivalence_inverse_monoidal S χ d L e hL j hj
  infer_instance

/-- The previously constructed representing object of an actual homogeneous
module autoequivalence has a genuine two-sided tensor inverse. -/
def homogeneousRepresentativeTensorInverse
    (F : ModuleAlphaInduction.End Pos Md) [F.toFunctor.IsEquivalence] :
    TensorInverse (homogeneousRepresentative S χ d L e hL j hj F) := by
  letI : RightRigidCategory Pos := SignKernel.rightRigid χ S
  letI : (Alpha).IsEquivalence :=
    (homogeneousNegativeEquivalence S χ d L e hL j hj).isEquivalence_functor
  exact ModuleAlphaInduction.tensorInverseOfImageIso
    (ModuleAlphaInduction.negativeMop Pos Md)
    (Iso.mop (homogeneousRepresentativeIso S χ d L e hL j hj F))
    (ModuleAlphaInduction.tensorInverseMop (ModuleAlphaInduction.endTensorInverse Pos Md F))

/-- The neutral representing object is genuinely invertible in the ambient
category as well, through the actual strong neutral inclusion. -/
def homogeneousRepresentativeAmbientTensorInverse
    (F : ModuleAlphaInduction.End Pos Md) [F.toFunctor.IsEquivalence] :
    TensorInverse (homogeneousRepresentative S χ d L e hL j hj F).obj :=
  (homogeneousRepresentativeTensorInverse S χ d L e hL j hj F).map (SignKernel.inclusion χ)

include S L e hL j hj in
/-- Actual invertibility and module-natural representation, without any
representability or tensor-inverse premise in the input. -/
theorem exists_invertible_homogeneous_representer
    (F : ModuleAlphaInduction.End Pos Md) [F.toFunctor.IsEquivalence] :
    ∃ Z : Pos, Nonempty (TensorInverse Z) ∧ Nonempty ((Alpha).obj Z ≅ F) :=
  ⟨homogeneousRepresentative S χ d L e hL j hj F,
    ⟨homogeneousRepresentativeTensorInverse S χ d L e hL j hj F⟩,
    ⟨homogeneousRepresentativeIso S χ d L e hL j hj F⟩⟩

end Paper18.Category.FixedBoundary
