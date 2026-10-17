import Paper18.Category.BimoduleRelativeTensorWatts
import Paper18.Category.BimoduleRelativeTensorMonoidal

/-! # The actual strong monoidal inverse to Eilenberg--Watts evaluation -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u
namespace Paper18.Category.BimoduleRelativeTensor
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [HasCoequalizers D] [LeftRigidCategory D] [RightRigidCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction nativeMonoidal
variable {R : D} [MonObj R]

/-- The actual regular-module contraction is natural for both bimodule
actions, and identifies the composite with actual evaluation. -/
def tensorEvaluationRoundtripIso :
    tensorRepresentation (R := R) (S := R) ⋙ ModuleFunctor.wattsEvaluation ≅
      𝟭 (Native R R) :=
  NatIso.ofComponents wattsTensorIso (by
    intro P Q f
    apply Mod_.Hom.ext
    apply Mod_.Hom.ext
    change ((tensorNat f).app (Mod_.regular R)).hom ≫
        (tensorFunctorRegularIso Q).hom.hom =
      (tensorFunctorRegularIso P).hom.hom ≫ f.hom.hom
    apply (cancel_epi (moduleπ P (Mod_.regular R))).mp
    rw [moduleπ_tensorNat_assoc, moduleπ_regular, moduleπ_regular_assoc]
    exact (congrArg Mod_.Hom.hom f.isMod_Hom.smul_hom).symm)

/-- Actual relative tensor is an equivalence, by the actual natural
roundtrip and the independently proved full faithful evaluation functor. -/
def tensorRepresentationIsEquivalence (Sep : SeparableAlgebra R) :
    (tensorRepresentation (R := R) (S := R)).IsEquivalence := by
  letI : (ModuleFunctor.wattsEvaluation (R := R)).IsEquivalence :=
    (wattsEquivalence Sep).isEquivalence_functor
  letI : (tensorRepresentation (R := R) (S := R) ⋙
      ModuleFunctor.wattsEvaluation).IsEquivalence :=
    Functor.isEquivalence_of_iso tensorEvaluationRoundtripIso.symm
  exact Functor.isEquivalence_of_comp_right tensorRepresentation ModuleFunctor.wattsEvaluation

/-- Reversing composition gives the ordinary equivalence underlying the
strong monoidal Eilenberg--Watts equivalence. -/
def reverseRepresentationIsEquivalence (Sep : SeparableAlgebra R) :
    (reverseRepresentation R).IsEquivalence := by
  letI := tensorRepresentationIsEquivalence Sep
  change (tensorRepresentation ⋙ mopFunctor (ModuleEnd R)).IsEquivalence
  infer_instance

/-- The forward functor is precisely actual relative tensor, with
codomain the monoidal opposite of the native strong module endofunctors. -/
def reverseWattsEquivalence (Sep : SeparableAlgebra R) :
    Native R R ≌ (ModuleEnd R)ᴹᵒᵖ := by
  letI := reverseRepresentationIsEquivalence Sep
  exact (reverseRepresentation R).asEquivalence

instance reverseWattsEquivalence_monoidal (Sep : SeparableAlgebra R) :
    (reverseWattsEquivalence Sep).functor.Monoidal :=
  reverseRepresentationMonoidal R

instance reverseWattsEquivalence_inverseMonoidal (Sep : SeparableAlgebra R) :
    (reverseWattsEquivalence Sep).inverse.Monoidal :=
  (reverseWattsEquivalence Sep).inverseMonoidal

instance reverseWattsEquivalence_isMonoidal (Sep : SeparableAlgebra R) :
    (reverseWattsEquivalence Sep).IsMonoidal := by
  infer_instance

end Paper18.Category.BimoduleRelativeTensor
