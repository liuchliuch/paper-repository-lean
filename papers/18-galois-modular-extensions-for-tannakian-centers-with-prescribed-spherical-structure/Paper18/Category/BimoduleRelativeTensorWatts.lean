import Paper18.Category.BimoduleRelativeTensorFunctorTransformation
import Paper18.Category.ModuleFunctorSemisimpleWattsFullyFaithful

/-! # Actual essential surjectivity of Eilenberg--Watts evaluation

The inverse objects are the actual relative tensor functors. Evaluation
at the regular module contracts their actual right action and recovers
both native bimodule actions.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u
namespace Paper18.Category.BimoduleRelativeTensor
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [HasCoequalizers D] [LeftRigidCategory D] [RightRigidCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
variable {R : D} [MonObj R] (P : Native R R)

lemma wattsTensor_regular_right :
    γ[mop R,(ModuleFunctor.wattsEvaluation.obj (tensorBundled P)).X] ≫
        (tensorFunctorRegularIso P).hom =
      (mop R) ⊴ₗ (tensorFunctorRegularIso P).hom ≫ γ[mop R,P.X] := by
  apply Mod_.Hom.ext
  change (lineatorRaw P (Mod_.regular R) R ≫
      ((tensorFunctor P).map
        (γ[mop R,(ModuleFunctor.wattsRegular (R := R)).X])).hom) ≫
          (tensorFunctorRegularIso P).hom.hom =
    (tensorFunctorRegularIso P).hom.hom ▷ R ≫ γ[mop R,P.X].hom
  apply (cancel_epi (moduleπ P (Mod_.regular R) ▷ R)).mp
  simp only [assoc]
  rw [moduleπ_lineatorRaw_assoc, moduleπ_map_assoc]
  change (α_ P.X.X R R).hom ≫ P.X.X ◁ μ[R] ≫
      moduleπ P (Mod_.regular R) ≫ (tensorFunctorRegularIso P).hom.hom =
    moduleπ P (Mod_.regular R) ▷ R ≫ (tensorFunctorRegularIso P).hom.hom ▷ R ≫
      γ[mop R,P.X].hom
  rw [moduleπ_regular, ← comp_whiskerRight_assoc, moduleπ_regular]
  change (α_ P.X.X R R).hom ≫ P.X.X ◁ μ[R] ≫ γ[mop R,P.X].hom =
    γ[mop R,P.X].hom ▷ R ≫ γ[mop R,P.X].hom
  have h := (toBimodObj R R P).right_assoc
  apply (cancel_epi (α_ P.X.X R R).inv).mp
  simpa only [assoc, Iso.inv_hom_id_assoc] using h

/-- Evaluation of the actual relative tensor functor returns the actual
given bimodule, including its right algebra action. -/
def wattsTensorIso : ModuleFunctor.wattsEvaluation.obj (tensorBundled P) ≅ P where
  hom := Mod_.Hom.mk' (tensorFunctorRegularIso P).hom (wattsTensor_regular_right P)
  inv := by
    letI : IsMod_Hom (mop R)
        (M := (ModuleFunctor.wattsEvaluation.obj (tensorBundled P)).X) (N := P.X)
        (tensorFunctorRegularIso P).hom :=
      ⟨wattsTensor_regular_right P⟩
    exact ⟨(tensorFunctorRegularIso P).inv⟩
  hom_inv_id := by apply Mod_.Hom.ext; exact (tensorFunctorRegularIso P).hom_inv_id
  inv_hom_id := by apply Mod_.Hom.ext; exact (tensorFunctorRegularIso P).inv_hom_id

instance wattsEvaluation_essSurj : (ModuleFunctor.wattsEvaluation (R := R)).EssSurj where
  mem_essImage P := ⟨tensorBundled P, ⟨wattsTensorIso P⟩⟩

/-- For an actual separable algebra, genuine strong ambient module
endofunctors are equivalent to genuine native bimodules. -/
def wattsEquivalence (Sep : SeparableAlgebra R) :
    ModuleFunctor.Bundled Dᴹᵒᵖ (Mod_ D R) (Mod_ D R) ≌ Native R R := by
  letI := ModuleFunctor.wattsEvaluation_full Sep
  letI := ModuleFunctor.wattsEvaluation_faithful Sep
  letI : (ModuleFunctor.wattsEvaluation (R := R)).IsEquivalence := {}
  exact (ModuleFunctor.wattsEvaluation (R := R)).asEquivalence

end Paper18.Category.BimoduleRelativeTensor
