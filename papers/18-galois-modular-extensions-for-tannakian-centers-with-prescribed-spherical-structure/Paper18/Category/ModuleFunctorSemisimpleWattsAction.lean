import Paper18.Category.ModuleFunctorSemisimpleBimodules
import Paper18.Category.InternalModuleAmbientFree
import Paper18.Category.ModuleFunctorFiniteActionIso
import Paper18.Category.ModuleFunctorSemisimpleModuleMap

/-! # Actual free resolution and regular bimodule for Eilenberg--Watts -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u
namespace Paper18.Category.ModuleFunctor
open MonoidalLeftAction
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  {R : D} [MonObj R]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

/-- Forgetting an actual left module gives an object of the regular
module category for the monoidal opposite. -/
def wattsForget : Mod_ D R ⥤ Dᴹᵒᵖ := Mod_.forget R ⋙ mopFunctor D

/-- The underlying right tensor action is preserved identically. -/
def wattsForgetLaxLeftLinear : (wattsForget (R := R)).LaxLeftLinear Dᴹᵒᵖ where
  μₗ X M := 𝟙 _
  μₗ_naturality_left f M := by simp only [comp_id, id_comp]; rfl
  μₗ_naturality_right X M N f := by simp only [comp_id, id_comp]; rfl
  μₗ_associativity X Y M := by
    simp only [id_comp, actionHomRight_id, comp_id]
    rfl
  μₗ_unitality M := by simp only [id_comp]; rfl

instance wattsForgetLeftLinear : (wattsForget (R := R)).LeftLinear Dᴹᵒᵖ := by
  letI := wattsForgetLaxLeftLinear (R := R)
  letI (X : Dᴹᵒᵖ) (M : Mod_ D R) :
      IsIso (Functor.LaxLeftLinear.μₗ (wattsForget (R := R)) X M) :=
    inferInstanceAs (IsIso (𝟙 _))
  exact leftLinearOfLax (wattsForget (R := R))

/-- The regular algebra has its actual right multiplication as a second
native module action. -/
def wattsRegular : Bimodules R := by
  let Q := Mod_.regular R
  let a : (mop R) ⊙ₗ Q ⟶ Q := Mod_.Hom.mk' μ[R] (by
    change ((α_ R R R).inv ≫ μ[R] ▷ R) ≫ μ[R] = (R ◁ μ[R]) ≫ μ[R]
    rw [assoc, MonObj.mul_assoc, Iso.inv_hom_id_assoc])
  letI : ModObj (mop R) Q :=
    { smul := a
      one_smul' := by
        apply Mod_.Hom.ext
        change R ◁ η[R] ≫ μ[R] = (ρ_ R).hom
        exact MonObj.mul_one R
      mul_smul' := by
        apply Mod_.Hom.ext
        change R ◁ μ[R] ≫ μ[R] = (α_ R R R).inv ≫ μ[R] ▷ R ≫ μ[R]
        rw [MonObj.mul_assoc, Iso.inv_hom_id_assoc] }
  exact ⟨Q⟩

@[simp] lemma wattsRegular_X : (wattsRegular (R := R)).X = Mod_.regular R := rfl

variable [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]

/-- Evaluating a genuine strong module functor on the regular algebra
transports its actual right multiplication action. -/
def wattsEvaluationObject (F : Bundled Dᴹᵒᵖ (Mod_ D R) (Mod_ D R)) : Bimodules R :=
  mapActionModule F.toFunctor wattsRegular

/-- The actual evaluation functor to genuine bimodules. -/
def wattsEvaluation : Bundled Dᴹᵒᵖ (Mod_ D R) (Mod_ D R) ⥤ Bimodules R where
  obj := wattsEvaluationObject
  map τ := (mapActionModulesTransformation τ.val).app wattsRegular
  map_id F := by apply Mod_.Hom.ext; rfl
  map_comp τ σ := by apply Mod_.Hom.ext; rfl

end Paper18.Category.ModuleFunctor
