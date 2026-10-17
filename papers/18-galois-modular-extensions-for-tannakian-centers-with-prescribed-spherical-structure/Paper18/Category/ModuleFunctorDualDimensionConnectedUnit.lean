import Paper18.Category.ModuleFunctorDualDimensionCharacter
import Paper18.Category.ModuleFunctorFiniteDensity

/-! # Actual connected action forces a simple End tensor unit -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonoidalLeftAction
universe v u vM uM w wE
namespace Paper18.Category.ModuleFunctor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {M : Type uM} [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [HasKernels M] [HasFiniteBiproducts M] [∀ X Y : M, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalLeftAction C M]
  [∀ c : C, (MonoidalLeftAction.actionLeft M c).Additive]
  [∀ c : C, (MonoidalLeftAction.actionLeft M c).Linear ℂ]
  {κ : Type w} [Fintype κ] (SM : FiniteSemisimpleSkeleton M κ) (j₀ : κ)
  (hconn : ∀ j k : κ, ∃ X : C, Nonempty (Retract (SM.simpleObject k) (X ⊙ₗ SM.simpleObject j)))

omit [HasKernels M] [∀ X Y : M, FiniteDimensional ℂ (X ⟶ Y)] in
include hconn in
/-- Actual retract connectivity makes one-simple evaluation injective on
all module natural transformations. -/
lemma connected_moduleEndEvaluation_injective (F G : ModuleAlphaInduction.End C M) :
    Function.Injective ((moduleEndEvaluation (C := C) (SM.simpleObject j₀)).mapLinearMap ℂ
      (X := F) (Y := G)) := by
  intro τ σ h
  apply Subtype.ext
  apply natTrans_ext_simples SM F.toFunctor G.toFunctor
  intro k
  obtain ⟨X, ⟨q⟩⟩ := hconn j₀ k
  exact natTrans_app_eq_of_retract τ.val σ.val q
    (moduleNatTrans_app_action_eq τ.val σ.val X (SM.simpleObject j₀) h)

include j₀ hconn in
/-- The actual tensor-unit endomorphism space has dimension one. -/
lemma connected_moduleEndUnit_finrank :
    Module.finrank ℂ (𝟙_ (ModuleAlphaInduction.End C M) ⟶ 𝟙_ (ModuleAlphaInduction.End C M)) = 1 := by
  let E := ModuleAlphaInduction.endUnit C M
  letI : ∀ F G : ModuleAlphaInduction.End C M, FiniteDimensional ℂ (F ⟶ G) :=
    finiteDimensionalHom SM
  have hle := LinearMap.finrank_le_finrank_of_injective
    (connected_moduleEndEvaluation_injective SM j₀ hconn E E)
  change Module.finrank ℂ (E ⟶ E) ≤
    Module.finrank ℂ (SM.simpleObject j₀ ⟶ SM.simpleObject j₀) at hle
  rw [CategoryTheory.finrank_endomorphism_simple_eq_one ℂ (SM.simpleObject j₀)] at hle
  have hn : (𝟙 E : E ⟶ E) ≠ 0 := by
    intro hz
    have h := congrArg (fun τ : E ⟶ E => τ.val.app (SM.simpleObject j₀)) hz
    exact CategoryTheory.id_nonzero (SM.simpleObject j₀) h
  have hp : 0 < Module.finrank ℂ (E ⟶ E) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨𝟙 E, hn⟩
  change Module.finrank ℂ (E ⟶ E) = 1
  omega

variable [HasKernels (ModuleAlphaInduction.End C M)]
  {ε : Type wE} [Fintype ε]
  (TE : FiniteSemisimpleSkeleton (ModuleAlphaInduction.End C M) ε)

include j₀ hconn in
/-- A genuine End skeleton and actual action connectivity give actual
simplicity of its tensor unit, with no Schur certificate. -/
def connected_moduleEndSimpleUnit : Simple (𝟙_ (ModuleAlphaInduction.End C M)) := by
  letI : ∀ F G : ModuleAlphaInduction.End C M, FiniteDimensional ℂ (F ⟶ G) :=
    finiteDimensionalHom SM
  exact TE.simple_of_finrank_end_eq_one _ (connected_moduleEndUnit_finrank SM j₀ hconn)

end Paper18.Category.ModuleFunctor
