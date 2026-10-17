import Paper18.Category.TannakianC2GeneratorBasic
import Paper18.Category.TannakianSignKernelCharacterElement
import Paper18.Category.RepresentationRightTranslation

/-!
# The actual regular C₂ algebra and its two character summands

The maps below split the actual function representation into its constant
and sign lines. Right translation is identity on the first line and minus
identity on the second. These are actual equivariant linear-map identities,
used to identify crossed monodromy with regular translation.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace Paper18.Category.FixedBoundary.C2Regular
open Representation RepresentationZ2

@[simp] lemma generator_inv : generator⁻¹ = generator := by decide
@[simp] lemma generator_mul_generator : generator * generator = (1 : H) := by decide

/-- The actual sign matrix coefficient in the regular function representation. -/
def signInclusion : signRep ⟶ functions (G := H) :=
  TannakianSignKernel.matrixCoefficient signRep LinearMap.id

@[simp] lemma signInclusion_one (z : ℂ) : (signInclusion.hom.hom z) 1 = z := by
  exact TannakianSignKernel.matrixCoefficient_one signRep LinearMap.id z

@[simp] lemma signInclusion_generator (z : ℂ) : (signInclusion.hom.hom z) generator = -z := by
  change signRep.ρ generator⁻¹ z = -z
  rw [generator_inv, signRep_generator]
  rfl

def unitProjectionLinear : (H → ℂ) →ₗ[ℂ] ℂ where
  toFun f := (f 1 + f generator) / 2
  map_add' f h := by dsimp; ring
  map_smul' z f := by dsimp; ring

def signProjectionLinear : (H → ℂ) →ₗ[ℂ] ℂ where
  toFun f := (f 1 - f generator) / 2
  map_add' f h := by dsimp; ring
  map_smul' z f := by dsimp; ring

@[simp] lemma unitProjectionLinear_apply (f : H → ℂ) :
    unitProjectionLinear f = (f 1 + f generator) / 2 := rfl

@[simp] lemma signProjectionLinear_apply (f : H → ℂ) :
    signProjectionLinear f = (f 1 - f generator) / 2 := rfl

private lemma negId_apply (z : ℂ) : (-LinearMap.id : ℂ →ₗ[ℂ] ℂ) z = -z := rfl

/-- Projection onto the actual constant line. -/
def unitProjection : functions (G := H) ⟶ 𝟙_ (FDRep ℂ H) where
  hom := ModuleCat.ofHom unitProjectionLinear
  comm g := by
    rcases eq_one_or_generator g with rfl | rfl
    · simp
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      simp only [FGModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
        FDRep.hom_action_ρ]
      rw [show (functions (G := H)).ρ = functionAction from FDRep.of_ρ' _]
      rw [show (𝟙_ (FDRep ℂ H)).ρ generator = LinearMap.id from rfl]
      erw [unitProjectionLinear_apply, unitProjectionLinear_apply,
        functionAction_apply, functionAction_apply]
      simp [add_comm]

/-- Projection onto the actual sign line. -/
def signProjection : functions (G := H) ⟶ signRep where
  hom := ModuleCat.ofHom signProjectionLinear
  comm g := by
    rcases eq_one_or_generator g with rfl | rfl
    · simp
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      simp only [FGModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
        FDRep.hom_action_ρ]
      rw [show (functions (G := H)).ρ = functionAction from FDRep.of_ρ' _]
      rw [signRep_generator]
      erw [signProjectionLinear_apply, negId_apply,
        signProjectionLinear_apply, functionAction_apply, functionAction_apply]
      simp only [generator_inv, mul_one, generator_mul_generator]
      ring

/-- The two actual equivariant summands resolve the identity of Fun(C₂). -/
theorem resolution :
    unitProjection ≫ functionsOne + signProjection ≫ signInclusion =
      𝟙 (functions (G := H)) := by
  apply Action.hom_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  funext g
  dsimp [unitProjection, signProjection, functionsOne, unitProjectionLinear, signProjectionLinear]
  rcases eq_one_or_generator g with rfl | rfl
  · change (f 1 + f generator) / 2 +
      (signInclusion.hom.hom ((f 1 - f generator) / 2)) 1 = f 1
    rw [signInclusion_one]
    ring
  · change (f 1 + f generator) / 2 +
      (signInclusion.hom.hom ((f 1 - f generator) / 2)) generator = f generator
    rw [signInclusion_generator]
    ring

/-- Actual right translation fixes the constant line. -/
theorem unit_translation :
    functionsOne (G := H) ≫ rightTranslation generator = functionsOne := by
  apply Action.hom_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  funext g
  rfl

/-- Actual right translation negates the sign line. -/
theorem sign_translation :
    signInclusion ≫ rightTranslation generator = -signInclusion := by
  apply Action.hom_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  funext g
  rcases eq_one_or_generator g with rfl | rfl
  · change (signInclusion.hom.hom z) (1 * generator) = -(signInclusion.hom.hom z 1)
    rw [one_mul, signInclusion_generator, signInclusion_one]
  · change (signInclusion.hom.hom z) (generator * generator) =
      -(signInclusion.hom.hom z generator)
    rw [generator_mul_generator, signInclusion_one, signInclusion_generator, neg_neg]

end Paper18.Category.FixedBoundary.C2Regular
