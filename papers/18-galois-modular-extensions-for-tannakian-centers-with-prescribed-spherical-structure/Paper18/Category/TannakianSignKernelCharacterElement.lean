import Paper18.Category.TannakianSignKernelCharacter
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Actual tensor characters of finite group representations are central actions -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped TensorProduct
namespace Paper18.Category.TannakianSignKernel
open Representation
variable {G : Type} [Group G] [Fintype G]

/-- Actual equivariant matrix coefficients, with the inverse in the
coefficient variable matching the left regular function action. -/
def matrixCoefficient (V : FDRep ℂ G) (ℓ : Module.Dual ℂ V) : V ⟶ functions where
  hom := ModuleCat.ofHom (LinearMap.pi (fun g => ℓ.comp (V.ρ g⁻¹)))
  comm g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    funext x
    change ℓ (V.ρ x⁻¹ (V.ρ g v)) = ℓ (V.ρ ((g⁻¹ * x)⁻¹) v)
    simp only [mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply]

@[simp] lemma matrixCoefficient_apply (V : FDRep ℂ G) (ℓ : Module.Dual ℂ V)
    (v : V) (g : G) : (matrixCoefficient V ℓ).hom.hom v g = ℓ (V.ρ g⁻¹ v) := rfl

@[simp] lemma matrixCoefficient_one (V : FDRep ℂ G) (ℓ : Module.Dual ℂ V) (v : V) :
    (matrixCoefficient V ℓ).hom.hom v 1 = ℓ v := by
  rw [matrixCoefficient_apply, inv_one, map_one]
  rfl

variable (χ : 𝟭 (FDRep ℂ G) ≅ 𝟭 (FDRep ℂ G)) [NatTrans.IsMonoidal χ.hom]

/-- Naturality with actual matrix coefficients determines every actual
component of the tensor automorphism from its selected regular-function point. -/
lemma component_eq_action_inverse (V : FDRep ℂ G) :
    (χ.hom.app V).hom.hom = V.ρ (evaluationPoint χ)⁻¹ := by
  apply LinearMap.ext
  intro v
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
  intro ℓ
  rw [map_sub]
  apply sub_eq_zero.mpr
  have hn := χ.hom.naturality (matrixCoefficient V ℓ)
  have h := congrArg (fun k : V ⟶ functions => k.hom.hom v 1) hn
  change functionsLinear χ ((matrixCoefficient V ℓ).hom.hom v) 1 =
    (matrixCoefficient V ℓ).hom.hom ((χ.hom.app V).hom.hom v) 1 at h
  rw [matrixCoefficient_one] at h
  change evaluationCharacter χ ((matrixCoefficient V ℓ).hom.hom v) = _ at h
  rw [evaluationCharacter_eq, matrixCoefficient_apply] at h
  exact h.symm

/-- Naturality with actual right translations makes the recovered point central. -/
lemma evaluationPoint_central (g : G) : evaluationPoint χ * g = g * evaluationPoint χ := by
  have hf (f : G → ℂ) : f (evaluationPoint χ * g) = f (g * evaluationPoint χ) := by
    have hn := χ.hom.naturality (rightTranslation g)
    have h := congrArg (fun k : functions ⟶ functions => k.hom.hom f 1) hn
    change functionsLinear χ (rightTranslationLinear g f) 1 =
      rightTranslationLinear g (functionsLinear χ f) 1 at h
    simpa only [functionsLinear_apply, one_mul, rightTranslationLinear_apply] using h
  by_contra hn
  simpa [delta_apply, Ne.symm hn] using hf (delta (evaluationPoint χ * g))

/-- The actual central element acting by the character on every representation. -/
def characterElement : G := (evaluationPoint χ)⁻¹

lemma characterElement_central (g : G) : characterElement χ * g = g * characterElement χ :=
  (show Commute (evaluationPoint χ) g from evaluationPoint_central χ g).inv_left.eq

lemma component_eq_action (V : FDRep ℂ G) :
    (χ.hom.app V).hom.hom = V.ρ (characterElement χ) := component_eq_action_inverse χ V

lemma characterElement_sq
    (hχ : ∀ V : FDRep ℂ G, χ.hom.app V ≫ χ.hom.app V = 𝟙 V) :
    characterElement χ * characterElement χ = 1 := by
  have hp : evaluationPoint χ * evaluationPoint χ = 1 := by
    have h := congrArg (fun k : functions ⟶ functions => k.hom.hom (delta 1) 1) (hχ functions)
    change functionsLinear χ (functionsLinear χ (delta 1)) 1 = delta 1 1 at h
    rw [functionsLinear_apply, functionsLinear_apply] at h
    simp only [one_mul] at h
    by_contra hn
    simpa [delta_apply, hn] using h
  simp only [characterElement, ← mul_inv_rev, hp, inv_one]

end Paper18.Category.TannakianSignKernel
