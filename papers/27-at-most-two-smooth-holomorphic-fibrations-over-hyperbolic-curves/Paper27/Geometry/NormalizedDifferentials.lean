import Paper27.Geometry.CovectorGauges
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Actual ambient differentials along a normalized curve coordinate

The coefficient functions here are defined from actual `fderiv` values, and the
normalization tangent is the actual `deriv` of `ν : ℂ → ℂ × ℂ`. Analyticity,
the zero determinant, and the two derivative chain rules are proved from the
ambient analytic maps. In particular, no scalar, unit germ, chain rule, or
ramification-order comparison is among the inputs to the final theorem.

This is the local coordinate bridge. Passing from arbitrary complex manifold
charts and a normalization map to these actual analytic functions, and matching
their compositions with written coordinates of restricted maps, is not packaged
in this file.
-/

noncomputable section

open scoped Topology
open Filter

namespace Paper27.Geometry.NormalizedDifferentials

/-- The actual first component of the pulled-back ambient differential. -/
def coefficientOne (F : (ℂ × ℂ) → ℂ) (ν : ℂ → ℂ × ℂ) (z : ℂ) : ℂ :=
  fderiv ℂ F (ν z) (1, 0)

/-- The actual second component of the pulled-back ambient differential. -/
def coefficientTwo (F : (ℂ × ℂ) → ℂ) (ν : ℂ → ℂ × ℂ) (z : ℂ) : ℂ :=
  fderiv ℂ F (ν z) (0, 1)

/-- The first component of the actual normalization derivative; it may vanish. -/
def tangentOne (ν : ℂ → ℂ × ℂ) (z : ℂ) : ℂ := (deriv ν z).1

/-- The second component of the actual normalization derivative. -/
def tangentTwo (ν : ℂ → ℂ × ℂ) (z : ℂ) : ℂ := (deriv ν z).2

/-- The actual covector evaluated on a vector is the sum of its two coordinate
contributions, proved by decomposing the vector in the standard basis. -/
theorem covector_apply (l : (ℂ × ℂ) →L[ℂ] ℂ) (v : ℂ × ℂ) :
    l v = l (1, 0) * v.1 + l (0, 1) * v.2 := by
  have hv : v = v.1 • (1, 0) + v.2 • (0, 1) := by
    apply Prod.ext <;> simp
  calc
    l v = l (v.1 • (1, 0) + v.2 • (0, 1)) := congrArg l hv
    _ = l (1, 0) * v.1 + l (0, 1) * v.2 := by
      simp only [map_add, map_smul, smul_eq_mul]
      ring

/-- Surjectivity of an actual covector forces one of its actual coordinate
components to be nonzero. -/
theorem nonzero_component_of_surjective (l : (ℂ × ℂ) →L[ℂ] ℂ)
    (hl : Function.Surjective l) : l (1, 0) ≠ 0 ∨ l (0, 1) ≠ 0 := by
  by_cases h₁ : l (1, 0) = 0
  · right
    intro h₂
    obtain ⟨v, hv⟩ := hl 1
    have hzero : l v = 0 := by
      rw [covector_apply, h₁, h₂, zero_mul, zero_mul, zero_add]
    exact one_ne_zero (hv.symm.trans hzero)
  · exact Or.inl h₁

/-- Failure of surjectivity of the actual joint covector forces determinant
zero. The proof constructs a preimage by the inverse matrix formula if the
determinant were nonzero; no individual surjectivity near the centre is needed. -/
theorem determinant_zero_of_joint_not_surjective
    (l₁ l₂ : (ℂ × ℂ) →L[ℂ] ℂ)
    (hjoint : ¬ Function.Surjective (fun v : ℂ × ℂ => (l₁ v, l₂ v))) :
    l₁ (1, 0) * l₂ (0, 1) = l₁ (0, 1) * l₂ (1, 0) := by
  by_contra hdet
  let Δ := l₁ (1, 0) * l₂ (0, 1) - l₁ (0, 1) * l₂ (1, 0)
  have hΔ : Δ ≠ 0 := sub_ne_zero.mpr hdet
  apply hjoint
  intro ab
  refine ⟨((l₂ (0, 1) * ab.1 - l₁ (0, 1) * ab.2) / Δ,
    (l₁ (1, 0) * ab.2 - l₂ (1, 0) * ab.1) / Δ), ?_⟩
  apply Prod.ext
  · change l₁ _ = ab.1
    rw [covector_apply]
    change l₁ (1, 0) * ((l₂ (0, 1) * ab.1 - l₁ (0, 1) * ab.2) / Δ) +
      l₁ (0, 1) * ((l₁ (1, 0) * ab.2 - l₂ (1, 0) * ab.1) / Δ) = ab.1
    field_simp
    dsimp [Δ]
    ring
  · change l₂ _ = ab.2
    rw [covector_apply]
    change l₂ (1, 0) * ((l₂ (0, 1) * ab.1 - l₁ (0, 1) * ab.2) / Δ) +
      l₂ (0, 1) * ((l₁ (1, 0) * ab.2 - l₂ (1, 0) * ab.1) / Δ) = ab.2
    field_simp
    dsimp [Δ]
    ring

/-- Analyticity of the actual first differential coefficient follows from
analyticity of `fderiv F`, composition with `ν`, and continuous-linear evaluation. -/
theorem analytic_coefficientOne {F : (ℂ × ℂ) → ℂ} {ν : ℂ → ℂ × ℂ} {z₀ : ℂ}
    (hF : AnalyticAt ℂ F (ν z₀)) (hν : AnalyticAt ℂ ν z₀) :
    AnalyticAt ℂ (coefficientOne F ν) z₀ := by
  have hd : AnalyticAt ℂ (fun z => fderiv ℂ F (ν z)) z₀ := hF.fderiv.comp hν
  exact ((ContinuousLinearMap.apply ℂ ℂ (1, 0)).analyticAt _).comp hd

/-- The same statement for the actual second differential coefficient. -/
theorem analytic_coefficientTwo {F : (ℂ × ℂ) → ℂ} {ν : ℂ → ℂ × ℂ} {z₀ : ℂ}
    (hF : AnalyticAt ℂ F (ν z₀)) (hν : AnalyticAt ℂ ν z₀) :
    AnalyticAt ℂ (coefficientTwo F ν) z₀ := by
  have hd : AnalyticAt ℂ (fun z => fderiv ℂ F (ν z)) z₀ := hF.fderiv.comp hν
  exact ((ContinuousLinearMap.apply ℂ ℂ (0, 1)).analyticAt _).comp hd

/-- The chain rule for actual derivatives, expressed in the actual coordinate
coefficients and the actual normalization tangent. -/
theorem derivative_chain_germ {F : (ℂ × ℂ) → ℂ} {ν : ℂ → ℂ × ℂ} {z₀ : ℂ}
    (hF : AnalyticAt ℂ F (ν z₀)) (hν : AnalyticAt ℂ ν z₀) :
    deriv (F ∘ ν) =ᶠ[𝓝 z₀] fun z =>
      coefficientOne F ν z * tangentOne ν z + coefficientTwo F ν z * tangentTwo ν z := by
  have hFnear : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ F (ν z) :=
    hν.continuousAt.tendsto.eventually hF.eventually_analyticAt
  filter_upwards [hFnear, hν.eventually_analyticAt] with z hFz hνz
  have hchain : HasDerivAt (F ∘ ν) (fderiv ℂ F (ν z) (deriv ν z)) z :=
    hFz.differentiableAt.hasFDerivAt.comp_hasDerivAt z hνz.differentiableAt.hasDerivAt
  rw [hchain.deriv]
  exact covector_apply _ _

/-- All raw data required by the covector-gauge construction, with coefficient
and tangent functions fixed to actual differential formulas. -/
structure ActualCovectorData (F G : (ℂ × ℂ) → ℂ) (ν : ℂ → ℂ × ℂ) (z₀ : ℂ) : Prop where
  analytic_A₁ : AnalyticAt ℂ (coefficientOne F ν) z₀
  analytic_A₂ : AnalyticAt ℂ (coefficientTwo F ν) z₀
  analytic_B₁ : AnalyticAt ℂ (coefficientOne G ν) z₀
  analytic_B₂ : AnalyticAt ℂ (coefficientTwo G ν) z₀
  nonzero_A : coefficientOne F ν z₀ ≠ 0 ∨ coefficientTwo F ν z₀ ≠ 0
  nonzero_B : coefficientOne G ν z₀ ≠ 0 ∨ coefficientTwo G ν z₀ ≠ 0
  determinant_zero : ∀ᶠ z in 𝓝 z₀,
    coefficientOne F ν z * coefficientTwo G ν z =
      coefficientTwo F ν z * coefficientOne G ν z
  chain_F : deriv (F ∘ ν) =ᶠ[𝓝 z₀] fun z =>
    coefficientOne F ν z * tangentOne ν z + coefficientTwo F ν z * tangentTwo ν z
  chain_G : deriv (G ∘ ν) =ᶠ[𝓝 z₀] fun z =>
    coefficientOne G ν z * tangentOne ν z + coefficientTwo G ν z * tangentTwo ν z

/-- Actual ambient maps produce all the raw covector data. Only centre
surjectivity is required; nearby individual surjectivity is not an extra input. -/
theorem actual_covector_data {F G : (ℂ × ℂ) → ℂ} {ν : ℂ → ℂ × ℂ} {z₀ : ℂ}
    (hF : AnalyticAt ℂ F (ν z₀)) (hG : AnalyticAt ℂ G (ν z₀))
    (hν : AnalyticAt ℂ ν z₀)
    (hsurjF : Function.Surjective (fderiv ℂ F (ν z₀)))
    (hsurjG : Function.Surjective (fderiv ℂ G (ν z₀)))
    (hjoint : ∀ᶠ z in 𝓝 z₀, ¬ Function.Surjective
      (fun v : ℂ × ℂ => (fderiv ℂ F (ν z) v, fderiv ℂ G (ν z) v))) :
    ActualCovectorData F G ν z₀ where
  analytic_A₁ := analytic_coefficientOne hF hν
  analytic_A₂ := analytic_coefficientTwo hF hν
  analytic_B₁ := analytic_coefficientOne hG hν
  analytic_B₂ := analytic_coefficientTwo hG hν
  nonzero_A := nonzero_component_of_surjective _ hsurjF
  nonzero_B := nonzero_component_of_surjective _ hsurjG
  determinant_zero := hjoint.mono fun _ hz =>
    determinant_zero_of_joint_not_surjective _ _ hz
  chain_F := derivative_chain_germ hF hν
  chain_G := derivative_chain_germ hG hν

/-- The unit germ between the actual restricted derivatives is constructed
from the actual analytic ambient maps and joint differential degeneration. -/
theorem derivative_unit_germ_of_joint_not_surjective
    {F G : (ℂ × ℂ) → ℂ} {ν : ℂ → ℂ × ℂ} {z₀ : ℂ}
    (hF : AnalyticAt ℂ F (ν z₀)) (hG : AnalyticAt ℂ G (ν z₀))
    (hν : AnalyticAt ℂ ν z₀)
    (hsurjF : Function.Surjective (fderiv ℂ F (ν z₀)))
    (hsurjG : Function.Surjective (fderiv ℂ G (ν z₀)))
    (hjoint : ∀ᶠ z in 𝓝 z₀, ¬ Function.Surjective
      (fun v : ℂ × ℂ => (fderiv ℂ F (ν z) v, fderiv ℂ G (ν z) v))) :
    ∃ unit : ℂ → ℂ, AnalyticAt ℂ unit z₀ ∧ unit z₀ ≠ 0 ∧
      deriv (G ∘ ν) =ᶠ[𝓝 z₀] unit * deriv (F ∘ ν) := by
  have data := actual_covector_data hF hG hν hsurjF hsurjG hjoint
  exact CovectorGauges.derivative_unit_germ data.analytic_A₁ data.analytic_A₂
    data.analytic_B₁ data.analytic_B₂ data.nonzero_A data.nonzero_B data.determinant_zero
    data.chain_F data.chain_G

/-- Consequently the actual orders of the restricted derivatives agree. -/
theorem derivative_orders_equal_of_joint_not_surjective
    {F G : (ℂ × ℂ) → ℂ} {ν : ℂ → ℂ × ℂ} {z₀ : ℂ}
    (hF : AnalyticAt ℂ F (ν z₀)) (hG : AnalyticAt ℂ G (ν z₀))
    (hν : AnalyticAt ℂ ν z₀)
    (hsurjF : Function.Surjective (fderiv ℂ F (ν z₀)))
    (hsurjG : Function.Surjective (fderiv ℂ G (ν z₀)))
    (hjoint : ∀ᶠ z in 𝓝 z₀, ¬ Function.Surjective
      (fun v : ℂ × ℂ => (fderiv ℂ F (ν z) v, fderiv ℂ G (ν z) v))) :
    analyticOrderNatAt (deriv (G ∘ ν)) z₀ = analyticOrderNatAt (deriv (F ∘ ν)) z₀ := by
  obtain ⟨unit, hunit, hunit0, hrel⟩ :=
    derivative_unit_germ_of_joint_not_surjective hF hG hν hsurjF hsurjG hjoint
  exact RamificationCovectors.derivative_orders_eq_of_unit_relation
    hunit (hF.comp hν).deriv hunit0 hrel

end Paper27.Geometry.NormalizedDifferentials
