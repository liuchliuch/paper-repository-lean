import P31.PowerGeometry
import Mathlib.Analysis.Convex.Function

/-! Growth at a genuine global minimizer follows from the paper's Jensen
uniform convexity convention. No growth certificate is assumed. -/

noncomputable section
open scoped BigOperators
namespace P31

variable {ι : Type*} [Fintype ι]

lemma lpPower_sub_rev (p : ℝ) (x y : ι → ℝ) : lpPower p (x - y) = lpPower p (y - x) := by
  unfold lpPower
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply, abs_sub_comm]

/-- The zero-subgradient case of equation (2.2) follows from the actual Jensen
inequality (2.1) and a true global minimizing inequality. The proof uses a finite interpolation
parameter, so requires no differentiability or limiting hypothesis. -/
theorem lpPowerJensen_min_growth {p μ : ℝ} {F : (ι → ℝ) → ℝ}
    (hJ : LpPowerJensen p μ F) {z : ι → ℝ}
    (hz : ∀ x, F z ≤ F x) (y : ι → ℝ) :
    μ / p * lpPower p (y - z) ≤ F y - F z := by
  let K := μ / p * lpPower p (y - z)
  let gap := F y - F z
  change K ≤ gap
  have hgap : 0 ≤ gap := sub_nonneg.mpr (hz y)
  by_cases hK : K ≤ 0
  · exact hK.trans hgap
  have hKpos : 0 < K := lt_of_not_ge hK
  by_contra hfail
  have hsmall : gap < K := lt_of_not_ge hfail
  let θ := (K - gap) / (2 * K)
  have hden : 0 < 2 * K := mul_pos (by norm_num) hKpos
  have hθpos : 0 < θ := div_pos (sub_pos.mpr hsmall) hden
  have hθlt : θ < 1 := (div_lt_one hden).mpr (by linarith)
  have hθeq : (2 * K) * θ = K - gap := by
    dsimp [θ]
    exact mul_div_cancel₀ _ (ne_of_gt hden)
  have hremaining : 0 < K * (1 - θ) - gap := by nlinarith [hθeq]
  have hprod : 0 < θ * (K * (1 - θ) - gap) := mul_pos hθpos hremaining
  have hj := hJ z y θ hθpos.le hθlt.le
  have hpenalty : μ / p * θ * (1 - θ) * lpPower p (z - y) = K * θ * (1 - θ) := by
    rw [lpPower_sub_rev p z y]
    dsimp [K]
    ring
  rw [hpenalty] at hj
  have hm := hz (fun i => (1 - θ) * z i + θ * y i)
  dsimp [gap] at hprod
  nlinarith [hj, hm]

/-- Subtracting an affine functional preserves the Jensen modulus exactly. -/
theorem lpPowerJensen_sub_affine {p μ : ℝ} {F : (ι → ℝ) → ℝ}
    (hJ : LpPowerJensen p μ F) (l : (ι → ℝ) →L[ℝ] ℝ) (c : ℝ) :
    LpPowerJensen p μ (fun x => F x - l x - c) := by
  intro x y θ hθ₀ hθ₁
  have hlin : l (fun i => (1 - θ) * x i + θ * y i) =
      (1 - θ) * l x + θ * l y := by
    change l ((1 - θ) • x + θ • y) = _
    rw [map_add, map_smul, map_smul]
    rfl
  have hj := hJ x y θ hθ₀ hθ₁
  dsimp only
  rw [hlin]
  linarith

/-- Full equation (2.2): every actual global supporting linear functional
at x gains the p-power term. The hypothesis is precisely the defining
supporting inequality for a subgradient, with no growth term assumed. -/
theorem lpPowerJensen_support_growth {p μ : ℝ} {F : (ι → ℝ) → ℝ}
    (hJ : LpPowerJensen p μ F) (x : ι → ℝ) (l : (ι → ℝ) →L[ℝ] ℝ)
    (hsub : ∀ u, F x + l (u - x) ≤ F u) (y : ι → ℝ) :
    F x + l (y - x) + μ / p * lpPower p (y - x) ≤ F y := by
  have hmin : ∀ u, F x - l x - 0 ≤ F u - l u - 0 := by
    intro u
    have h := hsub u
    rw [map_sub] at h
    linarith
  have hg := lpPowerJensen_min_growth (lpPowerJensen_sub_affine hJ l 0) hmin y
  rw [map_sub]
  linarith

/-- A nonnegative Jensen modulus implies ordinary convexity on the entire
finite vector space. -/
theorem lpPowerJensen_convex {p μ : ℝ} (hp : 0 < p) (hμ : 0 ≤ μ)
    {F : (ι → ℝ) → ℝ} (hJ : LpPowerJensen p μ F) : ConvexOn ℝ Set.univ F := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have haeq : a = 1 - b := by linarith
  have hb1 : b ≤ 1 := by linarith
  have hj := hJ x y b hb hb1
  have hpenalty : 0 ≤ μ / p * b * (1 - b) * lpPower p (x - y) :=
    mul_nonneg (mul_nonneg (mul_nonneg (div_nonneg hμ hp.le) hb)
      (sub_nonneg.mpr hb1)) (lpPower_nonneg p _)
  rw [haeq]
  exact hj.trans (sub_le_self _ hpenalty)

/-- The same growth estimate in the genuine finite ℓₚ norm. -/
theorem lpPowerJensen_min_growth_norm {p μ : ℝ} (hp : 0 < p)
    {F : (ι → ℝ) → ℝ} (hJ : LpPowerJensen p μ F) {z : ι → ℝ}
    (hz : ∀ x, F z ≤ F x) (y : ι → ℝ) :
    μ / p * lpNorm p (y - z) ^ p ≤ F y - F z := by
  rw [lpNorm_rpow p hp]
  exact lpPowerJensen_min_growth hJ hz y

/-- The stage objective gap contracts actual ℓₚ distance; growth is derived
from the Jensen property and minimization, rather than supplied separately. -/
theorem lpPowerJensen_stage_contraction {p μ δ : ℝ}
    (hp : 0 < p) (hμ : 0 < μ) (hδ : 0 ≤ δ)
    {F : (ι → ℝ) → ℝ} (hJ : LpPowerJensen p μ F) {z : ι → ℝ}
    (hz : ∀ x, F z ≤ F x) (y : ι → ℝ)
    (hgap : F y - F z ≤ μ / p * δ ^ p) : lpNorm p (y - z) ≤ δ := by
  have hc : 0 < μ / p := div_pos hμ hp
  have hpower := (mul_le_mul_iff_right₀ hc).mp
    ((lpPowerJensen_min_growth_norm hp hJ hz y).trans hgap)
  exact (Real.rpow_le_rpow_iff (lpNorm_nonneg p _) hδ hp).mp hpower

/-- Conversion of the contraction to mathlib's standard `PiLp` norm. -/
theorem lpPowerJensen_stage_contraction_piLp {p μ δ : ℝ}
    (hp : 0 < p) (hμ : 0 < μ) (hδ : 0 ≤ δ)
    {F : (ι → ℝ) → ℝ} (hJ : LpPowerJensen p μ F) {z : ι → ℝ}
    (hz : ∀ x, F z ≤ F x) (y : ι → ℝ)
    (hgap : F y - F z ≤ μ / p * δ ^ p) :
    ‖(WithLp.toLp (ENNReal.ofReal p) (y - z) : PiLp (ENNReal.ofReal p) (fun _ : ι => ℝ))‖ ≤ δ := by
  rw [← lpNorm_eq_piLp_norm p hp]
  exact lpPowerJensen_stage_contraction hp hμ hδ hJ hz y hgap

/-- Adding a genuine convex function preserves the regularizer's Jensen
modulus. Differentiability of the smooth summand is unnecessary here. -/
theorem lpPowerJensen_add_convex {p μ : ℝ} {f H : (ι → ℝ) → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hH : LpPowerJensen p μ H) :
    LpPowerJensen p μ (fun x => f x + H x) := by
  intro x y θ hθ₀ hθ₁
  have hc := hf.2 (Set.mem_univ x) (Set.mem_univ y)
    (sub_nonneg.mpr hθ₁) hθ₀ (show (1 - θ) + θ = 1 by ring)
  have hc' : f (fun i => (1 - θ) * x i + θ * y i) ≤ (1 - θ) * f x + θ * f y := by
    simpa only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] using hc
  have hh := hH x y θ hθ₀ hθ₁
  dsimp only
  linarith

/-- The growth bound for the paper's actual smooth objective plus a Jensen
uniformly convex accumulated regularizer. -/
theorem convex_add_lpPowerJensen_min_growth {p μ : ℝ} {f H : (ι → ℝ) → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hH : LpPowerJensen p μ H) {z : ι → ℝ}
    (hz : ∀ x, f z + H z ≤ f x + H x) (y : ι → ℝ) :
    μ / p * lpPower p (y - z) ≤ (f y + H y) - (f z + H z) :=
  lpPowerJensen_min_growth (lpPowerJensen_add_convex hf hH) hz y

end P31
