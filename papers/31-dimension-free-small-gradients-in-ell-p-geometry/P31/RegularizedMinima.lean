import P31.JensenGrowth
import Mathlib.Topology.Order.Compact

/-! Actual existence and uniqueness of the finite accumulated regularized
objectives used for the analytical minimizers in Section 3. The compactness
argument is proved in coordinates; the scalar Clarkson theorem is the only
external geometric input. -/

noncomputable section
open scoped BigOperators
namespace P31
variable {ι : Type*} [Fintype ι]

/-- A positive shifted-power lower bound places every sublevel inside an
explicit finite coordinate box. -/
theorem power_lower_sublevel_box {p A b r : ℝ} (hp : 1 ≤ p) (hA : 0 < A)
    {F : (ι → ℝ) → ℝ} (c : ι → ℝ)
    (hlower : ∀ x, b + A * lpPower p (x - c) ≤ F x) :
    {x | F x ≤ r} ⊆ Set.Icc
      (fun i => c i - (1 + max 0 ((r - b) / A)))
      (fun i => c i + (1 + max 0 ((r - b) / A))) := by
  intro x hx
  have hsum : A * lpPower p (x - c) ≤ r - b := by
    have hl := hlower x
    change F x ≤ r at hx
    linarith
  have hcoord (i : ι) : |x i - c i| ≤ 1 + max 0 ((r - b) / A) := by
    have hsingle : |x i - c i| ^ p ≤ lpPower p (x - c) :=
      Finset.single_le_sum (fun j _ => Real.rpow_nonneg (abs_nonneg ((x - c) j)) p)
        (Finset.mem_univ i)
    have hterm : |x i - c i| ^ p ≤ (r - b) / A := by
      apply (le_div_iff₀ hA).mpr
      have hm := mul_le_mul_of_nonneg_left hsingle hA.le
      nlinarith
    by_cases hsmall : |x i - c i| ≤ 1
    · exact hsmall.trans (le_add_of_nonneg_right (le_max_left _ _))
    · have hlarge : 1 ≤ |x i - c i| := (lt_of_not_ge hsmall).le
      exact ((Real.self_le_rpow_of_one_le hlarge hp).trans hterm).trans
        ((le_max_right 0 ((r - b) / A)).trans (le_add_of_nonneg_left (by norm_num)))
  constructor
  · intro i
    have h := (abs_le.mp (hcoord i)).1
    linarith
  · intro i
    have h := (abs_le.mp (hcoord i)).2
    linarith

/-- All sublevels are compact: this is the coercivity consequence needed
for the actual finite-dimensional objectives. -/
theorem power_lower_sublevel_compact {p A b : ℝ} (hp : 1 ≤ p) (hA : 0 < A)
    {F : (ι → ℝ) → ℝ} (hF : Continuous F) (c : ι → ℝ)
    (hlower : ∀ x, b + A * lpPower p (x - c) ≤ F x) (r : ℝ) :
    IsCompact {x | F x ≤ r} :=
  isCompact_Icc.of_isClosed_subset (isClosed_le hF continuous_const)
    (power_lower_sublevel_box hp hA c hlower)

/-- A continuous objective with a positive shifted-power lower bound attains
its global minimum. Existence is proved by a nonempty compact sublevel. -/
theorem exists_min_of_power_lower {p A b : ℝ} (hp : 1 ≤ p) (hA : 0 < A)
    {F : (ι → ℝ) → ℝ} (hF : Continuous F) (c : ι → ℝ)
    (hlower : ∀ x, b + A * lpPower p (x - c) ≤ F x) :
    ∃ z, ∀ y, F z ≤ F y := by
  have hcompact := power_lower_sublevel_compact hp hA hF c hlower (F c)
  obtain ⟨z, hz, hmin⟩ := hcompact.exists_isMinOn ⟨c, (by change F c ≤ F c; exact le_rfl)⟩ hF.continuousOn
  refine ⟨z, fun y => ?_⟩
  by_cases hy : F y ≤ F c
  · exact hmin hy
  · exact hz.trans (lt_of_not_ge hy).le

lemma lpPower_pos_of_ne_zero (p : ℝ) {v : ι → ℝ} (hv : v ≠ 0) : 0 < lpPower p v := by
  classical
  have hex : ∃ i, v i ≠ 0 := not_forall.mp (fun h => hv (funext h))
  obtain ⟨i, hi⟩ := hex
  exact (Real.rpow_pos_of_pos (abs_pos.mpr hi) p).trans_le
    (Finset.single_le_sum (fun j _ => Real.rpow_nonneg (abs_nonneg (v j)) p) (Finset.mem_univ i))

/-- Positive Jensen modulus makes any genuine global minimizer unique. -/
theorem lpPowerJensen_unique_minimizer {p μ : ℝ} (hp : 0 < p) (hμ : 0 < μ)
    {F : (ι → ℝ) → ℝ} (hJ : LpPowerJensen p μ F) {z y : ι → ℝ}
    (hz : ∀ u, F z ≤ F u) (hy : ∀ u, F y ≤ F u) : y = z := by
  by_contra hne
  have hpower := lpPower_pos_of_ne_zero p (sub_ne_zero.mpr hne)
  have hpositive := mul_pos (div_pos hμ hp) hpower
  have hgrowth := lpPowerJensen_min_growth hJ hz y
  have hle := hy z
  linarith

lemma powerAtom_continuous {p : ℝ} (hp : 1 < p) (c : ι → ℝ) :
    Continuous (powerAtom p c) := by
  have hd : Differentiable ℝ (powerAtom p c) :=
    fun x => (powerAtom_hasFDerivAt hp c x).differentiableAt
  exact hd.continuous

/-- Section 3, paragraph 5: every actual finite stage objective f plus the
accumulated shifted atoms has exactly one global minimizer. All weights are
nonnegative and one retained initial atom has positive weight. The original
objective's attained minimum supplies its lower bound. The only external
input is the scalar weighted Clarkson inequality used by Lemma 2.1. -/
theorem regularizedObjective_existsUnique_minimizer {κ : Type*}
    (s : Finset κ) {p : ℝ} (hp : 2 ≤ p) (hClarkson : ScalarWeightedClarkson p)
    (f : (ι → ℝ) → ℝ) (hf : Continuous f) (hconvex : ConvexOn ℝ Set.univ f)
    (xstar : ι → ℝ) (hstar : ∀ y, f xstar ≤ f y)
    (w : κ → ℝ) (c : κ → ι → ℝ) (hw : ∀ j ∈ s, 0 ≤ w j)
    (j₀ : κ) (hj₀ : j₀ ∈ s) (hw₀ : 0 < w j₀) :
    ∃! z : ι → ℝ, ∀ y,
      f z + ∑ j ∈ s, w j * powerAtom p (c j) z ≤
      f y + ∑ j ∈ s, w j * powerAtom p (c j) y := by
  classical
  have hp0 : 0 < p := by linarith
  have hp1 : 1 < p := by linarith
  let F := fun x => f x + ∑ j ∈ s, w j * powerAtom p (c j) x
  have hF : Continuous F := hf.add
    (continuous_finset_sum _ (fun j _ => continuous_const.mul (powerAtom_continuous hp1 (c j))))
  have hlower : ∀ x, f xstar + (w j₀ * (atomScale p / p)) * lpPower p (x - c j₀) ≤ F x := by
    intro x
    have hs : w j₀ * powerAtom p (c j₀) x ≤ ∑ j ∈ s, w j * powerAtom p (c j) x :=
      Finset.single_le_sum (fun j hj => mul_nonneg (hw j hj) (powerAtom_nonneg hp0 _ _)) hj₀
    have he : w j₀ * powerAtom p (c j₀) x =
        (w j₀ * (atomScale p / p)) * lpPower p (x - c j₀) := by
      unfold powerAtom
      ring
    rw [he] at hs
    exact add_le_add (hstar x) hs
  have hA : 0 < w j₀ * (atomScale p / p) := mul_pos hw₀ (div_pos (atomScale_pos p) hp0)
  obtain ⟨z, hz⟩ := exists_min_of_power_lower (by linarith) hA hF (c j₀) hlower
  have hH : LpPowerJensen p (∑ j ∈ s, w j) (fun x => ∑ j ∈ s, w j * powerAtom p (c j) x) := by
    simpa only [mul_one] using lpPowerJensen_weighted_sum s p (fun _ => 1) w
      (fun j => powerAtom p (c j)) hw
      (fun j _ => powerAtom_jensen_of_scalar_clarkson hp0 hClarkson (c j))
  have hJ : LpPowerJensen p (∑ j ∈ s, w j) F := lpPowerJensen_add_convex hconvex hH
  have hW : 0 < ∑ j ∈ s, w j :=
    hw₀.trans_le (Finset.single_le_sum hw hj₀)
  refine ⟨z, hz, ?_⟩
  intro y hy
  exact lpPowerJensen_unique_minimizer hp0 hW hJ hz hy

end P31
