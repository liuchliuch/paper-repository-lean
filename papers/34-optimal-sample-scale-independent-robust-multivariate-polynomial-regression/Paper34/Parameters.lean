import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-! Scalar parameters and deterministic recurrence estimates from Sections 2 and 5.
These statements do not assert that the polynomial estimator obeys the recurrence. -/
namespace Paper34

noncomputable def alpha (rho : ℝ) : ℝ := (1 + 2 * rho) / 4
noncomputable def gap (rho : ℝ) : ℝ := (1 - 2 * rho) / 2
noncomputable def zeta (rho : ℝ) : ℝ := alpha rho - rho
noncomputable def beta (eps : ℝ) : ℝ := eps / 12

/-- All parameter identities and ranges in (2.1), without suppressing endpoints. -/
theorem parameter_ranges {rho eps : ℝ} (hr0 : 0 ≤ rho) (hr : rho < 1/2)
    (he0 : 0 < eps) (he : eps ≤ 1/2) :
    (1/4 ≤ alpha rho ∧ alpha rho < 1/2) ∧
    (0 < gap rho ∧ gap rho ≤ 1/2) ∧
    (zeta rho = gap rho / 2 ∧ 0 < zeta rho ∧ zeta rho ≤ 1/4) ∧
    (0 < beta eps ∧ beta eps ≤ 1/24) ∧
    gap rho = 1 - 2 * alpha rho := by
  dsimp [alpha, gap, zeta, beta]
  constructor
  · constructor <;> linarith
  constructor
  · constructor <;> linarith
  constructor
  · constructor
    · ring
    constructor <;> linarith
  constructor
  · constructor <;> linarith
  · ring

/-- The LAD margin coefficient in the proof of Proposition 4.1. -/
theorem lad_margin_coefficient (rho : ℝ) :
    (1 - alpha rho) * (1 - zeta rho) - alpha rho * (1 + zeta rho) =
      gap rho / 2 := by
  dsimp [alpha, gap, zeta]
  ring

/-- The grid's stronger oscillation constraint implies the one needed for contraction. -/
theorem grid_implies_contraction {b gamma : ℝ} (hb0 : 0 < b) (hb : b ≤ 1/24)
    (hg : gamma ≤ b / 6) : gamma ≤ b / (2 + b) := by
  have hden : 0 < 2 + b := by linarith
  apply (le_div_iff₀ hden).2
  nlinarith

/-- Absorbing the oscillation error proves the exact one-step scalar bound (5.3). -/
theorem absorb_oscillation {R E sigma gamma b : ℝ}
    (hR : 0 ≤ R) (hE : 0 ≤ E) (hs : 0 ≤ sigma)
    (hb : 0 ≤ b) (_hg0 : 0 ≤ gamma) (hg : gamma ≤ b / (2 + b))
    (h : R ≤ 2 * sigma + 2 * gamma * E + gamma * R) :
    R ≤ (2 + b) * sigma + b * E := by
  have hden : 0 < 2 + b := by linarith
  have hprod : gamma * (2 + b) ≤ b := (le_div_iff₀ hden).1 hg
  have hg1 : gamma < 1 := by nlinarith
  have hmain : (1 - gamma) * R ≤ 2 * sigma + 2 * gamma * E := by linarith
  have hcompare : 2 * sigma + 2 * gamma * E ≤
      (1 - gamma) * ((2 + b) * sigma + b * E) := by
    have hs' := mul_nonneg (sub_nonneg.mpr hprod) hs
    have hE' := mul_nonneg (sub_nonneg.mpr hprod) hE
    nlinarith
  nlinarith

/-- The exact geometric recurrence estimate (5.5), valid also at zero noise. -/
theorem recurrence_bound (E : ℕ → ℝ) {sigma b : ℝ} (hs : 0 ≤ sigma)
    (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hstep : ∀ t, E (t+1) ≤ (2+b)*sigma + b * E t) (T : ℕ) :
    E T ≤ (2+b)/(1-b)*sigma + b^T * E 0 := by
  have hden : 0 < 1-b := by linarith
  have hA : 0 ≤ (2+b)/(1-b)*sigma := by positivity
  induction T with
  | zero => simpa only [pow_zero, one_mul] using
      (le_add_of_nonneg_left hA : E 0 ≤ (2+b)/(1-b)*sigma + E 0)
  | succ t ih =>
    have hmul := mul_le_mul_of_nonneg_left ih hb0
    have hid : (2+b)*sigma + b * ((2+b)/(1-b)*sigma) =
        (2+b)/(1-b)*sigma := by field_simp; ring
    calc E (t+1) ≤ (2+b)*sigma + b * E t := hstep t
      _ ≤ (2+b)*sigma + b * ((2+b)/(1-b)*sigma + b^t * E 0) :=
        add_le_add_left hmul _
      _ = (2+b)/(1-b)*sigma + b^(t+1) * E 0 := by rw [pow_succ]; nlinarith [hid]

/-- The numerical inequality (5.6) for the paper's prescribed beta. -/
theorem noise_floor {eps : ℝ} (he0 : 0 < eps) (he : eps ≤ 1/2) :
    (2 + beta eps) / (1 - beta eps) ≤ 2 + eps/2 := by
  unfold beta
  apply (div_le_iff₀ (by linarith : 0 < 1 - eps/12)).2
  nlinarith

/-- Combining (5.5)--(5.7) gives the final scalar error guarantee. -/
theorem target_of_recurrence (E : ℕ → ℝ) {sigma eps K : ℝ}
    (hs : 0 ≤ sigma) (he0 : 0 < eps) (he : eps ≤ 1/2)
    (hinit : E 0 ≤ K * sigma)
    (hstep : ∀ t, E (t+1) ≤ (2+beta eps)*sigma + beta eps * E t)
    (T : ℕ) (hbudget : beta eps ^ T * K ≤ eps/2) :
    E T ≤ (2+eps)*sigma := by
  have hb0 : 0 ≤ beta eps := by unfold beta; positivity
  have hb1 : beta eps < 1 := by unfold beta; linarith
  have hrec := recurrence_bound E hs hb0 hb1 hstep T
  have hf := mul_le_mul_of_nonneg_right (noise_floor he0 he) hs
  have hi := mul_le_mul_of_nonneg_left hinit (pow_nonneg hb0 T)
  have ht := mul_le_mul_of_nonneg_right hbudget hs
  nlinarith

/-- A finite scale-independent budget always exists; no division by sigma occurs. -/
theorem exists_refinement_budget {eps K : ℝ} (he0 : 0 < eps) (he : eps ≤ 1/2) :
    ∃ T : ℕ, beta eps ^ T * K ≤ eps/2 := by
  have hb0 : 0 ≤ beta eps := by unfold beta; positivity
  have hb1 : beta eps < 1 := by unfold beta; linarith
  have hlim : Filter.Tendsto (fun T : ℕ => beta eps ^ T * K)
      Filter.atTop (nhds (0 * K)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hb0 hb1).mul_const K
  have hev := (tendsto_order.1 hlim).2 (eps/2) (by simpa using half_pos he0)
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 hev
  exact ⟨T, (hT T le_rfl).le⟩

/-- The source initializer constant in (4.3), depending only on n,d,rho. -/
noncomputable def initializationFactor (n d : ℕ) (rho : ℝ) : ℝ :=
  4*(2*(d : ℝ)+1)^n/gap rho

/-- The predetermined least integer in (2.7); neither p nor sigma is an input. -/
noncomputable def refinementBudget (n d : ℕ) (rho eps : ℝ)
    (he0 : 0 < eps) (he : eps ≤ 1/2) : ℕ :=
  Nat.find (exists_refinement_budget (K := initializationFactor n d rho) he0 he)

theorem refinementBudget_spec (n d : ℕ) (rho eps : ℝ)
    (he0 : 0 < eps) (he : eps ≤ 1/2) :
    beta eps ^ refinementBudget n d rho eps he0 he * initializationFactor n d rho ≤ eps/2 :=
  Nat.find_spec (exists_refinement_budget (K := initializationFactor n d rho) he0 he)

theorem refinementBudget_minimal (n d : ℕ) (rho eps : ℝ)
    (he0 : 0 < eps) (he : eps ≤ 1/2) (t : ℕ)
    (ht : beta eps ^ t * initializationFactor n d rho ≤ eps/2) :
    refinementBudget n d rho eps he0 he ≤ t :=
  Nat.find_min' (exists_refinement_budget (K := initializationFactor n d rho) he0 he) ht

end Paper34
