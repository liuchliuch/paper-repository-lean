import Paper37.RenewalModel
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Boundary calculations for stationary renewal prediction

The definitions below use extended nonnegative reals for KL, so a positive
Bernoulli mass against a zero prediction has infinite loss. In particular none
of the endpoint radius calculations uses `Real.log 0` as a finite loss.
-/

noncomputable section
open scoped ENNReal
open MeasureTheory

namespace Paper37.Boundary

/-- The finite formula for binary relative entropy. -/
def klReal (p q : ℝ) : ℝ :=
  p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))

/-- Binary KL with the usual extended-value support convention. Arguments used
as probability parameters are always restricted to `[0,1]`. -/
def kl (p q : ℝ) : ℝ≥0∞ :=
  if (q = 0 ∧ p ≠ 0) ∨ (q = 1 ∧ p ≠ 1) then ∞
  else ENNReal.ofReal (klReal p q)

@[simp] theorem kl_self (p : ℝ) : kl p p = 0 := by
  simp [kl, klReal]

@[simp] theorem kl_zero_one : kl 0 1 = ∞ := by simp [kl]
@[simp] theorem kl_one_zero : kl 1 0 = ∞ := by simp [kl]

 theorem kl_zero (q : ℝ) (hq : q ≠ 1) :
    kl 0 q = ENNReal.ofReal (-Real.log (1 - q)) := by
  simp [kl, klReal, hq, Real.log_inv, one_div]

 theorem kl_one (q : ℝ) (hq : q ≠ 0) :
    kl 1 q = ENNReal.ofReal (-Real.log q) := by
  simp [kl, klReal, hq, Real.log_inv, one_div]

/-- Entropy decomposition, including target endpoints. -/
theorem klReal_eq_crossEntropy {p q : ℝ} (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    klReal p q = -Real.binEntropy p - p * Real.log q -
      (1 - p) * Real.log (1 - q) := by
  by_cases hp0 : p = 0
  · subst p
    simp [klReal, Real.log_inv, one_div]
  by_cases hp1 : p = 1
  · subst p
    simp [klReal, Real.log_inv, one_div]
  have hq1' : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq1)
  have hp1' : 1 - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1)
  rw [klReal, Real.log_div hp0 hq0, Real.log_div hp1' hq1', Real.binEntropy]
  simp only [Real.log_inv]
  ring

/-- The fair coin has binary KL loss at most log 2. -/
theorem kl_half_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    kl p (1 / 2) ≤ ENNReal.ofReal (Real.log 2) := by
  have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    simpa using (Real.log_inv (2 : ℝ))
  have hreal : klReal p (1 / 2) = Real.log 2 - Real.binEntropy p := by
    rw [klReal_eq_crossEntropy (by norm_num) (by norm_num)]
    norm_num only [show (1:ℝ) - 1 / 2 = 1 / 2 by norm_num]
    rw [hhalf]
    ring
  unfold kl
  split_ifs with h
  · rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> norm_num at h
  · rw [hreal]
    apply ENNReal.ofReal_le_ofReal
    linarith [Real.binEntropy_nonneg hp0 hp1]

/-- The two endpoint losses have average at least log 2. -/
theorem endpoint_loss_sum_ge {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ENNReal.ofReal (2 * Real.log 2) ≤ kl 0 q + kl 1 q := by
  by_cases h0 : q = 0
  · subst q; simp
  by_cases h1 : q = 1
  · subst q; simp
  have hqpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm h0)
  have hqsubpos : 0 < 1 - q := sub_pos.mpr (lt_of_le_of_ne hq1 h1)
  have hprod : q * (1 - q) ≤ (1 / 2 : ℝ) * (1 / 2) := by
    nlinarith [sq_nonneg (q - 1 / 2)]
  have hlog := Real.log_le_log (mul_pos hqpos hqsubpos) hprod
  rw [Real.log_mul h0 (ne_of_gt hqsubpos), Real.log_mul (by norm_num) (by norm_num)] at hlog
  have hh : Real.log (1 / 2 : ℝ) = -Real.log 2 := by simp [one_div]
  rw [hh] at hlog
  rw [kl_zero q h1, kl_one q h0]
  calc
    ENNReal.ofReal (2 * Real.log 2) ≤
        ENNReal.ofReal (-Real.log (1 - q) + -Real.log q) :=
      ENNReal.ofReal_le_ofReal (by linarith)
    _ ≤ _ := ENNReal.ofReal_add_le

/-- Deterministic radius of the two Bernoulli endpoint targets. -/
theorem endpoint_radius {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ENNReal.ofReal (Real.log 2) ≤ max (kl 0 q) (kl 1 q) := by
  by_contra h
  have ha : kl 0 q < ENNReal.ofReal (Real.log 2) := (lt_of_not_ge h).trans_le' (le_max_left _ _)
  have hb : kl 1 q < ENNReal.ofReal (Real.log 2) := (lt_of_not_ge h).trans_le' (le_max_right _ _)
  have hadd : kl 0 q + kl 1 q < ENNReal.ofReal (Real.log 2) + ENNReal.ofReal (Real.log 2) :=
    ENNReal.add_lt_add ha hb
  have hlog0 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  rw [← ENNReal.ofReal_add hlog0 hlog0] at hadd
  have := endpoint_loss_sum_ge hq0 hq1
  have heq : Real.log 2 + Real.log 2 = 2 * Real.log 2 := by ring
  rw [heq] at hadd
  exact (not_lt_of_ge this) hadd

/-- Exact minimax radius of two Bernoulli endpoint targets. -/
theorem endpoint_minimax :
    (⨅ q : Set.Icc (0 : ℝ) 1, max (kl 0 q) (kl 1 q)) =
      ENNReal.ofReal (Real.log 2) := by
  apply le_antisymm
  · refine iInf_le_of_le ⟨1 / 2, by norm_num⟩ ?_
    exact max_le (kl_half_le (by norm_num) (by norm_num))
      (kl_half_le (by norm_num) (by norm_num))
  · exact le_iInf fun q => endpoint_radius q.property.1 q.property.2

@[simp] theorem kl_right_zero {p : ℝ} (hp : p ≠ 0) : kl p 0 = ∞ := by
  simp [kl, hp]

@[simp] theorem kl_right_one {p : ℝ} (hp : p ≠ 1) : kl p 1 = ∞ := by
  simp [kl, hp]

 theorem measurable_kl_zero : Measurable (kl 0) := by
  have heq : kl 0 = fun q : ℝ => if q = 1 then ∞ else ENNReal.ofReal (-Real.log (1 - q)) := by
    funext q
    by_cases h : q = 1
    · subst q; simp
    · simp [kl_zero q h, h]
  rw [heq]
  exact measurable_const.ite (measurableSet_singleton 1)
    ((measurable_const.sub measurable_id).log.neg.ennreal_ofReal)

/-- Lower bound for arbitrary private randomization on an arbitrary probability
space. No integrability assumption is imposed; the losses may be infinite. -/
theorem randomized_endpoint_radius {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (q : Ω → ℝ)
    (hq : Measurable q) (hq01 : ∀ ω, q ω ∈ Set.Icc (0 : ℝ) 1) :
    ENNReal.ofReal (Real.log 2) ≤
      max (∫⁻ ω, kl 0 (q ω) ∂μ) (∫⁻ ω, kl 1 (q ω) ∂μ) := by
  have hsum : ENNReal.ofReal (2 * Real.log 2) ≤
      (∫⁻ ω, kl 0 (q ω) ∂μ) + (∫⁻ ω, kl 1 (q ω) ∂μ) := by
    rw [← lintegral_add_left (show Measurable (fun ω => kl 0 (q ω)) from measurable_kl_zero.comp hq) (fun ω => kl 1 (q ω))]
    calc
      ENNReal.ofReal (2 * Real.log 2) = ∫⁻ _ : Ω, ENNReal.ofReal (2 * Real.log 2) ∂μ := by simp
      _ ≤ _ := lintegral_mono fun ω => endpoint_loss_sum_ge (hq01 ω).1 (hq01 ω).2
  by_contra h
  have ha := (le_max_left (∫⁻ ω, kl 0 (q ω) ∂μ) (∫⁻ ω, kl 1 (q ω) ∂μ)).trans_lt (lt_of_not_ge h)
  have hb := (le_max_right (∫⁻ ω, kl 0 (q ω) ∂μ) (∫⁻ ω, kl 1 (q ω) ∂μ)).trans_lt (lt_of_not_ge h)
  have hadd := ENNReal.add_lt_add ha hb
  have hlog0 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  rw [← ENNReal.ofReal_add hlog0 hlog0, show Real.log 2 + Real.log 2 = 2 * Real.log 2 by ring] at hadd
  exact (not_lt_of_ge hsum) hadd

section FiniteEquilibrium

variable {ι : Type*} [Fintype ι]

/-- Mean gap for a finite gap distribution (possibly with repeated lengths). -/
def finiteMean (length : ι → ℕ) (weight : ι → ℝ) : ℝ :=
  ∑ i, (length i : ℝ) * weight i

/-- Equilibrium cycle and phase mass: each of the `length i` possible initial
waits in cycle type `i` has weight `weight i / finiteMean length weight`. -/
def phaseWeight (length : ι → ℕ) (weight : ι → ℝ)
    (s : (i : ι) × Fin (length i)) : ℝ := weight s.1 / finiteMean length weight

/-- These are normalized probability weights, rather than an assumed formula. -/
theorem phaseWeight_sum (length : ι → ℕ) (weight : ι → ℝ)
    (hm : finiteMean length weight ≠ 0) :
    ∑ s : (i : ι) × Fin (length i), phaseWeight length weight s = 1 := by
  classical
  simp only [phaseWeight, Fintype.sum_sigma, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div]
  simpa [finiteMean] using div_self hm

 theorem phaseWeight_nonneg (length : ι → ℕ) (weight : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hm : 0 < finiteMean length weight)
    (s : (i : ι) × Fin (length i)) : 0 ≤ phaseWeight length weight s :=
  div_nonneg (hw s.1) hm.le

private theorem sum_fin_ge (d n : ℕ) (c : ℝ) :
    (∑ j : Fin d, if n ≤ j.val then c else 0) = ((d - n : ℕ) : ℝ) * c := by
  induction d generalizing n with
  | zero => simp
  | succ d ih =>
    cases n with
    | zero => simp
    | succ n => simpa [Fin.sum_univ_succ, Nat.succ_le_succ_iff] using ih n

private theorem sum_fin_eq (d n : ℕ) (c : ℝ) :
    (∑ j : Fin d, if j.val = n then c else 0) = if n < d then c else 0 := by
  induction d generalizing n with
  | zero => simp
  | succ d ih =>
    cases n with
    | zero => simp [Fin.sum_univ_succ]
    | succ n => simpa [Fin.sum_univ_succ] using ih n

/-- Probability of an all-zero history of length `n` in the finite equilibrium
phase construction: the first renewal is at phase value plus one. -/
def zeroHistoryMass (length : ι → ℕ) (weight : ι → ℝ) (n : ℕ) : ℝ :=
  ∑ s : (i : ι) × Fin (length i), if n ≤ s.2.val then phaseWeight length weight s else 0

/-- Joint mass of the all-zero history and renewal at the following time. -/
def nextRenewalMass (length : ι → ℕ) (weight : ι → ℝ) (n : ℕ) : ℝ :=
  ∑ s : (i : ι) × Fin (length i), if s.2.val = n then phaseWeight length weight s else 0

 theorem zeroHistoryMass_eq (length : ι → ℕ) (weight : ι → ℝ) (n : ℕ) :
    zeroHistoryMass length weight n =
      (∑ i, ((length i - n : ℕ) : ℝ) * weight i) / finiteMean length weight := by
  classical
  unfold zeroHistoryMass
  rw [Fintype.sum_sigma]
  simp only [phaseWeight, sum_fin_ge]
  simp only [← mul_div_assoc, ← Finset.sum_div]

 theorem nextRenewalMass_eq (length : ι → ℕ) (weight : ι → ℝ) (n : ℕ) :
    nextRenewalMass length weight n =
      (∑ i, if n < length i then weight i else 0) / finiteMean length weight := by
  classical
  unfold nextRenewalMass
  rw [Fintype.sum_sigma]
  simp only [phaseWeight, sum_fin_eq]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> simp

/-- Equilibrium residual conditional (2.3) proved as a ratio of actual event
masses in a normalized finite probability space. -/
theorem zeroHistory_conditional (length : ι → ℕ) (weight : ι → ℝ) (n : ℕ)
    (hm : finiteMean length weight ≠ 0) :
    nextRenewalMass length weight n / zeroHistoryMass length weight n =
      (∑ i, if n < length i then weight i else 0) /
      (∑ i, ((length i - n : ℕ) : ℝ) * weight i) := by
  rw [nextRenewalMass_eq, zeroHistoryMass_eq, div_div_div_cancel_right₀ hm]

end FiniteEquilibrium

/-- Finite ordinary post-renewal hazard. -/
def finiteHazard {ι : Type*} [Fintype ι] (length : ι → ℕ)
    (weight : ι → ℝ) (n : ℕ) : ℝ :=
  (∑ i, if length i = n + 1 then weight i else 0) /
    (∑ i, if n < length i then weight i else 0)

/-- The two genuine finite gap distributions used in Appendix A, represented
by a Bernoulli choice between lengths `n+1` and `M`. -/
def twoLength (n M : ℕ) : Bool → ℕ
  | false => n + 1
  | true => M

def twoWeight (δ : ℝ) : Bool → ℝ
  | false => 1 - δ
  | true => δ

 theorem twoWeight_nonneg {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    ∀ b, 0 ≤ twoWeight δ b := by
  intro b; cases b <;> simp [twoWeight] <;> linarith

 theorem twoWeight_sum (δ : ℝ) : ∑ b, twoWeight δ b = 1 := by
  simp [twoWeight, Fintype.sum_bool]

 theorem twoMean (n M : ℕ) (δ : ℝ) :
    finiteMean (twoLength n M) (twoWeight δ) =
      (1 - δ) * ((n : ℝ) + 1) + δ * M := by
  simp [finiteMean, twoLength, twoWeight, Fintype.sum_bool, Nat.cast_add,
    Nat.cast_one]
  ring

 theorem twoMean_pos {n M : ℕ} {δ : ℝ} (hM : n + 1 < M) (hδ : 0 ≤ δ) :
    0 < finiteMean (twoLength n M) (twoWeight δ) := by
  rw [twoMean]
  have hMreal : (n : ℝ) + 1 < M := by exact_mod_cast hM
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hprod : 0 ≤ δ * ((M : ℝ) - (n + 1)) := mul_nonneg hδ (by linarith)
  nlinarith

/-- Exact equilibrium all-zero probability (A.1) for the two-point mixture. -/
theorem two_zeroHistoryMass {n M : ℕ} (δ : ℝ) (hM : n + 1 < M) :
    zeroHistoryMass (twoLength n M) (twoWeight δ) n =
      ((1 - δ) + δ * ((M : ℝ) - n)) /
        ((1 - δ) * ((n : ℝ) + 1) + δ * M) := by
  rw [zeroHistoryMass_eq, twoMean]
  have hle : n ≤ M := by omega
  simp only [Fintype.sum_bool, twoLength, twoWeight,
    Nat.add_sub_cancel_left, Nat.cast_one, Nat.cast_sub hle]
  ring

/-- The substituted ordinary hazard on the common all-zero history. -/
theorem two_hazard {n M : ℕ} (δ : ℝ) (hM : n + 1 < M) :
    finiteHazard (twoLength n M) (twoWeight δ) n = 1 - δ := by
  have hne : M ≠ n + 1 := by omega
  have hlt : n < M := by omega
  simp [finiteHazard, Fintype.sum_bool, twoLength, twoWeight, hne, hlt]

/-- Genuine equilibrium conditional on the same history. -/
theorem two_conditional {n M : ℕ} {δ : ℝ} (hM : n + 1 < M) (hδ : 0 ≤ δ) :
    nextRenewalMass (twoLength n M) (twoWeight δ) n /
      zeroHistoryMass (twoLength n M) (twoWeight δ) n =
        1 / ((1 - δ) + δ * ((M : ℝ) - n)) := by
  rw [zeroHistory_conditional _ _ _ (ne_of_gt (twoMean_pos hM hδ))]
  have hle : n ≤ M := by omega
  have hlt : n < M := by omega
  simp only [Fintype.sum_bool, twoLength, twoWeight,
    Nat.add_sub_cancel_left, Nat.cast_one, Nat.cast_sub hle, hlt,
    Nat.lt_succ_self, if_true]
  ring

/-- A deterministic period as a one-point genuine gap law. -/
def periodLength (d : ℕ) : Unit → ℕ := fun _ => d

def periodWeight : Unit → ℝ := fun _ => 1

 theorem period_phase_sum {d : ℕ} (hd : 0 < d) :
    ∑ s : (i : Unit) × Fin (periodLength d i), phaseWeight (periodLength d) periodWeight s = 1 := by
  apply phaseWeight_sum
  simp [finiteMean, periodLength, periodWeight, Nat.ne_of_gt hd]

 theorem period_zeroHistoryMass (d n : ℕ) :
    zeroHistoryMass (periodLength d) periodWeight n = ((d - n : ℕ) : ℝ) / d := by
  simp [zeroHistoryMass_eq, finiteMean, periodLength, periodWeight]

 theorem period_conditional {d n : ℕ} (hd : n < d) :
    nextRenewalMass (periodLength d) periodWeight n /
      zeroHistoryMass (periodLength d) periodWeight n = 1 / ((d - n : ℕ) : ℝ) := by
  rw [zeroHistory_conditional]
  · simp [periodLength, periodWeight, hd]
  · simp [finiteMean, periodLength, periodWeight, Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le n) hd)]

/-- Exact two deterministic-period boundary probabilities and conditionals in
Proposition E.6; no asymptotic estimate or lower bound is assumed. -/
theorem deterministic_period_comparison {n : ℕ} (hn : 0 < n) :
    zeroHistoryMass (periodLength (n + 1)) periodWeight n = 1 / ((n : ℝ) + 1) ∧
    nextRenewalMass (periodLength (n + 1)) periodWeight n /
      zeroHistoryMass (periodLength (n + 1)) periodWeight n = 1 ∧
    zeroHistoryMass (periodLength (2 * n)) periodWeight n = 1 / 2 ∧
    nextRenewalMass (periodLength (2 * n)) periodWeight n /
      zeroHistoryMass (periodLength (2 * n)) periodWeight n = 1 / (n : ℝ) := by
  have h2n : n < 2 * n := by omega
  have heq : 2 * n - n = n := by omega
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [period_zeroHistoryMass]
  · simp [period_conditional (Nat.lt_succ_self n)]
  · rw [period_zeroHistoryMass, heq]
    push_cast
    field_simp
  · simpa [heq] using period_conditional h2n

/-- Jensen-Shannon objective identity used by the two-model lower bound in
Appendix A. Its remainder is an actual binary KL finite formula. -/
theorem two_target_average_identity {p q : ℝ} (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    (klReal 0 q + klReal p q) / 2 =
      Real.binEntropy (p / 2) - Real.binEntropy p / 2 + klReal (p / 2) q := by
  rw [klReal_eq_crossEntropy hq0 hq1, klReal_eq_crossEntropy hq0 hq1,
    klReal_eq_crossEntropy hq0 hq1]
  simp only [Real.binEntropy_zero]
  ring

/-- A genuine deterministic-period law, with gap `a+1` in the model used by
all other modules. Its mean is finite by a singleton summation proof. -/
def pointLaw (a : ℕ) : Paper37.Renewal.Law where
  mass d := if d = a then 1 else 0
  nonneg d := by split_ifs <;> norm_num
  total := by simpa using hasSum_ite_eq a (1 : ℝ)
  finiteMean := by
    have heq : (fun d : ℕ => ((d : ℝ) + 1) * (if d = a then 1 else 0)) =
        (fun d : ℕ => if d = a then ((a : ℝ) + 1) else 0) := by
      funext d
      split_ifs with h
      · subst d; simp
      · simp
    rw [heq]
    exact (hasSum_ite_eq a ((a : ℝ) + 1)).summable

@[simp] theorem pointLaw_mean (a : ℕ) : Paper37.Renewal.mean (pointLaw a) = (a : ℝ) + 1 := by
  simp only [Paper37.Renewal.mean, pointLaw, mul_ite, mul_one, mul_zero]
  have heq : (fun d : ℕ => if d = a then (d : ℝ) + 1 else 0) =
      (fun d : ℕ => if d = a then (a : ℝ) + 1 else 0) := by
    funext d; split_ifs with h
    · subst d; rfl
    · rfl
  rw [heq]
  exact tsum_ite_eq a _

@[simp] theorem pointLaw_tail (a n : ℕ) :
    Paper37.Renewal.tail (pointLaw a) n = if n ≤ a then 1 else 0 := by
  unfold Paper37.Renewal.tail
  have heq : (fun d : ℕ => if n ≤ d then (pointLaw a).mass d else 0) =
      (fun d : ℕ => if d = a then (if n ≤ a then 1 else 0) else 0) := by
    funext d
    by_cases h : d = a
    · subst d; simp [pointLaw]
    · simp [pointLaw, h]
  rw [heq]
  simp

@[simp] theorem pointLaw_residual (a n : ℕ) :
    Paper37.Renewal.residual (pointLaw a) n = ((a + 1 - n : ℕ) : ℝ) := by
  simp only [Paper37.Renewal.residual, pointLaw, mul_ite, mul_one, mul_zero]
  have heq : (fun d : ℕ => if d = a then ((d + 1 - n : ℕ) : ℝ) else 0) =
      (fun d : ℕ => if d = a then ((a + 1 - n : ℕ) : ℝ) else 0) := by
    funext d; split_ifs with h
    · subst d; rfl
    · rfl
  rw [heq]
  exact tsum_ite_eq a _

/-- The concrete all-zero history under period `n+k+1` is positive, and its
true stationary conditional is `1/(k+1)`. -/
theorem pointLaw_zero_history (n k : ℕ) :
    0 < Paper37.Renewal.blockMass (pointLaw (n + k)) (List.replicate n false) ∧
    Paper37.Renewal.conditional (pointLaw (n + k)) (List.replicate n false) =
      1 / ((k : ℝ) + 1) := by
  rw [Paper37.Renewal.blockMass_zeros, Paper37.Renewal.conditional_zeros]
  have hsub : n + k + 1 - n = k + 1 := by omega
  simp only [pointLaw_mean, pointLaw_residual, pointLaw_tail, hsub,
    show n ≤ n + k by omega, if_true, Nat.cast_add, Nat.cast_one]
  constructor
  · positivity
  · trivial

 theorem continuous_kl_left {q : ℝ} (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    Continuous (fun p : ℝ => kl p q) := by
  have h : Continuous (fun p : ℝ => -Real.binEntropy p - p * Real.log q -
      (1 - p) * Real.log (1 - q)) :=
    (Real.binEntropy_continuous.neg.sub (continuous_id.mul continuous_const)).sub
      ((continuous_const.sub continuous_id).mul continuous_const)
  convert ENNReal.continuous_ofReal.comp h using 1
  funext p
  simp [kl, hq0, hq1, klReal_eq_crossEntropy hq0 hq1]

/-- Even the countable family of deterministic periods has binary radius
log 2 when all-zero histories are judged separately. -/
theorem period_history_radius {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ENNReal.ofReal (Real.log 2) ≤ ⨆ k : ℕ, kl (1 / ((k : ℝ) + 1)) q := by
  by_cases h0 : q = 0
  · subst q
    exact le_trans (by simp : ENNReal.ofReal (Real.log 2) ≤ kl 1 0)
      (by simpa using (le_iSup (fun k : ℕ => kl (1 / ((k : ℝ) + 1)) 0) 0))
  by_cases h1 : q = 1
  · subst q
    have h : kl (1 / ((1 : ℕ) + 1 : ℝ)) 1 = ∞ := by norm_num [kl]
    have hi := le_iSup (fun k : ℕ => kl (1 / ((k : ℝ) + 1)) 1) 1
    norm_num only [Nat.cast_one] at hi
    norm_num only [Nat.cast_one, one_add_one_eq_two] at h
    rw [h] at hi
    exact le_trans le_top hi
  have hlim : Filter.Tendsto (fun k : ℕ => kl (1 / ((k : ℝ) + 1)) q)
      Filter.atTop (nhds (kl 0 q)) :=
    (continuous_kl_left h0 h1).continuousAt.tendsto.comp tendsto_one_div_add_atTop_nhds_zero_nat
  have hz : kl 0 q ≤ ⨆ k : ℕ, kl (1 / ((k : ℝ) + 1)) q :=
    le_of_tendsto' hlim fun k => le_iSup (fun k : ℕ => kl (1 / ((k : ℝ) + 1)) q) k
  have ho : kl 1 q ≤ ⨆ k : ℕ, kl (1 / ((k : ℝ) + 1)) q := by
    simpa using (le_iSup (fun k : ℕ => kl (1 / ((k : ℝ) + 1)) q) 0)
  exact (endpoint_radius hq0 hq1).trans (max_le hz ho)

/-- Genuine source historywise risk, with every positive-probability history
and every finite-mean law included in the supremum. -/
def historywiseRisk (n : ℕ) (q : List Bool → ℝ) : ℝ≥0∞ :=
  ⨆ μ : Paper37.Renewal.Law,
    ⨆ x : {x : List Bool // x.length = n ∧ 0 < Paper37.Renewal.blockMass μ x},
      kl (Paper37.Renewal.conditional μ x.val) (q x.val)

/-- Full deterministic-predictor form of Proposition A.2. -/
theorem historywise_minimax (n : ℕ) :
    (⨅ q : {q : List Bool → ℝ // ∀ x, q x ∈ Set.Icc (0 : ℝ) 1},
      historywiseRisk n q.val) = ENNReal.ofReal (Real.log 2) := by
  apply le_antisymm
  · refine iInf_le_of_le ⟨fun _ => 1 / 2, fun _ => by norm_num⟩ ?_
    apply iSup_le
    intro μ
    apply iSup_le
    intro x
    exact kl_half_le (Paper37.Renewal.conditional_mem_unitInterval μ x.val).1
      (Paper37.Renewal.conditional_mem_unitInterval μ x.val).2
  · apply le_iInf
    intro q
    refine (period_history_radius (q.property (List.replicate n false)).1
      (q.property (List.replicate n false)).2).trans ?_
    apply iSup_le
    intro k
    have h := pointLaw_zero_history n k
    rw [← h.2]
    unfold historywiseRisk
    exact le_iSup_of_le (pointLaw (n + k))
      (le_iSup (fun x : {x : List Bool // x.length = n ∧
        0 < Paper37.Renewal.blockMass (pointLaw (n + k)) x} =>
          kl (Paper37.Renewal.conditional (pointLaw (n + k)) x.val) (q.val x.val))
        ⟨List.replicate n false, by simp, h.1⟩)

/-- Measurability of extended binary KL in the predicted parameter. -/
theorem measurable_kl_right (p : ℝ) : Measurable (kl p) := by
  have h0 : MeasurableSet {q : ℝ | q = 0 ∧ p ≠ 0} := by
    by_cases hp : p = 0
    · simp [hp]
    · simpa [hp] using (measurableSet_singleton (0 : ℝ))
  have h1 : MeasurableSet {q : ℝ | q = 1 ∧ p ≠ 1} := by
    by_cases hp : p = 1
    · simp [hp]
    · simpa [hp] using (measurableSet_singleton (1 : ℝ))
  have hr : Measurable (klReal p) :=
    (measurable_const.mul (measurable_const.div measurable_id).log).add
      (measurable_const.mul (measurable_const.div (measurable_const.sub measurable_id)).log)
  exact measurable_const.ite (h0.union h1) hr.ennreal_ofReal

/-- Endpoint lower semicontinuity along the deterministic-period target
sequence. At an impossible prediction the limit loss is treated in ENNReal. -/
theorem kl_zero_le_liminf_period (q : ℝ) :
    kl 0 q ≤ Filter.liminf (fun k : ℕ => kl (1 / ((k : ℝ) + 1)) q) Filter.atTop := by
  by_cases h0 : q = 0
  · subst q; simp
  by_cases h1 : q = 1
  · subst q
    have hevent : ∀ᶠ k : ℕ in Filter.atTop, kl (1 / ((k : ℝ) + 1)) 1 = ∞ := by
      filter_upwards [Filter.eventually_ge_atTop 1] with k hk
      apply kl_right_one
      have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
      have hlt : 1 / ((k : ℝ) + 1) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
      exact ne_of_lt hlt
    have hlim : Filter.Tendsto (fun k : ℕ => kl (1 / ((k : ℝ) + 1)) 1)
        Filter.atTop (nhds ∞) := tendsto_const_nhds.congr' (hevent.mono fun _ h => h.symm)
    rw [hlim.liminf_eq]
    exact le_top
  have hlim : Filter.Tendsto (fun k : ℕ => kl (1 / ((k : ℝ) + 1)) q)
      Filter.atTop (nhds (kl 0 q)) :=
    (continuous_kl_left h0 h1).continuousAt.tendsto.comp tendsto_one_div_add_atTop_nhds_zero_nat
  rw [hlim.liminf_eq]

/-- Arbitrary randomized predictors cannot improve the period-history radius.
This is Fatou's lemma over the private random seed and the actual countable
family of finite deterministic-period models. -/
theorem randomized_period_history_radius {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (q : Ω → ℝ)
    (hq : Measurable q) (hq01 : ∀ ω, q ω ∈ Set.Icc (0 : ℝ) 1) :
    ENNReal.ofReal (Real.log 2) ≤
      ⨆ k : ℕ, ∫⁻ ω, kl (1 / ((k : ℝ) + 1)) (q ω) ∂μ := by
  have hz : (∫⁻ ω, kl 0 (q ω) ∂μ) ≤
      ⨆ k : ℕ, ∫⁻ ω, kl (1 / ((k : ℝ) + 1)) (q ω) ∂μ := by
    calc
      (∫⁻ ω, kl 0 (q ω) ∂μ) ≤
          ∫⁻ ω, Filter.liminf (fun k : ℕ => kl (1 / ((k : ℝ) + 1)) (q ω)) Filter.atTop ∂μ :=
        lintegral_mono fun ω => kl_zero_le_liminf_period (q ω)
      _ ≤ Filter.liminf (fun k : ℕ => ∫⁻ ω, kl (1 / ((k : ℝ) + 1)) (q ω) ∂μ) Filter.atTop :=
        lintegral_liminf_le fun k => (measurable_kl_right (1 / ((k : ℝ) + 1))).comp hq
      _ ≤ _ := by
        rw [Filter.liminf_eq_iSup_iInf_of_nat]
        apply iSup_le
        intro n
        exact (iInf₂_le n le_rfl).trans (le_iSup
          (fun k : ℕ => ∫⁻ ω, kl (1 / ((k : ℝ) + 1)) (q ω) ∂μ) n)
  have ho : (∫⁻ ω, kl 1 (q ω) ∂μ) ≤
      ⨆ k : ℕ, ∫⁻ ω, kl (1 / ((k : ℝ) + 1)) (q ω) ∂μ := by
    simpa using (le_iSup (fun k : ℕ => ∫⁻ ω, kl (1 / ((k : ℝ) + 1)) (q ω) ∂μ) 0)
  exact (randomized_endpoint_radius μ q hq hq01).trans (max_le hz ho)

end Paper37.Boundary
