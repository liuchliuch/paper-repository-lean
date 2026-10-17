import PsgEst.Probability
import PsgEst.Estimator
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Concentration specializations used in Section 3

The external probability inequalities are explicit propositions, never axioms.
`PaulinBernsteinInput` is the original stationary Bernstein inequality with
positive upper bounds for its variance and centered range. `FreedmanJointInput`
is the joint-event, two-sided matrix Freedman conclusion, parametrized by the
norms of the martingale sum and predictable variation. All subsequent
specializations, finite union bounds and numerical constants are proved here.
The martingale construction and verification of the hypotheses of Freedman's
external theorem are separate obligations, not implicit in these definitions.
-/

open Matrix BigOperators Real Finset
namespace PsgEst

/-- A finite path event, represented by its truth predicate. -/
noncomputable def eventProb {d m : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ)
    (mu : Fin d → ℝ) (E : (Fin (m+1) → Fin d) → Prop) : ℝ := by
  classical
  exact pathMeasure Q mu (univ.filter E)

lemma eventProb_mono {d m : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ)
    (mu : Fin d → ℝ) (hQ : ∀ i j, 0 ≤ Q i j) (hmu : ∀ i, 0 ≤ mu i)
    {E F : (Fin (m+1) → Fin d) → Prop} (h : ∀ Y, E Y → F Y) :
    eventProb Q mu E ≤ eventProb Q mu F := by
  classical
  unfold eventProb pathMeasure
  exact sum_le_sum_of_subset_of_nonneg
    (by intro Y hY; simp only [mem_filter, mem_univ, true_and] at *; exact h Y hY)
    (by intro Y _ _; exact pathProb_nonneg Q mu hQ hmu Y)

/-- Finite union bound, allowing overlapping events. -/
theorem eventProb_exists_le {d m : ℕ} {ι : Type*} [Fintype ι]
    (Q : Matrix (Fin d) (Fin d) ℝ) (mu : Fin d → ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hmu : ∀ i, 0 ≤ mu i)
    (E : ι → (Fin (m+1) → Fin d) → Prop) :
    eventProb Q mu (fun Y => ∃ i, E i Y) ≤ ∑ i, eventProb Q mu (E i) := by
  classical
  unfold eventProb pathMeasure
  simp only [sum_filter]
  rw [sum_comm]
  apply sum_le_sum
  intro Y _
  by_cases h : ∃ i, E i Y
  · obtain ⟨i, hi⟩ := h
    rw [if_pos ⟨i, hi⟩]
    have hsingle := single_le_sum (f := fun j => if E j Y then pathProb Q mu Y else 0)
      (fun j _ => by dsimp only; split_ifs; exact pathProb_nonneg Q mu hQ hmu Y; exact le_rfl)
      (mem_univ i)
    simpa only [if_pos hi] using hsingle
  · rw [if_neg h]
    exact sum_nonneg (fun i _ => by split_ifs; exact pathProb_nonneg Q mu hQ hmu Y; exact le_rfl)

/-- Union bound for two arbitrary path events. -/
theorem eventProb_or_le {d m : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ)
    (mu : Fin d → ℝ) (hQ : ∀ i j, 0 ≤ Q i j) (hmu : ∀ i, 0 ≤ mu i)
    (E F : (Fin (m+1) → Fin d) → Prop) :
    eventProb Q mu (fun Y => E Y ∨ F Y) ≤ eventProb Q mu E + eventProb Q mu F := by
  classical
  have h := eventProb_exists_le Q mu hQ hmu (fun b : Bool => if b then E else F)
  have heq : (fun Y => ∃ b : Bool, (if b then E else F) Y) = (fun Y => E Y ∨ F Y) := by
    funext Y
    simp only [Bool.exists_bool, Bool.false_eq_true, ↓reduceIte]
    exact propext or_comm
  rw [heq] at h
  simpa only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte] using h

/-- Observing the departure or the arrival of each transition. -/
def observationIndex {m : ℕ} (arrival : Bool) (t : Fin m) : Fin (m+1) :=
  if arrival then t.succ else t.castSucc

noncomputable def stateSum {d m : ℕ} (f : Fin d → ℝ)
    (arrival : Bool) (Y : Fin (m+1) → Fin d) : ℝ :=
  ∑ t : Fin m, f (Y (observationIndex arrival t))

noncomputable def stationaryMean {d : ℕ} (pi : Fin d → ℝ) (f : Fin d → ℝ) : ℝ :=
  ∑ i, pi i * f i

noncomputable def stationaryVariance {d : ℕ} (pi : Fin d → ℝ) (f : Fin d → ℝ) : ℝ :=
  ∑ i, pi i * (f i - stationaryMean pi f)^2

/-- Paulin [4], Thm 3.11, corrected (3.25), in its variance/range upper-bound
form. Both observation offsets are allowed by stationarity. No instance of
this proposition is postulated in this development. -/
def PaulinBernsteinInput {d : ℕ} (Q : Stoch d) (st : Stationary Q) (Γ : ℝ) : Prop :=
  ∀ (m : ℕ) (f : Fin d → ℝ) (arrival : Bool) (u V b : ℝ),
    0 < u → 0 < V → 0 < b →
    stationaryVariance st.mu f ≤ V →
    (∀ i, |f i - stationaryMean st.mu f| ≤ b) →
    eventProb Q.P st.mu (fun Y : Fin (m+1) → Fin d =>
      u ≤ |stateSum f arrival Y - (m : ℝ) * stationaryMean st.mu f|)
      ≤ 2 * exp (-(u^2 * Γ) / (8 * ((m : ℝ) + 1 / Γ) * V + 20 * u * b))

/-- The exact corrected inequality [4, Theorem 3.11, (3.25)], before
replacing its variance and centered sup norm by upper bounds. -/
def PaulinOriginalInput {d : ℕ} (Q : Stoch d) (st : Stationary Q) (Γ : ℝ) : Prop :=
  ∀ (m : ℕ) (f : Fin d → ℝ) (arrival : Bool) (u : ℝ),
    0 < u → (∃ i j, f i ≠ f j) →
    eventProb Q.P st.mu (fun Y : Fin (m+1) → Fin d =>
      u ≤ |stateSum f arrival Y - (m:ℝ)*stationaryMean st.mu f|)
      ≤ 2*exp (-(u^2*Γ) / (8*((m:ℝ)+1/Γ)*stationaryVariance st.mu f +
          20*u*‖fun i => f i - stationaryMean st.mu f‖))

/-- Passing to variance and range upper bounds loses no mathematical input.
Constant functions are handled directly, so the original nonconstant-function
hypothesis does not create an unproved exceptional case. -/
theorem paulin_upper_bounds {d : ℕ} (Q : Stoch d) (st : Stationary Q) (Γ : ℝ)
    (hΓ : 0 < Γ) (hinput : PaulinOriginalInput Q st Γ) : PaulinBernsteinInput Q st Γ := by
  classical
  intro m f arrival u V b hu hV hb hvar hrange
  by_cases hf : ∃ i j, f i ≠ f j
  · have hvariance : 0 ≤ stationaryVariance st.mu f :=
      sum_nonneg (fun i _ => mul_nonneg (st.nonneg i) (sq_nonneg _))
    have hnorm : 0 < ‖fun i => f i - stationaryMean st.mu f‖ := by
      apply norm_pos_iff.mpr
      intro hz
      obtain ⟨i, j, hij⟩ := hf
      have hi := congrFun hz i
      have hj := congrFun hz j
      apply hij
      dsimp at hi hj
      linarith
    have hnormle : ‖fun i => f i - stationaryMean st.mu f‖ ≤ b := by
      exact (pi_norm_le_iff_of_nonneg (le_of_lt hb)).mpr (by simpa only [Real.norm_eq_abs] using hrange)
    have hcoef : 0 ≤ 8*((m:ℝ)+1/Γ) := by positivity
    have hdpos : 0 < 8*((m:ℝ)+1/Γ)*stationaryVariance st.mu f +
        20*u*‖fun i => f i - stationaryMean st.mu f‖ := by positivity
    have hdle : 8*((m:ℝ)+1/Γ)*stationaryVariance st.mu f +
        20*u*‖fun i => f i - stationaryMean st.mu f‖ ≤ 8*((m:ℝ)+1/Γ)*V+20*u*b := by
      exact add_le_add (mul_le_mul_of_nonneg_left hvar hcoef)
        (mul_le_mul_of_nonneg_left hnormle (by positivity))
    calc _ ≤ 2*exp (-(u^2*Γ) / (8*((m:ℝ)+1/Γ)*stationaryVariance st.mu f +
          20*u*‖fun i => f i - stationaryMean st.mu f‖)) := hinput m f arrival u hu hf
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.exp_le_exp.mpr
        have hfrac := div_le_div_of_nonneg_left (show 0 ≤ u^2*Γ by positivity) hdpos hdle
        simpa only [neg_div] using neg_le_neg hfrac
  · have hc : ∀ i j, f i = f j := by
      intro i j
      by_contra hij
      exact hf ⟨i,j,hij⟩
    have hzero : ∀ Y : Fin (m+1) → Fin d,
        stateSum f arrival Y - (m:ℝ)*stationaryMean st.mu f = 0 := by
      intro Y
      have hmean : stationaryMean st.mu f = f (Y 0) := by
        unfold stationaryMean
        simp_rw [hc _ (Y 0)]
        rw [← sum_mul, st.sum_one, one_mul]
      rw [hmean]
      unfold stateSum
      simp_rw [hc _ (Y 0)]
      simp
    have hempty : (univ : Finset (Fin (m+1) → Fin d)).filter
        (fun Y => u ≤ |stateSum f arrival Y - (m:ℝ)*stationaryMean st.mu f|) = ∅ := by
      ext Y
      simp [hzero Y, not_le.mpr hu]
    unfold eventProb
    rw [hempty]
    simp only [pathMeasure, sum_empty]
    positivity

/-- The denominator estimate responsible for the constant 36 in (10). -/
theorem bernstein_denominator_le (m pi Γ η : ℝ)
    (hm : 0 < m) (hpi : 0 < pi) (hΓ : 0 < Γ)
    (hmΓ : 1 ≤ m * Γ) (hη : 0 < η) (hη1 : η ≤ 1) :
    0 < 8 * (m + 1 / Γ) * pi + 20 * (η * m * pi) * 1 ∧
    8 * (m + 1 / Γ) * pi + 20 * (η * m * pi) * 1 ≤ 36 * m * pi := by
  have hinv : 1 / Γ ≤ m := (div_le_iff₀ hΓ).mpr (by nlinarith)
  have hmp : 0 < m * pi := mul_pos hm hpi
  constructor
  · positivity
  · nlinarith [mul_nonneg (sub_nonneg.mpr hinv) (le_of_lt hpi),
      mul_nonneg (sub_nonneg.mpr hη1) (le_of_lt hmp)]

/-- Numerical specialization of Bernstein at `u = η m pi`. -/
theorem bernstein_indicator_exponent (m pi Γ η : ℝ)
    (hm : 0 < m) (hpi : 0 < pi) (hΓ : 0 < Γ)
    (hmΓ : 1 ≤ m * Γ) (hη : 0 < η) (hη1 : η ≤ 1) :
    -((η * m * pi)^2 * Γ / (8 * (m + 1 / Γ) * pi + 20 * (η * m * pi) * 1))
      ≤ -(η^2 * m * pi * Γ / 36) := by
  obtain ⟨hden, hdenle⟩ := bernstein_denominator_le m pi Γ η hm hpi hΓ hmΓ hη hη1
  have hnum : 0 ≤ (η * m * pi)^2 * Γ := mul_nonneg (sq_nonneg _) (le_of_lt hΓ)
  have hfrac := div_le_div_of_nonneg_left hnum hden hdenle
  have heq : (η*m*pi)^2 * Γ / (36*m*pi) = η^2*m*pi*Γ/36 := by
    field_simp
    <;> ring
  rw [heq] at hfrac
  exact neg_le_neg hfrac

/-- Probability-vector coordinates are at most one. -/
lemma probability_coordinate_le_one {d : ℕ} (mu : Fin d → ℝ)
    (hmu : ∀ i, 0 ≤ mu i) (hsum : ∑ i, mu i = 1) (i : Fin d) : mu i ≤ 1 := by
  rw [← hsum]
  exact single_le_sum (fun j _ => hmu j) (mem_univ i)

/-- Comparison (11), with its pointwise hypothesis discharged for every
initial probability distribution, using the project's stationary minimum. -/
theorem eventProb_initial_le {d m : ℕ} [NeZero d] (Q : Stoch d) (st : Stationary Q)
    (mu : Fin d → ℝ) (hmu : ∀ i, 0 ≤ mu i) (hsum : ∑ i, mu i = 1)
    (E : (Fin (m+1) → Fin d) → Prop) :
    eventProb Q.P mu E ≤ eventProb Q.P st.mu E / Stationary.star st := by
  classical
  have hp := Stationary.star_pos st
  have hratio : ∀ i, mu i ≤ st.mu i / Stationary.star st := by
    intro i
    calc mu i ≤ 1 := probability_coordinate_le_one mu hmu hsum i
      _ ≤ st.mu i / Stationary.star st := (le_div_iff₀ hp).mpr (by
        simpa using Stationary.star_le st i)
  have hpath : ∀ Y : Fin (m+1) → Fin d,
      pathProb Q.P mu Y ≤ pathProb Q.P st.mu Y / Stationary.star st := by
    intro Y
    unfold pathProb
    have hprod : 0 ≤ ∏ t : Fin m, Q.P (Y t.castSucc) (Y t.succ) :=
      prod_nonneg (fun t _ => Q.nonneg _ _)
    calc mu (Y 0) * _ ≤ (st.mu (Y 0) / Stationary.star st) * _ :=
        mul_le_mul_of_nonneg_right (hratio _) hprod
      _ = _ := by ring
  unfold eventProb pathMeasure
  rw [sum_div]
  exact sum_le_sum (fun Y _ => hpath Y)

/-- The state indicator used for the occupation estimate. -/
noncomputable def stateIndicator {d : ℕ} (i : Fin d) (j : Fin d) : ℝ :=
  if j = i then 1 else 0

lemma indicator_mean {d : ℕ} (pi : Fin d → ℝ) (i : Fin d) :
    stationaryMean pi (stateIndicator i) = pi i := by
  classical
  simp [stationaryMean, stateIndicator, mul_ite]

lemma indicator_variance {d : ℕ} (pi : Fin d → ℝ) (hsum : ∑ j, pi j = 1)
    (i : Fin d) : stationaryVariance pi (stateIndicator i) = pi i - (pi i)^2 := by
  classical
  unfold stationaryVariance
  rw [indicator_mean]
  have hexpand : ∀ j, pi j * (stateIndicator i j - pi i)^2 =
      pi j * stateIndicator i j - 2*pi i*(pi j*stateIndicator i j) + (pi i)^2*pi j := by
    intro j
    unfold stateIndicator
    split_ifs <;> ring
  simp_rw [hexpand]
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum]
  change stationaryMean pi (stateIndicator i) - 2*pi i*stationaryMean pi (stateIndicator i)
    + (pi i)^2*(∑ j, pi j) = _
  rw [indicator_mean, hsum]
  ring

/-- (10), simultaneously for the departure and arrival occupation counts. -/
theorem occupation_tail_stationary {d m : ℕ} (Q : Stoch d) (st : Stationary Q)
    (Γ η : ℝ) (hΓ : 0 < Γ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hmΓ : 1 ≤ (m:ℝ)*Γ) (hBernstein : PaulinBernsteinInput Q st Γ)
    (arrival : Bool) (i : Fin d) :
    eventProb Q.P st.mu (fun Y : Fin (m+1) → Fin d =>
      η*(m:ℝ)*st.mu i < |stateSum (stateIndicator i) arrival Y - (m:ℝ)*st.mu i|)
      ≤ 2*exp (-(η^2*(m:ℝ)*st.mu i*Γ/36)) := by
  have hm : 0 < (m:ℝ) := by nlinarith [show (0:ℝ) ≤ (m:ℝ) from Nat.cast_nonneg m]
  have hpi := st.pos i
  have hpi1 := probability_coordinate_le_one st.mu st.nonneg st.sum_one i
  have hvar : stationaryVariance st.mu (stateIndicator i) ≤ st.mu i := by
    rw [indicator_variance st.mu st.sum_one i]
    nlinarith [sq_nonneg (st.mu i)]
  have hrange : ∀ j, |stateIndicator i j - stationaryMean st.mu (stateIndicator i)| ≤ 1 := by
    intro j
    rw [indicator_mean]
    unfold stateIndicator
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  calc eventProb Q.P st.mu (fun Y : Fin (m+1) → Fin d =>
        η*(m:ℝ)*st.mu i < |stateSum (stateIndicator i) arrival Y - (m:ℝ)*st.mu i|)
      ≤ eventProb Q.P st.mu (fun Y : Fin (m+1) → Fin d =>
        η*(m:ℝ)*st.mu i ≤ |stateSum (stateIndicator i) arrival Y - (m:ℝ)*stationaryMean st.mu (stateIndicator i)|) :=
      eventProb_mono Q.P st.mu Q.nonneg st.nonneg (by
        intro Y hY; rw [indicator_mean]; exact le_of_lt hY)
    _ ≤ 2*exp (-((η*(m:ℝ)*st.mu i)^2*Γ) /
        (8*((m:ℝ)+1/Γ)*st.mu i+20*(η*(m:ℝ)*st.mu i)*1)) :=
      hBernstein m (stateIndicator i) arrival _ (st.mu i) 1 (by positivity) hpi
        (by norm_num) hvar hrange
    _ ≤ 2*exp (-(η^2*(m:ℝ)*st.mu i*Γ/36)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      convert bernstein_indicator_exponent (m:ℝ) (st.mu i) Γ η hm hpi hΓ hmΓ hη hη1 using 1 <;> ring

/-- Occupation tail from any initial law, with the stationary minimum in both
its prefactor and exponent. -/
theorem occupation_tail_initial {d m : ℕ} [NeZero d] (Q : Stoch d) (st : Stationary Q)
    (mu : Fin d → ℝ) (hmu : ∀ i, 0 ≤ mu i) (hsum : ∑ i, mu i = 1)
    (Γ η : ℝ) (hΓ : 0 < Γ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hmΓ : 1 ≤ (m:ℝ)*Γ) (hBernstein : PaulinBernsteinInput Q st Γ)
    (arrival : Bool) (i : Fin d) :
    eventProb Q.P mu (fun Y : Fin (m+1) → Fin d =>
      η*(m:ℝ)*st.mu i < |stateSum (stateIndicator i) arrival Y - (m:ℝ)*st.mu i|)
      ≤ 2 / Stationary.star st * exp (-((m:ℝ)*Stationary.star st*Γ*η^2/36)) := by
  have hp := Stationary.star_pos st
  have hm : 0 ≤ (m:ℝ) := Nat.cast_nonneg m
  calc _ ≤ eventProb Q.P st.mu (fun Y : Fin (m+1) → Fin d =>
      η*(m:ℝ)*st.mu i < |stateSum (stateIndicator i) arrival Y - (m:ℝ)*st.mu i|)
        / Stationary.star st := eventProb_initial_le Q st mu hmu hsum _
    _ ≤ (2*exp (-(η^2*(m:ℝ)*st.mu i*Γ/36))) / Stationary.star st :=
      div_le_div_of_nonneg_right
        (occupation_tail_stationary Q st Γ η hΓ hη hη1 hmΓ hBernstein arrival i) (le_of_lt hp)
    _ ≤ 2 / Stationary.star st * exp (-((m:ℝ)*Stationary.star st*Γ*η^2/36)) := by
      have hc : 0 ≤ η^2*(m:ℝ)*Γ := by positivity
      have hprod := mul_le_mul_of_nonneg_left (Stationary.star_le st i) hc
      have hexp : exp (-(η^2*(m:ℝ)*st.mu i*Γ/36)) ≤
          exp (-((m:ℝ)*Stationary.star st*Γ*η^2/36)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      convert mul_le_mul_of_nonneg_left hexp (show 0 ≤ 2/Stationary.star st by positivity) using 1 <;> ring

lemma outDeg_eq_stateSum {d m : ℕ} (Y : Fin (m+1) → Fin d) (i : Fin d) :
    (outDeg Y i : ℝ) = stateSum (stateIndicator i) false Y := by
  classical
  unfold outDeg countMat stateSum
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [sum_comm]
  apply sum_congr rfl
  intro t _
  by_cases hi : Y t.castSucc = i
  · simp [observationIndex, stateIndicator, hi, eq_comm]
  · simp [observationIndex, stateIndicator, hi]

lemma inDeg_eq_stateSum {d m : ℕ} (Y : Fin (m+1) → Fin d) (i : Fin d) :
    (inDeg Y i : ℝ) = stateSum (stateIndicator i) true Y := by
  classical
  unfold inDeg countMat stateSum
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [sum_comm]
  apply sum_congr rfl
  intro t _
  by_cases hi : Y t.succ = i
  · simp [observationIndex, stateIndicator, hi, eq_comm]
  · simp [observationIndex, stateIndicator, hi]

/-- Joint degree event, written as count deviations before division by `m`. -/
def degreeEvent {d m : ℕ} (pi : Fin d → ℝ) (η : ℝ)
    (Y : Fin (m+1) → Fin d) : Prop :=
  ∀ arrival i, |stateSum (stateIndicator i) arrival Y - (m:ℝ)*pi i| ≤ η*(m:ℝ)*pi i

/-- Event (15) is exactly the simultaneous relative error bounds for the
incoming and outgoing degree vectors. -/
theorem degreeEvent_iff_counts {d m : ℕ} (Y : Fin (m+1) → Fin d)
    (pi : Fin d → ℝ) (η : ℝ) (hm : 0 < m) :
    degreeEvent pi η Y ↔ ∀ i,
      (1-η)*pi i ≤ (outDeg Y i:ℝ)/(m:ℝ) ∧
      (outDeg Y i:ℝ)/(m:ℝ) ≤ (1+η)*pi i ∧
      (1-η)*pi i ≤ (inDeg Y i:ℝ)/(m:ℝ) ∧
      (inDeg Y i:ℝ)/(m:ℝ) ≤ (1+η)*pi i := by
  have hm' : 0 < (m:ℝ) := Nat.cast_pos.mpr hm
  constructor
  · intro h i
    have ho := abs_le.mp (h false i)
    have hi := abs_le.mp (h true i)
    rw [← outDeg_eq_stateSum Y i] at ho
    rw [← inDeg_eq_stateSum Y i] at hi
    exact ⟨(le_div_iff₀ hm').mpr (by nlinarith),
      (div_le_iff₀ hm').mpr (by nlinarith),
      (le_div_iff₀ hm').mpr (by nlinarith),
      (div_le_iff₀ hm').mpr (by nlinarith)⟩
  · intro h arrival i
    obtain ⟨hol, hou, hil, hiu⟩ := h i
    have hol' := (le_div_iff₀ hm').mp hol
    have hou' := (div_le_iff₀ hm').mp hou
    have hil' := (le_div_iff₀ hm').mp hil
    have hiu' := (div_le_iff₀ hm').mp hiu
    cases arrival
    · rw [← outDeg_eq_stateSum Y i, abs_le]
      constructor <;> nlinarith
    · rw [← inDeg_eq_stateSum Y i, abs_le]
      constructor <;> nlinarith

/-- Every degree is strictly positive on event (15). -/
theorem degreeEvent_degPos {d m : ℕ} (Y : Fin (m+1) → Fin d)
    (pi : Fin d → ℝ) (hpi : ∀ i, 0 < pi i) (η : ℝ) (hη : η < 1)
    (hm : 0 < m) (h : degreeEvent pi η Y) : degPos Y := by
  intro i
  have ho := abs_le.mp (h false i)
  have hi := abs_le.mp (h true i)
  rw [← outDeg_eq_stateSum Y i] at ho
  rw [← inDeg_eq_stateSum Y i] at hi
  have hm' : 0 < (m:ℝ) := Nat.cast_pos.mpr hm
  have hpos : 0 < (1-η)*(m:ℝ)*pi i :=
    mul_pos (mul_pos (sub_pos.mpr hη) hm') (hpi i)
  constructor
  · exact Nat.cast_pos.mp (by nlinarith [ho.1] : (0:ℝ) < (outDeg Y i:ℝ))
  · exact Nat.cast_pos.mp (by nlinarith [hi.1] : (0:ℝ) < (inDeg Y i:ℝ))

/-- The first summand in (13), including the factor `4d/p`. -/
theorem degree_failure_bound {d m : ℕ} [NeZero d] (Q : Stoch d) (st : Stationary Q)
    (mu : Fin d → ℝ) (hmu : ∀ i, 0 ≤ mu i) (hsum : ∑ i, mu i = 1)
    (Γ η : ℝ) (hΓ : 0 < Γ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hmΓ : 1 ≤ (m:ℝ)*Γ) (hBernstein : PaulinBernsteinInput Q st Γ) :
    eventProb Q.P mu (fun Y : Fin (m+1) → Fin d => ¬ degreeEvent st.mu η Y)
      ≤ 4*(d:ℝ)/Stationary.star st * exp (-((m:ℝ)*Stationary.star st*Γ*η^2/36)) := by
  classical
  have heq : (fun Y : Fin (m+1) → Fin d => ¬ degreeEvent st.mu η Y) =
      (fun Y => ∃ a : Bool × Fin d,
        η*(m:ℝ)*st.mu a.2 < |stateSum (stateIndicator a.2) a.1 Y - (m:ℝ)*st.mu a.2|) := by
    funext Y
    simp only [degreeEvent, not_forall, not_le, Prod.exists]
  rw [heq]
  calc _ ≤ ∑ a : Bool × Fin d, eventProb Q.P mu (fun Y : Fin (m+1) → Fin d =>
        η*(m:ℝ)*st.mu a.2 < |stateSum (stateIndicator a.2) a.1 Y - (m:ℝ)*st.mu a.2|) :=
      eventProb_exists_le Q.P mu Q.nonneg hmu _
    _ ≤ ∑ _a : Bool × Fin d,
        2 / Stationary.star st * exp (-((m:ℝ)*Stationary.star st*Γ*η^2/36)) :=
      sum_le_sum (fun a _ => occupation_tail_initial Q st mu hmu hsum Γ η hΓ hη hη1 hmΓ hBernstein a.1 a.2)
    _ = _ := by simp [Fintype.card_prod, Fintype.card_fin]; ring

/-- A two-sided joint-event Freedman tail. Its arguments are the actual
norms of the self-adjoint martingale sum and predictable quadratic variation.
An application must supply this theorem for its constructed process after
checking the external theorem's martingale, self-adjointness and increment
bound hypotheses. -/
def FreedmanJointInput {d m : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (D : ℕ) (R : ℝ) (sumNorm varianceNorm : (Fin (m+1) → Fin d) → ℝ) : Prop :=
  ∀ u v : ℝ, 0 < u → 0 < v →
    eventProb Q.P mu (fun Y => u ≤ sumNorm Y ∧ varianceNorm Y ≤ v)
      ≤ 2 * (D : ℝ) * exp (-(u^2) / (2 * (v + R*u/3)))

/-- Equality of the observations generating the path filtration at time `t`. -/
def samePrefix {d m : ℕ} (t : ℕ) (Y W : Fin (m+1) → Fin d) : Prop :=
  ∀ k : Fin (m+1), k.val ≤ t → Y k = W k

/-- Conditional expectation on a prefix atom of the finite path space.
Zero-mass atoms receive value zero, as usual for an a.e. representative. -/
noncomputable def pathMatrixCondExp {d m D : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (t : ℕ) (A : (Fin (m+1) → Fin d) → Matrix (Fin D) (Fin D) ℝ)
    (Y : Fin (m+1) → Fin d) : Matrix (Fin D) (Fin D) ℝ := by
  classical
  exact (eventProb Q.P mu (samePrefix t Y))⁻¹ •
    ∑ W ∈ univ.filter (samePrefix t Y), pathProb Q.P mu W • A W

/-- Euclidean operator norm, without relying on the default entrywise matrix
norm instance. -/
noncomputable def euclideanMatrixNorm {D : ℕ} (A : Matrix (Fin D) (Fin D) ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := Fin D) (𝕜 := ℝ) A‖

noncomputable def martingaleSumNorm {d m D : ℕ}
    (Z : Fin m → (Fin (m+1) → Fin d) → Matrix (Fin D) (Fin D) ℝ)
    (Y : Fin (m+1) → Fin d) : ℝ := euclideanMatrixNorm (∑ t, Z t Y)

noncomputable def predictableVariationNorm {d m D : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (Z : Fin m → (Fin (m+1) → Fin d) → Matrix (Fin D) (Fin D) ℝ)
    (Y : Fin (m+1) → Fin d) : ℝ :=
  euclideanMatrixNorm (∑ t : Fin m, pathMatrixCondExp Q mu t.val (fun W => Z t W * Z t W) Y)

/-- Complete external matrix Freedman input (12) in finite-path coordinates.
The increment at index `t` is revealed at time `t+1`, is conditionally centered
at time `t`, and is bounded by `R` in Euclidean operator norm. The predictable
variation is computed from those same increments, rather than supplied as an
unrelated random variable. This is an explicit theorem dependency, not an
axiom or a claimed proof of Tropp's result. -/
def MatrixFreedmanInput {d : ℕ} (Q : Stoch d) (mu : Fin d → ℝ) : Prop :=
  ∀ (m D : ℕ) (R : ℝ)
    (Z : Fin m → (Fin (m+1) → Fin d) → Matrix (Fin D) (Fin D) ℝ),
    (∀ i, 0 ≤ mu i) → (∑ i, mu i = 1) → 0 < R →
    (∀ t Y, (Z t Y).IsHermitian) →
    (∀ t Y W, samePrefix (t.val+1) Y W → Z t Y = Z t W) →
    (∀ t Y, pathMatrixCondExp Q mu t.val (Z t) Y = 0) →
    (∀ t Y, euclideanMatrixNorm (Z t Y) ≤ R) →
    ∀ u v : ℝ, 0 < u → 0 < v →
      eventProb Q.P mu (fun Y => u ≤ martingaleSumNorm Z Y ∧
        predictableVariationNorm Q mu Z Y ≤ v)
      ≤ 2*(D:ℝ)*exp (-(u^2)/(2*(v+R*u/3)))

/-- Instantiate the full external theorem only after providing its concrete
matrix martingale hypotheses. -/
theorem matrixFreedman_joint {d m D : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (hinput : MatrixFreedmanInput Q mu)
    (R : ℝ) (Z : Fin m → (Fin (m+1) → Fin d) → Matrix (Fin D) (Fin D) ℝ)
    (hmu : ∀ i, 0 ≤ mu i) (hsum : ∑ i, mu i = 1) (hR : 0 < R)
    (hsa : ∀ t Y, (Z t Y).IsHermitian)
    (hadapted : ∀ t Y W, samePrefix (t.val+1) Y W → Z t Y = Z t W)
    (hcentered : ∀ t Y, pathMatrixCondExp Q mu t.val (Z t) Y = 0)
    (hbound : ∀ t Y, euclideanMatrixNorm (Z t Y) ≤ R) :
    FreedmanJointInput Q mu D R (martingaleSumNorm Z) (predictableVariationNorm Q mu Z) :=
  hinput m D R Z hmu hsum hR hsa hadapted hcentered hbound

/-- The exact exponent identity before inequality (18). -/
theorem freedman_exponent_identity (m p τ η : ℝ)
    (hm : 0 < m) (hp : 0 < p) (hτ : 0 < τ) :
    (η*m)^2 / (2 * ((2/(p*τ))*m*(1+η) + (2/(p*τ))*(η*m)/3))
      = m*p*τ*η^2 / (4*(1+4*η/3)) := by
  field_simp
  <;> ring

/-- The constant `3/16` in (18) follows from `η ≤ 1/4`. -/
theorem freedman_exponent_lower (m p τ η : ℝ)
    (hm : 0 < m) (hp : 0 < p) (hτ : 0 < τ)
    (hη : 0 < η) (hη4 : η ≤ 1/4) :
    3*m*p*τ*η^2/16 ≤
      (η*m)^2 / (2 * ((2/(p*τ))*m*(1+η) + (2/(p*τ))*(η*m)/3)) := by
  rw [freedman_exponent_identity m p τ η hm hp hτ]
  have hden : 0 < 4*(1+4*η/3) := by positivity
  apply (le_div_iff₀ hden).mpr
  have hnum : 0 ≤ m*p*τ*η^2 := by positivity
  nlinarith [mul_nonneg hnum (sub_nonneg.mpr hη4)]

/-- (18), from the joint-event Freedman input and the variation bound on the
degree event. This uses event inclusion; the martingale is never conditioned
on the degree event. -/
theorem freedman_on_degree_event {d m : ℕ} (Q : Stoch d)
    (mu : Fin d → ℝ) (hmu : ∀ i, 0 ≤ mu i)
    (p τ η : ℝ) (hm : 0 < m) (hp : 0 < p) (hτ : 0 < τ)
    (hη : 0 < η) (hη4 : η ≤ 1/4)
    (E : (Fin (m+1) → Fin d) → Prop)
    (sumNorm varianceNorm : (Fin (m+1) → Fin d) → ℝ)
    (hvariation : ∀ Y, E Y → varianceNorm Y ≤ (2/(p*τ))*(m:ℝ)*(1+η))
    (hFreedman : FreedmanJointInput Q mu (2*d) (2/(p*τ)) sumNorm varianceNorm) :
    eventProb Q.P mu (fun Y => E Y ∧ η*(m:ℝ) < sumNorm Y)
      ≤ 4*(d:ℝ)*exp (-(3*(m:ℝ)*p*τ*η^2/16)) := by
  have hm' : 0 < (m:ℝ) := Nat.cast_pos.mpr hm
  have hu : 0 < η*(m:ℝ) := mul_pos hη hm'
  have hv : 0 < (2/(p*τ))*(m:ℝ)*(1+η) := by positivity
  calc eventProb Q.P mu (fun Y => E Y ∧ η*(m:ℝ) < sumNorm Y)
      ≤ eventProb Q.P mu (fun Y => η*(m:ℝ) ≤ sumNorm Y ∧
          varianceNorm Y ≤ (2/(p*τ))*(m:ℝ)*(1+η)) :=
        eventProb_mono Q.P mu Q.nonneg hmu (fun Y h => ⟨le_of_lt h.2, hvariation Y h.1⟩)
    _ ≤ 2*((2*d:ℕ):ℝ)*exp (-((η*(m:ℝ))^2) /
        (2*((2/(p*τ))*(m:ℝ)*(1+η) + (2/(p*τ))*(η*(m:ℝ))/3))) :=
      hFreedman _ _ hu hv
    _ ≤ 4*(d:ℝ)*exp (-(3*(m:ℝ)*p*τ*η^2/16)) := by
      have hexp := Real.exp_le_exp.mpr
        (neg_le_neg (freedman_exponent_lower (m:ℝ) p τ η hm' hp hτ hη hη4))
      simp only [neg_div] at *
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      nlinarith [mul_nonneg (show 0 ≤ (d:ℝ) by positivity) (sub_nonneg.mpr hexp)]

end PsgEst
