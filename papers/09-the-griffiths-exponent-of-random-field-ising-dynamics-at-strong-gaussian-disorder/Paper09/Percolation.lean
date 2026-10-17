import Paper09.FiniteProb
import Paper09.Defects
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Mathlib.Combinatorics.Pigeonhole

open Finset BigOperators Classical

set_option maxHeartbeats 1000000

noncomputable section
namespace Paper09.Percolation

/-- Probability of an event in a finite probability space. -/
def eventProb {Ω : Type*} [Fintype Ω] (μ : FinProb Ω) (A : Ω → Prop) : ℝ :=
  μ.expect (fun ω => if A ω then 1 else 0)

theorem eventProb_nonneg {Ω : Type*} [Fintype Ω] (μ : FinProb Ω) (A : Ω → Prop) :
    0 ≤ eventProb μ A := by
  exact μ.expect_nonneg (fun ω => by split_ifs <;> norm_num)

theorem eventProb_mono {Ω : Type*} [Fintype Ω] (μ : FinProb Ω)
    {A B : Ω → Prop} (h : ∀ ω, A ω → B ω) : eventProb μ A ≤ eventProb μ B := by
  apply μ.expect_mono
  intro ω
  by_cases ha : A ω
  · have hb := h ω ha
    simp [ha, hb]
  · simp only [if_neg ha]
    split_ifs <;> norm_num

/-- Markov's inequality, proved by summing the pointwise inequality. -/
theorem markov {Ω : Type*} [Fintype Ω] (μ : FinProb Ω) (X : Ω → ℝ)
    (hX : ∀ ω, 0 ≤ X ω) (a : ℝ) (_ha : 0 < a) :
    a * eventProb μ (fun ω => a ≤ X ω) ≤ μ.expect X := by
  rw [eventProb, ← FinProb.expect_smul]
  apply μ.expect_mono
  intro ω
  by_cases h : a ≤ X ω
  · simp only [if_pos h, mul_one]; exact h
  · simp only [if_neg h, mul_zero]; exact hX ω

/-- The union bound for a finite indexed family of events. -/
theorem eventProb_exists_le {Ω I : Type*} [Fintype Ω] [Fintype I]
    (μ : FinProb Ω) (A : I → Ω → Prop) :
    eventProb μ (fun ω => ∃ i, A i ω) ≤ ∑ i, eventProb μ (A i) := by
  have hpoint (ω : Ω) :
      (if ∃ i, A i ω then (1 : ℝ) else 0) ≤ ∑ i, if A i ω then 1 else 0 := by
    split_ifs with h
    · obtain ⟨i, hi⟩ := h
      exact (by simpa only [if_pos hi] using
        (single_le_sum (f := fun i => if A i ω then (1 : ℝ) else 0)
          (fun i _ => by dsimp; split_ifs <;> norm_num) (mem_univ i)))
    · exact sum_nonneg (fun i _ => by split_ifs <;> norm_num)
  calc
    eventProb μ (fun ω => ∃ i, A i ω)
        ≤ μ.expect (fun ω => ∑ i, if A i ω then 1 else 0) := by
          apply μ.expect_mono
          intro ω
          by_cases h : ∃ i, A i ω <;> simpa [h] using hpoint ω
    _ = ∑ i, eventProb μ (A i) := by
      simp only [FinProb.expect, eventProb, mul_sum]
      rw [sum_comm]

/-- One Bernoulli mark with opening parameter `p`. -/
def markWeight (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

/-- Independent Bernoulli site marks on an arbitrary finite set of sites.
The normalization is the product-of-sums identity, rather than an assumption. -/
def bernoulliSites (I : Type*) [Fintype I] [DecidableEq I] (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    FinProb (I → Bool) where
  w ω := ∏ i, markWeight p (ω i)
  nonneg ω := prod_nonneg (fun i _ => by
    unfold markWeight
    split_ifs <;> first | exact hp | exact sub_nonneg.mpr hp1)
  sum_one := by
    rw [← Fintype.prod_sum]
    simp [markWeight]

/-- Number of open marks in a set of sites. -/
def openCount {I : Type*} (S : Finset I) (ω : I → Bool) : ℕ :=
  (S.filter (fun i => ω i = true)).card

theorem prod_open_factor {I : Type*} (S : Finset I) (ω : I → Bool) (s : ℝ) :
    (∏ i ∈ S, if ω i then s else 1) = s ^ openCount S ω := by
  simp only [openCount, ← Finset.prod_filter]
  rw [Finset.prod_const]

/-- The probability generating function of the actual independent-site count. -/
theorem bernoulliSites_moment {I : Type*} [Fintype I] [DecidableEq I] (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (s : ℝ) :
    (bernoulliSites I p hp hp1).expect (fun ω => s ^ openCount univ ω) =
      (1 + p * (s - 1)) ^ Fintype.card I := by
  unfold FinProb.expect bernoulliSites
  simp only
  conv_lhs => arg 2; intro ω; rw [← prod_open_factor]
  simp_rw [← prod_mul_distrib]
  rw [← Fintype.prod_sum (fun _ : I => fun b : Bool =>
    markWeight p b * if b then s else 1)]
  simp only [markWeight, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte,
    mul_one]
  have heq : p * s + (1 - p) = 1 + p * (s - 1) := by ring
  simp [heq]

/-- Exponential Markov bound for the actual independent Bernoulli count.
This includes the probability generating function calculation, with no moment
or tail estimate supplied as a premise. -/
theorem bernoulli_count_tail_mgf {I : Type*} [Fintype I] [DecidableEq I] (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (r : ℕ) (s : ℝ) (hs : 1 ≤ s) :
    s ^ r * eventProb (bernoulliSites I p hp hp1)
      (fun ω => r ≤ openCount univ ω) ≤
        (1 + p * (s - 1)) ^ Fintype.card I := by
  have hs0 : 0 ≤ s := le_trans (by norm_num) hs
  have hpoint (ω : I → Bool) :
      s ^ r * (if r ≤ openCount univ ω then (1 : ℝ) else 0) ≤
        s ^ openCount univ ω := by
    by_cases h : r ≤ openCount univ ω
    · simp only [if_pos h, mul_one]
      exact pow_le_pow_right₀ hs h
    · simp only [if_neg h, mul_zero]
      exact pow_nonneg hs0 _
  have h := (bernoulliSites I p hp hp1).expect_mono hpoint
  rw [FinProb.expect_smul, bernoulliSites_moment] at h
  convert h using 1
  congr 1
  unfold eventProb
  congr 1
  funext ω
  by_cases h : r ≤ openCount univ ω <;> simp [h]

/-- The binomial Chernoff upper tail used in Lemma 3.2, for an explicit product
Bernoulli probability space. In particular there is no independence hypothesis
which can secretly assume the desired tail. -/
theorem bernoulli_count_tail_chernoff {I : Type*} [Fintype I] [DecidableEq I] (p : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) (hm : 0 < Fintype.card I)
    (r : ℕ) (hr : 0 < r) (hmean : (Fintype.card I : ℝ) * p ≤ r) :
    eventProb (bernoulliSites I p hp.le hp1) (fun ω => r ≤ openCount univ ω) ≤
      (Real.exp 1 * Fintype.card I * p / r) ^ r := by
  let m : ℝ := Fintype.card I
  let s : ℝ := (r : ℝ) / (m * p)
  have hm0 : 0 < m := by
    change (0 : ℝ) < (Fintype.card I : ℝ)
    exact_mod_cast hm
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hmp : 0 < m * p := mul_pos hm0 hp
  have hs : 1 ≤ s := by
    dsimp [s]
    exact (le_div_iff₀ hmp).mpr (by simpa [m] using hmean)
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have hg := bernoulli_count_tail_mgf (I := I) p hp.le hp1 r s hs
  have hbase : 0 ≤ p * (s - 1) := mul_nonneg hp.le (sub_nonneg.mpr hs)
  have hexp := Paper09.one_add_pow_le_exp (Fintype.card I) (p * (s - 1)) hbase
  have harg : (Fintype.card I : ℝ) * (p * (s - 1)) ≤ r := by
    have heq : m * p * s = r := by
      dsimp [s]
      field_simp
    change m * (p * (s - 1)) ≤ r
    nlinarith
  have hpow : (1 + p * (s - 1)) ^ Fintype.card I ≤ (Real.exp 1) ^ r := by
    calc
      _ ≤ Real.exp ((Fintype.card I : ℝ) * (p * (s - 1))) := hexp
      _ ≤ Real.exp (r : ℝ) := Real.exp_le_exp.mpr harg
      _ = (Real.exp 1) ^ r := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hdiv : eventProb (bernoulliSites I p hp.le hp1)
      (fun ω => r ≤ openCount univ ω) ≤ (Real.exp 1) ^ r / s ^ r := by
    apply (le_div_iff₀ (pow_pos hs0 r)).mpr
    exact (by simpa [mul_comm] using hg.trans hpow)
  have heq : Real.exp 1 / s = Real.exp 1 * Fintype.card I * p / r := by
    dsimp [s, m]
    field_simp
  simpa only [← div_pow, heq] using hdiv

/-- The numerical parameter regime in Lemma 3.2 gives the paper's actual
binomial probability bound `(e / 10)^r` for `2 d r` marks. -/
theorem bernoulli_exploration_marks_tail (d r : ℕ) (hd : 0 < d) (hr : 0 < r)
    (p : ℝ) (hp : 0 < p) (hpK : p < 1 / (20 * (d : ℝ))) :
    ∃ hp1 : p ≤ 1,
      eventProb (bernoulliSites (Fin (2 * d * r)) p hp.le hp1)
        (fun ω : Fin (2 * d * r) → Bool => r ≤ openCount univ ω) ≤ (Real.exp 1 / 10) ^ r := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hp20 : 20 * (d : ℝ) * p < 1 := by
    have h := (lt_div_iff₀ (show (0 : ℝ) < 20 * d by positivity)).mp hpK
    nlinarith
  have hsmall : 2 * (d : ℝ) * p < 1 / 10 := by linarith
  have hp1 : p ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_right hd1 hp.le]
  refine ⟨hp1, ?_⟩
  have hm : 0 < Fintype.card (Fin (2 * d * r)) := by simp only [Fintype.card_fin]; positivity
  have hmean : (Fintype.card (Fin (2 * d * r)) : ℝ) * p ≤ r := by
    simp only [Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
    have h := mul_lt_mul_of_pos_right hsmall hr0
    nlinarith
  have htail := bernoulli_count_tail_chernoff (I := Fin (2 * d * r))
    p hp hp1 hm r hr hmean
  have heq : Real.exp 1 * Fintype.card (Fin (2 * d * r)) * p / r =
      2 * (d : ℝ) * Real.exp 1 * p := by
    simp only [Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
    field_simp
  rw [heq] at htail
  apply htail.trans
  apply pow_le_pow_left₀ (by positivity)
  have h := mul_le_mul_of_nonneg_left hsmall.le (Real.exp_nonneg 1)
  nlinarith

/-- Independent field and auxiliary randomness, as a genuine product law. -/
def productLaw {H U : Type*} [Fintype H] [Fintype U]
    (μ : FinProb H) (ν : FinProb U) : FinProb (H × U) where
  w x := μ.w x.1 * ν.w x.2
  nonneg x := mul_nonneg (μ.nonneg x.1) (ν.nonneg x.2)
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp only [← mul_sum, ν.sum_one, mul_one, μ.sum_one]

/-- Quenched probability is obtained by averaging only the auxiliary marks. -/
def quenched {H U : Type*} [Fintype H] [Fintype U]
    (ν : FinProb U) (A : H → U → Prop) (h : H) : ℝ := eventProb ν (A h)

/-- Averaging quenched probabilities is exactly the annealed probability. -/
theorem quenched_average {H U : Type*} [Fintype H] [Fintype U]
    (μ : FinProb H) (ν : FinProb U) (A : H → U → Prop) :
    μ.expect (quenched ν A) = eventProb (productLaw μ ν) (fun x => A x.1 x.2) := by
  simp only [FinProb.expect, quenched, eventProb, productLaw, Fintype.sum_prod_type,
    mul_sum, mul_assoc]

/-- Markov's inequality for a quenched probability, with the annealed law
computed from the actual independent field and noise distributions. -/
theorem quenched_bad_probability {H U : Type*} [Fintype H] [Fintype U]
    (μ : FinProb H) (ν : FinProb U) (A : H → U → Prop) (a : ℝ) (ha : 0 < a) :
    eventProb μ (fun h => a < quenched ν A h) ≤
      eventProb (productLaw μ ν) (fun x => A x.1 x.2) / a := by
  have hm := markov μ (quenched ν A) (fun h => eventProb_nonneg ν (A h)) a ha
  have hsub := eventProb_mono μ (fun h => le_of_lt :
    ∀ h, a < quenched ν A h → a ≤ quenched ν A h)
  have hmul := mul_le_mul_of_nonneg_left hsub ha.le
  rw [quenched_average] at hm
  apply (le_div_iff₀ ha).mpr
  nlinarith

/-- The quenched bad-label union bound in (3.4). The event is the actual
existence of a location/radius with a too-large conditional probability. -/
theorem quenched_bad_union_bound {H U I : Type*} [Fintype H] [Fintype U] [Fintype I]
    (μ : FinProb H) (ν : FinProb U) (A : I → H → U → Prop) (radius : I → ℕ) :
    eventProb μ (fun h => ∃ i,
      Real.exp (-(radius i : ℝ)) < quenched ν (A i) h) ≤
      ∑ i, Real.exp (radius i : ℝ) *
        eventProb (productLaw μ ν) (fun x => A i x.1 x.2) := by
  apply (eventProb_exists_le μ _).trans
  apply sum_le_sum
  intro i _
  have h := quenched_bad_probability μ ν (A i)
    (Real.exp (-(radius i : ℝ))) (Real.exp_pos _)
  simpa only [Real.exp_neg, div_inv_eq_mul, mul_comm] using h

/-- Arbitrary independent finite coordinate laws, with normalization proved. -/
def independentFamily {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] (μ : ∀ i, FinProb (Ω i)) :
    FinProb (∀ i, Ω i) where
  w ω := ∏ i, (μ i).w (ω i)
  nonneg ω := prod_nonneg (fun i _ => (μ i).nonneg (ω i))
  sum_one := by
    rw [← Fintype.prod_sum]
    simp only [FinProb.sum_one, prod_const_one]

/-- Events of distinct coordinates of the product law are mutually independent. -/
theorem independentFamily_all_probability {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] (μ : ∀ i, FinProb (Ω i))
    (A : ∀ i, Ω i → Prop) :
    eventProb (independentFamily μ) (fun ω => ∀ i, A i (ω i)) =
      ∏ i, eventProb (μ i) (A i) := by
  have hfactor (ω : ∀ i, Ω i) :
      (@ite ℝ (∀ i, A i (ω i)) (Classical.propDecidable _) 1 0) =
        ∏ i, if A i (ω i) then 1 else 0 := by
    rw [Fintype.prod_boole]
    by_cases h : ∀ i, A i (ω i) <;> simp [h]
  unfold eventProb FinProb.expect independentFamily
  simp only
  simp_rw [hfactor, ← prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i ω => (μ i).w ω * if A i ω then 1 else 0)]

/-- Mutual independence of the site events in each color class. This is the
usual finite-event factorization; the color-class tail theorem below derives
its probability bound from this factorization and marginal bounds. -/
def IndependentWithinColors {H V C : Type*} [Fintype H]
    (μ : FinProb H) (A : V → H → Prop) (color : V → C) : Prop :=
  ∀ (c : C) (S : Finset V), (∀ v ∈ S, color v = c) →
    eventProb μ (fun h => ∀ v ∈ S, A v h) = ∏ v ∈ S, eventProb μ (A v)

/-- The `q^(ell / number-of-colors)` bound used for finite dependent bad labels
in Lemma 3.2. It is proved by an actual color pigeonhole argument and event
monotonicity; no bound for the all-bad event is assumed. -/
theorem finite_dependence_all_bad_bound {H V C : Type*}
    [Fintype H] [Fintype C] [Nonempty C] (μ : FinProb H)
    (A : V → H → Prop) (color : V → C)
    (hind : IndependentWithinColors μ A color) (S : Finset V)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hmarg : ∀ v ∈ S, eventProb μ (A v) ≤ q) :
    eventProb μ (fun h => ∀ v ∈ S, A v h) ≤
      q ^ ((S.card : ℝ) / Fintype.card C) := by
  classical
  have hC : (0 : ℝ) < Fintype.card C := by
    exact_mod_cast Fintype.card_pos
  obtain ⟨c, _, hc⟩ :=
    Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
      (s := S) (t := (univ : Finset C)) (f := color)
      (b := (S.card : ℝ) / Fintype.card C)
      (fun _ _ => mem_univ _) univ_nonempty (by
        simp only [card_univ, nsmul_eq_mul]
        field_simp
        exact le_rfl)
  let T := S.filter (fun v => color v = c)
  have hT : ∀ v ∈ T, color v = c := by
    intro v hv
    exact (mem_filter.mp hv).2
  calc
    eventProb μ (fun h => ∀ v ∈ S, A v h)
        ≤ eventProb μ (fun h => ∀ v ∈ T, A v h) :=
      eventProb_mono μ (fun h hh v hv => hh v (mem_filter.mp hv).1)
    _ = ∏ v ∈ T, eventProb μ (A v) := hind c T hT
    _ ≤ ∏ _v ∈ T, q := prod_le_prod
      (fun v _ => eventProb_nonneg μ (A v))
      (fun v hv => hmarg v (mem_filter.mp hv).1)
    _ = q ^ T.card := prod_const q
    _ ≤ q ^ ((S.card : ℝ) / Fintype.card C) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge' hq hq1 (by positivity) hc

end Paper09.Percolation
