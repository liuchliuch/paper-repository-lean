/-
Copyright (c) 2026. Prescribed-update censoring for ferromagnetic heat bath.
-/
import Paper09.GibbsShell
import Paper09.Semigroup
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open Finset BigOperators Classical Real Matrix
open scoped Matrix.Norms.Operator

noncomputable section
namespace Paper09
namespace Censoring

variable {V : Type*} [Fintype V]

theorem law_ext {α γ : FinProb (Config V)} (hw : ∀ η, α.w η = γ.w η) : α = γ := by
  cases α with
  | mk aw an as =>
    cases γ with
    | mk bw bn bs =>
      have h : aw = bw := funext hw
      cases h
      rfl

/-- Stochastic order on the actual finite spin laws, tested by every increasing statistic. -/
def StochLE (α γ : FinProb (Config V)) : Prop :=
  ∀ f : Config V → ℝ, Monotone f → α.expect f ≤ γ.expect f

theorem StochLE.refl (α : FinProb (Config V)) : StochLE α α := fun _ _ => le_rfl

theorem StochLE.trans {α γ δ : FinProb (Config V)} (h1 : StochLE α γ) (h2 : StochLE γ δ) :
    StochLE α δ := fun f hf => (h1 f hf).trans (h2 f hf)

private theorem flip_ne (x : V) (η : Config V) : spinFlip x η ≠ η := by
  intro hh
  have h := congrFun hh x
  exact otherSpin_ne (η x) (by simpa using h)

/-- Exact single-site conditional heat-bath kernel under the positive law `p`. -/
def singleSite (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (x : V) (η : Config V) : FinProb (Config V) where
  w ξ := ((if ξ = η then p.w η else 0) +
    (if ξ = spinFlip x η then p.w (spinFlip x η) else 0)) /
      (p.w η + p.w (spinFlip x η))
  nonneg ξ := div_nonneg (add_nonneg
    (by split_ifs; exact p.nonneg _; exact le_rfl)
    (by split_ifs; exact p.nonneg _; exact le_rfl))
    (add_nonneg (p.nonneg _) (p.nonneg _))
  sum_one := by
    classical
    rw [← sum_div, sum_add_distrib]
    simp only [sum_ite_eq', mem_univ, if_true]
    exact div_self (ne_of_gt (add_pos (hp _) (hp _)))

/-- The conditional expectation operator has exactly the binary conditional weights. -/
theorem singleSite_act (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (x : V) (f : Config V → ℝ) (η : Config V) :
    MarkovKernel.act (singleSite p hp x) f η =
      (p.w η * f η + p.w (spinFlip x η) * f (spinFlip x η)) /
        (p.w η + p.w (spinFlip x η)) := by
  classical
  unfold MarkovKernel.act FinProb.expect singleSite
  simp only [div_mul_eq_mul_div]
  rw [← sum_div]
  simp only [add_mul, ite_mul, zero_mul, sum_add_distrib,
    sum_ite_eq', mem_univ, if_true]

theorem singleSite_flip (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (x : V) (η ξ : Config V) :
    (singleSite p hp x (spinFlip x η)).w ξ = (singleSite p hp x η).w ξ := by
  classical
  simp only [singleSite, spinFlip_involutive, add_comm]

theorem singleSite_reversible (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η) (x : V) :
    MarkovKernel.Reversible (singleSite p hp x) p := by
  classical
  intro η ξ
  by_cases h : ξ = η
  · subst ξ; rfl
  by_cases hh : ξ = spinFlip x η
  · subst ξ
    simp only [singleSite, if_neg (flip_ne x η), ite_true, spinFlip_involutive,
      if_neg (Ne.symm (flip_ne x η)), zero_add, add_comm]
    ring
  · have hrev : η ≠ spinFlip x ξ := by
      intro hη
      apply hh
      rw [hη, spinFlip_involutive]
    simp [singleSite, h, hh, Ne.symm h, hrev]

/-- One actual heat-bath update of a law. -/
def update (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (x : V) (α : FinProb (Config V)) : FinProb (Config V) :=
  MarkovKernel.push (singleSite p hp x) α

/-- Density relative to the actual equilibrium law. -/
def density (p α : FinProb (Config V)) (η : Config V) : ℝ := α.w η / p.w η

theorem update_density (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (x : V) (α : FinProb (Config V)) (η : Config V) :
    density p (update p hp x α) η =
      MarkovKernel.act (singleSite p hp x) (density p α) η := by
  unfold density update MarkovKernel.push MarkovKernel.act FinProb.expect
  rw [sum_div]
  apply sum_congr rfl
  intro ξ _
  have hh := singleSite_reversible p hp x η ξ
  field_simp [ne_of_gt (hp η), ne_of_gt (hp ξ)]
  nlinarith only [congrArg (fun z : ℝ => α.w ξ * z) hh]

theorem update_expect (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (x : V) (α : FinProb (Config V)) (f : Config V → ℝ) :
    (update p hp x α).expect f = α.expect (MarkovKernel.act (singleSite p hp x) f) := by
  unfold update MarkovKernel.push MarkovKernel.act FinProb.expect
  simp only [sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro η _
  apply sum_congr rfl
  intro ξ _
  ring

theorem expect_density (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (α : FinProb (Config V)) (f : Config V → ℝ) :
    α.expect f = p.expect (fun η => density p α η * f η) := by
  unfold FinProb.expect density
  apply sum_congr rfl
  intro η _
  field_simp [ne_of_gt (hp η)]

private theorem flip_comparable (x : V) (η : Config V) :
    η ≤ spinFlip x η ∨ spinFlip x η ≤ η := by
  classical
  rcases le_total (η x) (otherSpin (η x)) with h | h
  · left
    intro y
    by_cases hh : y = x
    · subst y; simpa using h
    · simp [spinFlip, hh]
  · right
    intro y
    by_cases hh : y = x
    · subst y; simpa using h
    · simp [spinFlip, hh]

/-- Binary conditional covariance is nonnegative for two increasing statistics. -/
theorem conditional_covariance (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (x : V) (r f : Config V → ℝ) (hr : Monotone r) (hf : Monotone f) :
    p.expect (fun η => r η * MarkovKernel.act (singleSite p hp x) f η) ≤
      p.expect (fun η => r η * f η) := by
  classical
  let c := fun η => conductance p η (spinFlip x η)
  let D := fun η => c η * r η * (f η - f (spinFlip x η))
  have hc (η : Config V) : c (spinFlip x η) = c η := by
    dsimp [c, conductance]
    simp only [spinFlip_involutive, add_comm, mul_comm]
  have hsum : (∑ η, D (spinFlip x η)) = ∑ η, D η :=
    (spinFlipEquiv x).sum_comp D
  have hpoint (η : Config V) : 0 ≤ D η + D (spinFlip x η) := by
    have hprod : 0 ≤ (r η - r (spinFlip x η)) * (f η - f (spinFlip x η)) := by
      rcases flip_comparable x η with h | h
      · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hr h)) (sub_nonpos.mpr (hf h))
      · exact mul_nonneg (sub_nonneg.mpr (hr h)) (sub_nonneg.mpr (hf h))
    have hn := mul_nonneg (conductance_nonneg p η (spinFlip x η)) hprod
    dsimp [D]
    rw [hc, spinFlip_involutive]
    dsimp [c] at *
    nlinarith only [hn]
  have hD : 0 ≤ ∑ η, D η := by
    have hh := sum_nonneg (s := (univ : Finset (Config V))) (fun η _ => hpoint η)
    rw [sum_add_distrib, hsum] at hh
    linarith
  have he : p.expect (fun η => r η * f η) -
      p.expect (fun η => r η * MarkovKernel.act (singleSite p hp x) f η) = ∑ η, D η := by
    unfold FinProb.expect
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro η _
    dsimp only
    rw [singleSite_act]
    dsimp [D, c, conductance]
    field_simp [ne_of_gt (add_pos (hp η) (hp (spinFlip x η)))]
    <;> ring
  linarith

/-- One update moves a law with increasing equilibrium density down in stochastic order. -/
theorem update_le (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (x : V) (α : FinProb (Config V)) (hα : Monotone (density p α)) :
    StochLE (update p hp x α) α := by
  intro f hf
  rw [update_expect, expect_density p hp α, expect_density p hp α f]
  exact conditional_covariance p hp x (density p α) f hα hf

private theorem spinVal_monotone : Monotone spinVal := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> norm_num [spinVal] at *

/-- Ferromagnetism makes the actual local field increasing in the surrounding spins. -/
theorem localField_monotone (Λ : Lattice V) (h : V → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (T : Finset V) (φ : Config V) (x : V) :
    Monotone (fun η => localField Λ h β univ T φ η x) := by
  intro η ξ hηξ
  unfold localField
  apply add_le_add_left
  apply mul_le_mul_of_nonneg_left _ hβ
  apply add_le_add_right
  apply sum_le_sum
  intro y _
  split_ifs
  · exact spinVal_monotone (hηξ y)
  · exact le_rfl

/-- A site's own spin does not enter its conditional local field. -/
theorem localField_update (Λ : Lattice V) (h : V → ℝ) (β : ℝ)
    (T : Finset V) (φ η : Config V) (x : V) (s : Spin) :
    localField Λ h β univ T φ (Function.update η x s) x =
      localField Λ h β univ T φ η x := by
  classical
  unfold localField
  congr 2
  congr 1
  apply sum_congr rfl
  intro y _
  by_cases hh : y = x
  · subst y; simp [Λ.irrefl]
  · simp [hh]

private theorem setSpin_mono {η ξ : Config V} (hηξ : η ≤ ξ) (x : V) (s : Spin) :
    Function.update η x s ≤ Function.update ξ x s := by
  classical
  intro y
  by_cases hh : y = x
  · subst y; simp
  · simpa [hh] using hηξ y

private theorem setSpin_ordered (η : Config V) (x : V) :
    Function.update η x (0 : Spin) ≤ Function.update η x (1 : Spin) := by
  classical
  intro y
  by_cases hh : y = x
  · subst y; simp
  · simp [hh]

private theorem flip_set_zero (η : Config V) (x : V) :
    spinFlip x (Function.update η x 0) = Function.update η x 1 := by
  classical
  simp [spinFlip, otherSpin, Function.update_idem]

/-- The conditional expectation can equivalently be written using the two
specified values at `x`, independently of the incoming value there. -/
theorem singleSite_act_binary (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (x : V) (f : Config V → ℝ) (η : Config V) :
    MarkovKernel.act (singleSite p hp x) f η =
      (p.w (Function.update η x 0) * f (Function.update η x 0) +
        p.w (Function.update η x 1) * f (Function.update η x 1)) /
      (p.w (Function.update η x 0) + p.w (Function.update η x 1)) := by
  classical
  have hs : η x = 0 ∨ η x = 1 := by
    have hh := (η x).isLt
    have hv : (η x).val = 0 ∨ (η x).val = 1 := by omega
    rcases hv with hv | hv
    · exact Or.inl (Fin.ext hv)
    · exact Or.inr (Fin.ext hv)
  rcases hs with hs | hs
  · have he : Function.update η x 0 = η := by
      rw [← hs]
      exact Function.update_eq_self x η
    have hf : spinFlip x η = Function.update η x 1 := by
      rw [← he, flip_set_zero]
      simp [Function.update_idem]
    rw [singleSite_act, he, hf]
  · have he : Function.update η x 1 = η := by
      rw [← hs]
      exact Function.update_eq_self x η
    have hf : spinFlip x η = Function.update η x 0 := by
      simp [spinFlip, hs, otherSpin]
    rw [singleSite_act, he, hf]
    congr 1 <;> ring

def plusProbability (p : FinProb (Config V)) (x : V) (η : Config V) : ℝ :=
  p.w (Function.update η x 1) /
    (p.w (Function.update η x 0) + p.w (Function.update η x 1))

theorem plusProbability_nonneg (p : FinProb (Config V)) (x : V) (η : Config V) :
    0 ≤ plusProbability p x η := by
  exact div_nonneg (p.nonneg _) (add_nonneg (p.nonneg _) (p.nonneg _))

theorem plusProbability_le_one (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (x : V) (η : Config V) : plusProbability p x η ≤ 1 := by
  apply (div_le_one (add_pos (hp _) (hp _))).mpr
  linarith [p.nonneg (Function.update η x 0)]

theorem singleSite_act_mixture (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (x : V) (f : Config V → ℝ) (η : Config V) :
    MarkovKernel.act (singleSite p hp x) f η =
      (1 - plusProbability p x η) * f (Function.update η x 0) +
        plusProbability p x η * f (Function.update η x 1) := by
  rw [singleSite_act_binary]
  unfold plusProbability
  field_simp [ne_of_gt (add_pos (hp (Function.update η x 0)) (hp (Function.update η x 1)))]
  <;> ring

theorem gibbs_positive (Λ : Lattice V) (h : V → ℝ) (β : ℝ)
    (T : Finset V) (φ : Config V) (η : Config V) :
    0 < (gibbs Λ h β univ T φ).w η :=
  div_pos (isingWeight_pos _ _ _ _ _ _ _) (isingZ_pos _ _ _ _ _ _)

/-- The actual conditional probability is the local-field logistic probability. -/
theorem gibbs_plusProbability (Λ : Lattice V) (h : V → ℝ) (β : ℝ)
    (T : Finset V) (φ η : Config V) (x : V) :
    plusProbability (gibbs Λ h β univ T φ) x η =
      Real.exp (2 * localField Λ h β univ T φ η x) /
        (1 + Real.exp (2 * localField Λ h β univ T φ η x)) := by
  classical
  let p := gibbs Λ h β univ T φ
  let E := Real.exp (2 * localField Λ h β univ T φ η x)
  have hr := isingWeight_flip_ratio Λ h β univ T φ (Function.update η x 0) x (mem_univ x)
  rw [flip_set_zero, localField_update] at hr
  norm_num only [Function.update_self, spinVal_zero] at hr
  have hr' : p.w (Function.update η x 1) = p.w (Function.update η x 0) * E := by
    dsimp [p, gibbs, E]
    rw [hr]
    ring
  change p.w (Function.update η x 1) /
    (p.w (Function.update η x 0) + p.w (Function.update η x 1)) = E / (1 + E)
  rw [hr']
  have hp0 : 0 < p.w (Function.update η x 0) := gibbs_positive _ _ _ _ _ _
  have hE : 0 < E := Real.exp_pos _
  field_simp [ne_of_gt hp0, ne_of_gt (by linarith : 0 < 1 + E),
    ne_of_gt (by positivity : 0 < p.w (Function.update η x 0) + p.w (Function.update η x 0) * E)]
  <;> ring

/-- Actual Ising heat-bath conditionals are attractive for `β ≥ 0`. -/
theorem gibbs_plusProbability_monotone (Λ : Lattice V) (h : V → ℝ)
    (β : ℝ) (hβ : 0 ≤ β) (T : Finset V) (φ : Config V) (x : V) :
    Monotone (plusProbability (gibbs Λ h β univ T φ) x) := by
  intro η ξ hηξ
  rw [gibbs_plusProbability, gibbs_plusProbability]
  have hh := localField_monotone Λ h β hβ T φ x hηξ
  have he : Real.exp (2 * localField Λ h β univ T φ η x) ≤
      Real.exp (2 * localField Λ h β univ T φ ξ x) := Real.exp_le_exp.mpr (by linarith)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- Monotonicity of the actual single-site Markov operator follows from the
conditional probabilities and the two ordered update configurations. -/
theorem singleSite_monotone_of_plus (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (x : V) (hq : Monotone (plusProbability p x)) (f : Config V → ℝ) (hf : Monotone f) :
    Monotone (MarkovKernel.act (singleSite p hp x) f) := by
  intro η ξ hηξ
  rw [singleSite_act_mixture, singleSite_act_mixture]
  have h0 := hf (setSpin_mono hηξ x 0)
  have h1 := hf (setSpin_mono hηξ x 1)
  have h01 := hf (setSpin_ordered ξ x)
  have hq0 := plusProbability_nonneg p x η
  have hq1 := plusProbability_le_one p hp x η
  have hqηξ := hq hηξ
  have hA := add_le_add (mul_le_mul_of_nonneg_left h0 (sub_nonneg.mpr hq1))
    (mul_le_mul_of_nonneg_left h1 hq0)
  have hB := mul_nonneg (sub_nonneg.mpr hqηξ) (sub_nonneg.mpr h01)
  nlinarith only [hA, hB]

/-- Applying an attractive update preserves stochastic order of two input laws. -/
theorem update_monotone (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (x : V) (hq : Monotone (plusProbability p x))
    {α γ : FinProb (Config V)} (hαγ : StochLE α γ) :
    StochLE (update p hp x α) (update p hp x γ) := by
  intro f hf
  rw [update_expect, update_expect]
  exact hαγ _ (singleSite_monotone_of_plus p hp x hq f hf)

theorem update_density_monotone (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (x : V) (hq : Monotone (plusProbability p x))
    (α : FinProb (Config V)) (hα : Monotone (density p α)) :
    Monotone (density p (update p hp x α)) := by
  intro η ξ hηξ
  rw [update_density, update_density]
  exact singleSite_monotone_of_plus p hp x hq (density p α) hα hηξ

private theorem expect_neg (p : FinProb (Config V)) (f : Config V → ℝ) :
    p.expect (fun η => -f η) = -p.expect f := by
  simpa only [neg_one_mul] using p.expect_smul (-1) f

private theorem singleSite_act_neg (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (x : V) (f : Config V → ℝ) (η : Config V) :
    MarkovKernel.act (singleSite p hp x) (fun ξ => -f ξ) η =
      -MarkovKernel.act (singleSite p hp x) f η := expect_neg _ f

/-- The order-reversed single-update inequality is proved by the same binary
covariance applied to minus the decreasing density. -/
theorem le_update (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (x : V) (α : FinProb (Config V)) (hα : Antitone (density p α)) :
    StochLE α (update p hp x α) := by
  intro f hf
  rw [update_expect, expect_density p hp α f, expect_density p hp α]
  have hr : Monotone (fun η => -density p α η) :=
    fun η ξ hηξ => neg_le_neg (hα hηξ)
  have hh := conditional_covariance p hp x (fun η => -density p α η) f hr hf
  simp only [neg_mul] at hh
  rw [expect_neg, expect_neg] at hh
  linarith

theorem update_density_antitone (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (x : V) (hq : Monotone (plusProbability p x))
    (α : FinProb (Config V)) (hα : Antitone (density p α)) :
    Antitone (density p (update p hp x α)) := by
  intro η ξ hηξ
  rw [update_density, update_density]
  have hr : Monotone (fun η => -density p α η) :=
    fun η ξ hηξ => neg_le_neg (hα hηξ)
  have hh := singleSite_monotone_of_plus p hp x hq (fun η => -density p α η) hr hηξ
  simp only [singleSite_act_neg] at hh
  linarith

/-- Run the specified update word in its listed chronological order. -/
def run (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η) :
    FinProb (Config V) → List V → FinProb (Config V)
  | α, [] => α
  | α, x :: xs => run p hp (update p hp x α) xs

theorem run_monotone (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (hq : ∀ x, Monotone (plusProbability p x)) (word : List V)
    {α γ : FinProb (Config V)} (hαγ : StochLE α γ) :
    StochLE (run p hp α word) (run p hp γ word) := by
  induction word generalizing α γ with
  | nil => exact hαγ
  | cons x xs ih => exact ih (update_monotone p hp x (hq x) hαγ)

/-- Prescribed subsequence censoring, with the increasing-density invariant
proved at every retained step of the induction. -/
theorem prescribed_censoring_increasing (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (hq : ∀ x, Monotone (plusProbability p x))
    (α : FinProb (Config V)) (hα : Monotone (density p α))
    {censored full : List V} (hsub : censored.Sublist full) :
    StochLE (run p hp α full) (run p hp α censored) := by
  induction hsub generalizing α with
  | slnil => exact StochLE.refl α
  | @cons l₁ l₂ x h ih =>
    exact (run_monotone p hp hq l₂ (update_le p hp x α hα)).trans (ih α hα)
  | @cons₂ l₁ l₂ x h ih =>
    exact ih (update p hp x α) (update_density_monotone p hp x (hq x) α hα)

/-- The complete bottom-start order-reversed prescribed censoring theorem. -/
theorem prescribed_censoring_decreasing (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (hq : ∀ x, Monotone (plusProbability p x))
    (α : FinProb (Config V)) (hα : Antitone (density p α))
    {censored full : List V} (hsub : censored.Sublist full) :
    StochLE (run p hp α censored) (run p hp α full) := by
  induction hsub generalizing α with
  | slnil => exact StochLE.refl α
  | @cons l₁ l₂ x h ih =>
    exact (ih α hα).trans (run_monotone p hp hq l₂ (le_update p hp x α hα))
  | @cons₂ l₁ l₂ x h ih =>
    exact ih (update p hp x α) (update_density_antitone p hp x (hq x) α hα)

/-- Actual deterministic starting law. -/
def dirac (η : Config V) : FinProb (Config V) where
  w ξ := if ξ = η then 1 else 0
  nonneg ξ := by split_ifs <;> norm_num
  sum_one := by
    classical
    simp

@[simp] theorem dirac_expect (η : Config V) (f : Config V → ℝ) :
    (dirac η).expect f = f η := by
  classical
  simp [FinProb.expect, dirac, ite_mul]

theorem top_density_monotone (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η) :
    Monotone (density p (dirac ⊤)) := by
  intro η ξ hηξ
  by_cases hh : η = ⊤
  · have hξ : ξ = ⊤ := top_le_iff.mp (hh ▸ hηξ)
    rw [hh, hξ]
  · simp only [density, dirac, if_neg hh, zero_div]
    exact div_nonneg (by split_ifs <;> norm_num) (p.nonneg ξ)

theorem bottom_density_antitone (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η) :
    Antitone (density p (dirac ⊥)) := by
  intro η ξ hηξ
  by_cases hh : ξ = ⊥
  · have hη : η = ⊥ := le_bot_iff.mp (hh ▸ hηξ)
    rw [hh, hη]
  · simp only [density, dirac, if_neg hh, zero_div]
    exact div_nonneg (by split_ifs <;> norm_num) (p.nonneg η)

/-- Exact prescribed-update form of (3.21), for the actual ferromagnetic
Ising heat-bath kernels, without an assumed censoring inequality. -/
theorem ising_prescribed_censoring (Λ : Lattice V) (h : V → ℝ)
    (β : ℝ) (hβ : 0 ≤ β) (T : Finset V) (φ : Config V)
    {censored full : List V} (hsub : censored.Sublist full) :
    let p := gibbs Λ h β univ T φ
    let hp := gibbs_positive Λ h β T φ
    StochLE (run p hp (dirac ⊥) censored) (run p hp (dirac ⊥) full) ∧
    StochLE (run p hp (dirac ⊥) full) (run p hp (dirac ⊤) full) ∧
    StochLE (run p hp (dirac ⊤) full) (run p hp (dirac ⊤) censored) := by
  dsimp only
  let p := gibbs Λ h β univ T φ
  let hp := gibbs_positive Λ h β T φ
  have hq (x : V) : Monotone (plusProbability p x) :=
    gibbs_plusProbability_monotone Λ h β hβ T φ x
  refine ⟨prescribed_censoring_decreasing p hp hq _ (bottom_density_antitone p hp) hsub,
    ?_, prescribed_censoring_increasing p hp hq _ (top_density_monotone p hp) hsub⟩
  apply run_monotone p hp hq full
  intro f hf
  rw [dirac_expect, dirac_expect]
  exact hf bot_le

/-! Continuous-time retained-site dynamics. -/

/-- Matrix of the actual single-site conditional update. -/
def siteMatrix (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η) (x : V) :
    Matrix (Config V) (Config V) ℝ := fun η ξ => (singleSite p hp x η).w ξ

/-- Sum of the retained site's rate-one clock generators. -/
def siteGenerator (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η) (B : Finset V) :
    Matrix (Config V) (Config V) ℝ := ∑ x ∈ B, (siteMatrix p hp x - 1)

def siteSum (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η) (B : Finset V) :
    Matrix (Config V) (Config V) ℝ := ∑ x ∈ B, siteMatrix p hp x

theorem siteMatrix_mulVec (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (x : V) (f : Config V → ℝ) :
    siteMatrix p hp x *ᵥ f = MarkovKernel.act (singleSite p hp x) f := rfl

theorem siteGenerator_apply (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (B : Finset V) (f : Config V → ℝ) (η : Config V) :
    (siteGenerator p hp B *ᵥ f) η =
      ∑ x ∈ B, (MarkovKernel.act (singleSite p hp x) f η - f η) := by
  classical
  unfold siteGenerator Matrix.mulVec dotProduct
  simp only [Matrix.sum_apply, Matrix.sub_apply, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  simp only [sub_mul, sum_sub_distrib]
  have h1 := congrFun (Matrix.one_mulVec f) η
  change (∑ ξ, siteMatrix p hp x η ξ * f ξ) - ((1 : Matrix (Config V) (Config V) ℝ) *ᵥ f) η = _
  rw [Matrix.one_mulVec]
  rfl

theorem siteGenerator_shift (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η) (B : Finset V) :
    siteGenerator p hp B + (B.card : ℝ) • (1 : Matrix (Config V) (Config V) ℝ) = siteSum p hp B := by
  classical
  simp only [siteGenerator, siteSum, sum_sub_distrib, sum_const, Nat.cast_smul_eq_nsmul,
    sub_add_cancel]

theorem siteGenerator_rows (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (B : Finset V) (η : Config V) : ∑ ξ, siteGenerator p hp B η ξ = 0 := by
  classical
  have hh := siteGenerator_apply p hp B (fun _ => 1) η
  change (∑ ξ, siteGenerator p hp B η ξ * 1) = _ at hh
  simp only [mul_one, MarkovKernel.act, FinProb.expect_const, sub_self, sum_const_zero] at hh
  exact hh

theorem siteGenerator_reversible (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (B : Finset V) (η ξ : Config V) :
    p.w η * siteGenerator p hp B η ξ = p.w ξ * siteGenerator p hp B ξ η := by
  classical
  by_cases hh : η = ξ
  · subst ξ; rfl
  unfold siteGenerator
  simp only [Matrix.sum_apply, Matrix.sub_apply, Matrix.one_apply_ne hh,
    Matrix.one_apply_ne (Ne.symm hh), sub_zero, mul_sum]
  apply sum_congr rfl
  intro x _
  exact singleSite_reversible p hp x η ξ

/-- The actual continuous-time kernel retaining precisely the clocks in `B`. -/
def siteSemigroup (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (B : Finset V) (t : ℝ) : Matrix (Config V) (Config V) ℝ :=
  NormedSpace.exp ℝ (t • siteGenerator p hp B)

@[simp] theorem siteSemigroup_zero (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (B : Finset V) : siteSemigroup p hp B 0 = 1 := by simp [siteSemigroup]

theorem siteSemigroup_add (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (B : Finset V) (s t : ℝ) :
    siteSemigroup p hp B (s + t) = siteSemigroup p hp B s * siteSemigroup p hp B t := by
  classical
  unfold siteSemigroup
  rw [add_smul]
  apply Matrix.exp_add_of_commute
  change (s • siteGenerator p hp B) * (t • siteGenerator p hp B) =
    (t • siteGenerator p hp B) * (s • siteGenerator p hp B)
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm s t]

theorem siteSemigroup_rows (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (B : Finset V) (t : ℝ) (η : Config V) : ∑ ξ, siteSemigroup p hp B t η ξ = 1 := by
  classical
  apply matrix_exp_rows
  intro η
  simp only [Matrix.smul_apply, smul_eq_mul, ← mul_sum, siteGenerator_rows, mul_zero]

theorem siteSemigroup_reversible (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (B : Finset V) (t : ℝ) (η ξ : Config V) :
    p.w η * siteSemigroup p hp B t η ξ = p.w ξ * siteSemigroup p hp B t ξ η := by
  classical
  apply matrix_exp_reversible
  intro a b
  simp only [Matrix.smul_apply, smul_eq_mul]
  calc
    _ = t * (p.w a * siteGenerator p hp B a b) := by ring
    _ = t * (p.w b * siteGenerator p hp B b a) := by rw [siteGenerator_reversible]
    _ = _ := by ring

private theorem siteSemigroup_shift (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (B : Finset V) (t : ℝ) :
    t • siteGenerator p hp B + (t * B.card) • (1 : Matrix (Config V) (Config V) ℝ) =
      t • siteSum p hp B := by
  rw [← smul_smul, ← smul_add, siteGenerator_shift]

theorem siteSemigroup_nonneg (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (B : Finset V) (t : ℝ) (ht : 0 ≤ t) (η ξ : Config V) :
    0 ≤ siteSemigroup p hp B t η ξ := by
  classical
  apply matrix_exp_nonneg_of_shift (t • siteGenerator p hp B) (t * B.card)
  intro a b
  rw [siteSemigroup_shift]
  change 0 ≤ t * (siteSum p hp B a b)
  apply mul_nonneg ht
  simp only [siteSum, Matrix.sum_apply, siteMatrix]
  exact sum_nonneg (fun x _ => (singleSite p hp x a).nonneg b)

/-- Positive exponential-series representation of retained-site evolution. -/
theorem siteSemigroup_factor (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (B : Finset V) (t : ℝ) :
    siteSemigroup p hp B t =
      Real.exp (-(t * B.card)) • NormedSpace.exp ℝ (t • siteSum p hp B) := by
  classical
  have hc : Commute (t • siteGenerator p hp B) ((t * B.card) • (1 : Matrix (Config V) (Config V) ℝ)) := by
    change _ * _ = _ * _
    simp only [Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul, smul_smul, mul_comm]
  have hh := Matrix.exp_add_of_commute ℝ (t • siteGenerator p hp B) ((t * B.card) • 1) hc
  rw [siteSemigroup_shift] at hh
  have he : NormedSpace.exp ℝ ((t * B.card) • (1 : Matrix (Config V) (Config V) ℝ)) =
      Real.exp (t * B.card) • (1 : Matrix (Config V) (Config V) ℝ) := by
    rw [← Algebra.algebraMap_eq_smul_one, ← NormedSpace.algebraMap_exp_comm,
      ← Real.exp_eq_exp_ℝ, Algebra.algebraMap_eq_smul_one]
  rw [he, Matrix.mul_smul, mul_one] at hh
  rw [hh, smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul]
  rfl

private theorem matrix_exp_action_hasSum {A : Type*} [Fintype A] [DecidableEq A]
    (M : Matrix A A ℝ) (f : A → ℝ) (a : A) :
    HasSum (fun n : ℕ => (n.factorial : ℝ)⁻¹ * ((M ^ n) *ᵥ f) a)
      ((NormedSpace.exp ℝ M *ᵥ f) a) := by
  have hh := hasSum_sum (fun b (_ : b ∈ (univ : Finset A)) =>
    (matrix_exp_hasSum M a b).mul_right (f b))
  convert hh using 1
  funext n
  simp only [Matrix.mulVec, dotProduct, mul_sum]
  apply sum_congr rfl
  intro b _
  ring

/-- Exponentiation preserves the cone of increasing functions when the
positive-series generator preserves it. -/
private theorem matrix_exp_monotone {A : Type*} [Fintype A] [DecidableEq A] [Preorder A]
    (M : Matrix A A ℝ) (hM : ∀ f : A → ℝ, Monotone f → Monotone (M *ᵥ f))
    (f : A → ℝ) (hf : Monotone f) : Monotone (NormedSpace.exp ℝ M *ᵥ f) := by
  have hp (n : ℕ) : Monotone (M ^ n *ᵥ f) := by
    induction n with
    | zero => simpa using hf
    | succ n ih => rw [pow_succ', ← Matrix.mulVec_mulVec]; exact hM _ ih
  intro a b hab
  apply hasSum_le _ (matrix_exp_action_hasSum M f a) (matrix_exp_action_hasSum M f b)
  intro n
  exact mul_le_mul_of_nonneg_left (hp n hab) (by positivity)

/-- The actual retained-site continuous-time dynamics is attractive. -/
theorem siteSemigroup_monotone (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (hq : ∀ x, Monotone (plusProbability p x)) (B : Finset V) (t : ℝ) (ht : 0 ≤ t)
    (f : Config V → ℝ) (hf : Monotone f) : Monotone (siteSemigroup p hp B t *ᵥ f) := by
  classical
  have hA : ∀ f : Config V → ℝ, Monotone f → Monotone ((t • siteSum p hp B) *ᵥ f) := by
    intro f hf η ξ hηξ
    simp only [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
    apply mul_le_mul_of_nonneg_left _ ht
    have he (a : Config V) : (siteSum p hp B *ᵥ f) a =
        ∑ x ∈ B, MarkovKernel.act (singleSite p hp x) f a := by
      unfold siteSum Matrix.mulVec dotProduct
      simp only [Matrix.sum_apply, sum_mul]
      rw [sum_comm]
      rfl
    rw [he, he]
    exact sum_le_sum fun x _ => singleSite_monotone_of_plus p hp x (hq x) f hf hηξ
  rw [siteSemigroup_factor, Matrix.smul_mulVec]
  intro η ξ hηξ
  exact mul_le_mul_of_nonneg_left (matrix_exp_monotone _ hA f hf hηξ) (Real.exp_pos _).le

/-- Retained-clock transition laws, extended by time zero for negative inputs. -/
def siteTransition (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (B : Finset V) (t : ℝ) (η : Config V) : FinProb (Config V) where
  w ξ := siteSemigroup p hp B (max t 0) η ξ
  nonneg ξ := siteSemigroup_nonneg p hp B (max t 0) (le_max_right _ _) η ξ
  sum_one := siteSemigroup_rows p hp B (max t 0) η

def evolve (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (B : Finset V) (t : ℝ) (α : FinProb (Config V)) : FinProb (Config V) :=
  MarkovKernel.push (siteTransition p hp B t) α

theorem siteTransition_w (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (B : Finset V) (t : ℝ) (ht : 0 ≤ t) (η ξ : Config V) :
    (siteTransition p hp B t η).w ξ = siteSemigroup p hp B t η ξ := by
  simp [siteTransition, max_eq_left ht]

/-- The backward equation for every actual retained-site semigroup. -/
theorem siteSemigroup_hasDerivAt (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (B : Finset V) (f : Config V → ℝ) (t : ℝ) (η : Config V) :
    HasDerivAt (fun s : ℝ => (siteSemigroup p hp B s *ᵥ f) η)
      ((siteGenerator p hp B *ᵥ (siteSemigroup p hp B t *ᵥ f)) η) t := by
  classical
  have h (ξ : Config V) :=
    (matrix_semigroup_hasDerivAt (siteGenerator p hp B) t η ξ).mul_const (f ξ)
  have hh := HasDerivAt.fun_sum (u := univ) (fun ξ _ => h ξ)
  change HasDerivAt (fun s : ℝ => (siteSemigroup p hp B s *ᵥ f) η)
    (((siteGenerator p hp B * siteSemigroup p hp B t) *ᵥ f) η) t at hh
  simpa only [← Matrix.mulVec_mulVec] using hh

private theorem matrix_weighted_symmetry (p : FinProb (Config V))
    (M : Matrix (Config V) (Config V) ℝ)
    (hM : ∀ η ξ, p.w η * M η ξ = p.w ξ * M ξ η) (f g : Config V → ℝ) :
    p.expect (fun η => (M *ᵥ f) η * g η) =
      p.expect (fun η => f η * (M *ᵥ g) η) := by
  unfold FinProb.expect Matrix.mulVec dotProduct
  simp only [sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro η _
  apply sum_congr rfl
  intro ξ _
  have hh := congrArg (fun z : ℝ => z * (f η * g ξ)) (hM ξ η)
  nlinarith only [hh]

theorem siteGenerator_selfadjoint (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (B : Finset V) (f g : Config V → ℝ) :
    p.expect (fun η => (siteGenerator p hp B *ᵥ f) η * g η) =
      p.expect (fun η => f η * (siteGenerator p hp B *ᵥ g) η) :=
  matrix_weighted_symmetry p _ (siteGenerator_reversible p hp B) f g

theorem siteSemigroup_selfadjoint (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (B : Finset V) (t : ℝ) (f g : Config V → ℝ) :
    p.expect (fun η => (siteSemigroup p hp B t *ᵥ f) η * g η) =
      p.expect (fun η => f η * (siteSemigroup p hp B t *ᵥ g) η) :=
  matrix_weighted_symmetry p _ (siteSemigroup_reversible p hp B t) f g

/-- The exact derivative comparison after deleting a set of site clocks. -/
theorem generator_subset_covariance (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (B A : Finset V) (hBA : B ⊆ A) (r f : Config V → ℝ)
    (hr : Monotone r) (hf : Monotone f) :
    p.expect (fun η => r η * (siteGenerator p hp A *ᵥ f) η) -
      p.expect (fun η => r η * (siteGenerator p hp B *ᵥ f) η) ≤ 0 := by
  classical
  let c := fun x : V => p.expect (fun η => r η * MarkovKernel.act (singleSite p hp x) f η) -
    p.expect (fun η => r η * f η)
  have hnonpos (x : V) : c x ≤ 0 := sub_nonpos.mpr (conditional_covariance p hp x r f hr hf)
  have hsum (D : Finset V) : p.expect (fun η => r η * (siteGenerator p hp D *ᵥ f) η) = ∑ x ∈ D, c x := by
    simp only [siteGenerator_apply]
    unfold FinProb.expect
    simp only [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro x _
    dsimp [c]
    unfold FinProb.expect
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro η _
    ring
  rw [hsum A, hsum B, ← sum_sdiff hBA]
  have hh : ∑ x ∈ A \ B, c x ≤ 0 := sum_nonpos fun x _ => hnonpos x
  linarith

/-- Continuous-time censoring proved by interpolating the two actual matrix
exponentials. Positive exponential series preserve both increasing cones;
binary conditional covariance supplies the derivative's sign. -/
theorem siteSemigroup_censoring_bilinear (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (hq : ∀ x, Monotone (plusProbability p x)) (B A : Finset V) (hBA : B ⊆ A)
    (t : ℝ) (ht : 0 ≤ t) (r f : Config V → ℝ) (hr : Monotone r) (hf : Monotone f) :
    p.expect (fun η => r η * (siteSemigroup p hp A t *ᵥ f) η) ≤
      p.expect (fun η => r η * (siteSemigroup p hp B t *ᵥ f) η) := by
  let u := fun s : ℝ => siteSemigroup p hp A s *ᵥ r
  let v := fun s : ℝ => siteSemigroup p hp B (t - s) *ᵥ f
  let H := fun s : ℝ => p.expect (fun η => u s η * v s η)
  let D := fun s : ℝ =>
    p.expect (fun η => (siteGenerator p hp A *ᵥ u s) η * v s η) -
      p.expect (fun η => u s η * (siteGenerator p hp B *ᵥ v s) η)
  have hd (s : ℝ) : HasDerivAt H (D s) s := by
    have hu (η : Config V) := siteSemigroup_hasDerivAt p hp A r s η
    have hv (η : Config V) := (siteSemigroup_hasDerivAt p hp B f (t-s) η).comp s
      ((hasDerivAt_id s).const_sub t)
    have hh := HasDerivAt.fun_sum (u := univ) (fun η _ =>
      (((hu η).mul (hv η)).const_mul (p.w η)))
    convert hh using 1
    unfold D FinProb.expect
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro η _
    dsimp [u, v]
    ring
  have hsign (s : ℝ) (hs : s ∈ Set.Icc 0 t) : D s ≤ 0 := by
    dsimp [D]
    rw [siteGenerator_selfadjoint]
    exact generator_subset_covariance p hp B A hBA (u s) (v s)
      (siteSemigroup_monotone p hp hq A s hs.1 r hr)
      (siteSemigroup_monotone p hp hq B (t-s) (sub_nonneg.mpr hs.2) f hf)
  have hdiff : Differentiable ℝ H := fun s => (hd s).differentiableAt
  have hmono : AntitoneOn H (Set.Icc 0 t) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 t)
    · exact hdiff.continuous.continuousOn
    · exact hdiff.differentiableOn
    · intro s hs
      rw [(hd s).deriv]
      exact hsign s (interior_subset hs)
  have hh := hmono ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
  dsimp [H, u, v] at hh
  simp only [siteSemigroup_zero, Matrix.one_mulVec, sub_self, sub_zero] at hh
  rw [siteSemigroup_selfadjoint] at hh
  exact hh

theorem evolve_expect (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (B : Finset V) (t : ℝ) (ht : 0 ≤ t) (α : FinProb (Config V)) (f : Config V → ℝ) :
    (evolve p hp B t α).expect f = α.expect (siteSemigroup p hp B t *ᵥ f) := by
  unfold evolve MarkovKernel.push FinProb.expect Matrix.mulVec dotProduct
  simp only [sum_mul, mul_sum, siteTransition_w p hp B t ht]
  rw [sum_comm]
  apply sum_congr rfl
  intro η _
  apply sum_congr rfl
  intro ξ _
  ring

theorem evolve_density (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (B : Finset V) (t : ℝ) (ht : 0 ≤ t) (α : FinProb (Config V)) :
    density p (evolve p hp B t α) = siteSemigroup p hp B t *ᵥ density p α := by
  funext η
  unfold density evolve MarkovKernel.push Matrix.mulVec dotProduct
  rw [sum_div]
  apply sum_congr rfl
  intro ξ _
  rw [siteTransition_w p hp B t ht]
  have hh := siteSemigroup_reversible p hp B t η ξ
  field_simp [ne_of_gt (hp η), ne_of_gt (hp ξ)]
  nlinarith only [congrArg (fun z : ℝ => α.w ξ * z) hh]

theorem evolve_density_monotone (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (hq : ∀ x, Monotone (plusProbability p x)) (B : Finset V) (t : ℝ) (ht : 0 ≤ t)
    (α : FinProb (Config V)) (hα : Monotone (density p α)) :
    Monotone (density p (evolve p hp B t α)) := by
  rw [evolve_density p hp B t ht]
  exact siteSemigroup_monotone p hp hq B t ht _ hα

theorem evolve_density_antitone (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (hq : ∀ x, Monotone (plusProbability p x)) (B : Finset V) (t : ℝ) (ht : 0 ≤ t)
    (α : FinProb (Config V)) (hα : Antitone (density p α)) :
    Antitone (density p (evolve p hp B t α)) := by
  rw [evolve_density p hp B t ht]
  have hneg : Monotone (fun η => -density p α η) := fun η ξ hηξ => neg_le_neg (hα hηξ)
  have hh := siteSemigroup_monotone p hp hq B t ht _ hneg
  intro η ξ hηξ
  have he := hh hηξ
  have hlin : siteSemigroup p hp B t *ᵥ (fun η => -density p α η) =
      fun η => -(siteSemigroup p hp B t *ᵥ density p α) η := by
    simpa only [Pi.neg_apply] using Matrix.mulVec_neg (density p α) (siteSemigroup p hp B t)
  rw [hlin] at he
  linarith

theorem evolve_monotone (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (hq : ∀ x, Monotone (plusProbability p x)) (B : Finset V) (t : ℝ) (ht : 0 ≤ t)
    {α γ : FinProb (Config V)} (hαγ : StochLE α γ) :
    StochLE (evolve p hp B t α) (evolve p hp B t γ) := by
  intro f hf
  rw [evolve_expect p hp B t ht, evolve_expect p hp B t ht]
  exact hαγ _ (siteSemigroup_monotone p hp hq B t ht f hf)

/-- Actual continuous-time deletion of clocks moves an increasing-density law
upward in stochastic order. -/
theorem evolve_censoring_increasing (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (hq : ∀ x, Monotone (plusProbability p x)) (B A : Finset V) (hBA : B ⊆ A)
    (t : ℝ) (ht : 0 ≤ t) (α : FinProb (Config V)) (hα : Monotone (density p α)) :
    StochLE (evolve p hp A t α) (evolve p hp B t α) := by
  intro f hf
  rw [evolve_expect p hp A t ht, evolve_expect p hp B t ht,
    expect_density p hp α, expect_density p hp α]
  exact siteSemigroup_censoring_bilinear p hp hq B A hBA t ht _ f hα hf

theorem evolve_censoring_decreasing (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (hq : ∀ x, Monotone (plusProbability p x)) (B A : Finset V) (hBA : B ⊆ A)
    (t : ℝ) (ht : 0 ≤ t) (α : FinProb (Config V)) (hα : Antitone (density p α)) :
    StochLE (evolve p hp B t α) (evolve p hp A t α) := by
  intro f hf
  rw [evolve_expect p hp A t ht, evolve_expect p hp B t ht,
    expect_density p hp α, expect_density p hp α]
  have hneg : Monotone (fun η => -density p α η) := fun η ξ hηξ => neg_le_neg (hα hηξ)
  have hh := siteSemigroup_censoring_bilinear p hp hq B A hBA t ht _ f hneg hf
  simp only [neg_mul] at hh
  rw [expect_neg, expect_neg] at hh
  linarith

private theorem oneSite_flip (η : Config V) (x : V) : oneSite η (spinFlip x η) := by
  refine ⟨x, ?_, ?_⟩
  · simpa only [spinFlip_self] using (otherSpin_ne (η x)).symm
  · intro y hy
    simp [spinFlip, hy]

private theorem oneSite_eq_flip {η ξ : Config V} (hh : oneSite η ξ) :
    ∃ x, ξ = spinFlip x η := by
  classical
  obtain ⟨x, hx, hrest⟩ := hh
  refine ⟨x, ?_⟩
  have hs : ξ x = otherSpin (η x) := by
    generalize η x = a at *
    generalize ξ x = b at *
    fin_cases a <;> fin_cases b <;> norm_num [otherSpin] at *
  funext y
  by_cases hy : y = x
  · subst y; simpa only [spinFlip_self] using hs
  · simpa [spinFlip, hy] using (hrest y hy).symm

private theorem spinFlip_site_injective (η : Config V) : Function.Injective (fun x : V => spinFlip x η) := by
  classical
  intro x y hh
  by_contra hxy
  have he := congrFun hh x
  simp only [spinFlip_self, spinFlip_of_ne hxy] at he
  exact otherSpin_ne (η x) he

/-- Summing the actual rate-one single-site clock generators gives exactly the
previously constructed heat-bath generator matrix. -/
theorem siteGenerator_univ (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η) :
    siteGenerator p hp univ = heatBathMatrix p := by
  classical
  have hact (f : Config V → ℝ) : siteGenerator p hp univ *ᵥ f = heatBathGenerator p f := by
    funext η
    rw [siteGenerator_apply]
    let g := fun ξ : Config V => heatBathRate p η ξ * (f ξ - f η)
    have hterm (x : V) : MarkovKernel.act (singleSite p hp x) f η - f η = g (spinFlip x η) := by
      rw [singleSite_act]
      dsimp [g, heatBathRate]
      rw [if_pos (oneSite_flip η x)]
      field_simp [ne_of_gt (add_pos (hp η) (hp (spinFlip x η)))]
      <;> ring
    simp only [hterm]
    change (∑ x : V, g (spinFlip x η)) = ∑ ξ : Config V, g ξ
    rw [← sum_image (fun x _ y _ h => spinFlip_site_injective η h)]
    apply sum_subset (subset_univ _)
    intro ξ _ hξ
    by_cases hh : oneSite η ξ
    · obtain ⟨x, rfl⟩ := oneSite_eq_flip hh
      exact False.elim (hξ (mem_image.mpr ⟨x, mem_univ x, rfl⟩))
    · simp [g, heatBathRate, hh]
  apply Matrix.ext_of_mulVec_single
  intro ξ
  rw [hact, heatBathMatrix_mulVec]

theorem siteSemigroup_univ (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η) (t : ℝ) :
    siteSemigroup p hp univ t = heatBathSemigroup p t := by
  simp only [siteSemigroup, siteGenerator_univ, heatBathSemigroup]

theorem siteTransition_univ (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η) (t : ℝ) (η : Config V) :
    siteTransition p hp univ t η = heatBathTransition p t η := by
  apply law_ext
  intro ξ
  exact congrArg (fun M : Matrix (Config V) (Config V) ℝ => M η ξ) (siteSemigroup_univ p hp (max t 0))

theorem evolve_add (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (B : Finset V) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (α : FinProb (Config V)) :
    evolve p hp B t (evolve p hp B s α) = evolve p hp B (s + t) α := by
  apply law_ext
  intro ξ
  unfold evolve MarkovKernel.push
  simp only [siteTransition_w p hp B t ht, siteTransition_w p hp B s hs,
    siteTransition_w p hp B (s+t) (add_nonneg hs ht), siteSemigroup_add,
    Matrix.mul_apply, sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro η _
  apply sum_congr rfl
  intro ζ _
  ring

@[simp] theorem evolve_zero (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (B : Finset V) (α : FinProb (Config V)) : evolve p hp B 0 α = α := by
  apply law_ext
  intro η
  unfold evolve MarkovKernel.push
  simp only [siteTransition_w p hp B 0 le_rfl, siteSemigroup_zero, Matrix.one_apply]
  simp

/-- Finite averaging over independent external schedule choices. -/
def mix {Ω : Type*} [Fintype Ω] (q : FinProb Ω)
    (family : Ω → FinProb (Config V)) : FinProb (Config V) where
  w η := ∑ ω, q.w ω * (family ω).w η
  nonneg η := sum_nonneg fun ω _ => mul_nonneg (q.nonneg ω) ((family ω).nonneg η)
  sum_one := by
    rw [sum_comm]
    simp only [← mul_sum, FinProb.sum_one, mul_one]

theorem mix_expect {Ω : Type*} [Fintype Ω] (q : FinProb Ω)
    (family : Ω → FinProb (Config V)) (f : Config V → ℝ) :
    (mix q family).expect f = ∑ ω, q.w ω * (family ω).expect f := by
  unfold mix FinProb.expect
  simp only [sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro ω _
  apply sum_congr rfl
  intro η _
  ring

theorem mix_const {Ω : Type*} [Fintype Ω] (q : FinProb Ω) (α : FinProb (Config V)) :
    mix q (fun _ => α) = α := by
  apply law_ext
  intro η
  change (∑ ω, q.w ω * α.w η) = α.w η
  rw [← sum_mul, q.sum_one, one_mul]

theorem mix_order {Ω : Type*} [Fintype Ω] (q : FinProb Ω)
    (α γ : Ω → FinProb (Config V)) (hαγ : ∀ ω, StochLE (α ω) (γ ω)) :
    StochLE (mix q α) (mix q γ) := by
  intro f hf
  rw [mix_expect, mix_expect]
  exact sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hαγ ω f hf) (q.nonneg ω)

theorem mix_density_monotone {Ω : Type*} [Fintype Ω] (q : FinProb Ω)
    (p : FinProb (Config V)) (family : Ω → FinProb (Config V))
    (hf : ∀ ω, Monotone (density p (family ω))) : Monotone (density p (mix q family)) := by
  intro η ξ hηξ
  unfold density mix
  rw [sum_div, sum_div]
  apply sum_le_sum
  intro ω _
  have hh := mul_le_mul_of_nonneg_left (hf ω hηξ) (q.nonneg ω)
  simpa only [density, mul_div_assoc] using hh

theorem mix_density_antitone {Ω : Type*} [Fintype Ω] (q : FinProb Ω)
    (p : FinProb (Config V)) (family : Ω → FinProb (Config V))
    (hf : ∀ ω, Antitone (density p (family ω))) : Antitone (density p (mix q family)) := by
  intro η ξ hηξ
  unfold density mix
  rw [sum_div, sum_div]
  apply sum_le_sum
  intro ω _
  have hh := mul_le_mul_of_nonneg_left (hf ω hηξ) (q.nonneg ω)
  simpa only [density, mul_div_assoc] using hh

/-- A stage chooses a retained clock set independently of the spin updates. -/
def colorStep {Ω : Type*} [Fintype Ω] (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (q : FinProb Ω) (blocks : Ω → Finset V) (t : ℝ) (α : FinProb (Config V)) : FinProb (Config V) :=
  mix q (fun ω => evolve p hp (blocks ω) t α)

def colorKernel {Ω : Type*} [Fintype Ω] (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (q : FinProb Ω) (blocks : Ω → Finset V) (t : ℝ) (η : Config V) : FinProb (Config V) :=
  mix q (fun ω => siteTransition p hp (blocks ω) t η)

theorem colorStep_kernel {Ω : Type*} [Fintype Ω] (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (q : FinProb Ω) (blocks : Ω → Finset V) (t : ℝ) (α : FinProb (Config V)) :
    colorStep p hp q blocks t α = MarkovKernel.push (colorKernel p hp q blocks t) α := by
  apply law_ext
  intro η
  unfold colorStep mix colorKernel evolve MarkovKernel.push
  simp only [mix, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro ω _
  apply sum_congr rfl
  intro ξ _
  ring

theorem colorStep_monotone {Ω : Type*} [Fintype Ω] (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (hq : ∀ x, Monotone (plusProbability p x)) (q : FinProb Ω) (blocks : Ω → Finset V)
    (t : ℝ) (ht : 0 ≤ t) {α γ : FinProb (Config V)} (hαγ : StochLE α γ) :
    StochLE (colorStep p hp q blocks t α) (colorStep p hp q blocks t γ) :=
  mix_order q _ _ (fun ω => evolve_monotone p hp hq (blocks ω) t ht hαγ)

theorem colorStep_censoring_increasing {Ω : Type*} [Fintype Ω] (p : FinProb (Config V))
    (hp : ∀ η, 0 < p.w η) (hq : ∀ x, Monotone (plusProbability p x))
    (q : FinProb Ω) (blocks : Ω → Finset V) (t : ℝ) (ht : 0 ≤ t)
    (α : FinProb (Config V)) (hα : Monotone (density p α)) :
    StochLE (evolve p hp univ t α) (colorStep p hp q blocks t α) := by
  rw [← mix_const q (evolve p hp univ t α)]
  exact mix_order q _ _ (fun ω =>
    evolve_censoring_increasing p hp hq (blocks ω) univ (subset_univ _) t ht α hα)

theorem colorStep_censoring_decreasing {Ω : Type*} [Fintype Ω] (p : FinProb (Config V))
    (hp : ∀ η, 0 < p.w η) (hq : ∀ x, Monotone (plusProbability p x))
    (q : FinProb Ω) (blocks : Ω → Finset V) (t : ℝ) (ht : 0 ≤ t)
    (α : FinProb (Config V)) (hα : Antitone (density p α)) :
    StochLE (colorStep p hp q blocks t α) (evolve p hp univ t α) := by
  rw [← mix_const q (evolve p hp univ t α)]
  exact mix_order q _ _ (fun ω =>
    evolve_censoring_decreasing p hp hq (blocks ω) univ (subset_univ _) t ht α hα)

/-- Actual iterated independently chosen retained-clock stages. -/
def colorRun {Ω : Type*} [Fintype Ω] (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (q : FinProb Ω) (blocks : Ω → Finset V) (t : ℝ) (α : FinProb (Config V)) : ℕ → FinProb (Config V)
  | 0 => α
  | k + 1 => colorStep p hp q blocks t (colorRun p hp q blocks t α k)

theorem colorRun_monotone {Ω : Type*} [Fintype Ω] (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (hq : ∀ x, Monotone (plusProbability p x)) (q : FinProb Ω) (blocks : Ω → Finset V)
    (t : ℝ) (ht : 0 ≤ t) {α γ : FinProb (Config V)} (hαγ : StochLE α γ) (k : ℕ) :
    StochLE (colorRun p hp q blocks t α k) (colorRun p hp q blocks t γ k) := by
  induction k with
  | zero => exact hαγ
  | succ k ih => exact colorStep_monotone p hp hq q blocks t ht ih

theorem colorRun_censoring_increasing {Ω : Type*} [Fintype Ω] (p : FinProb (Config V))
    (hp : ∀ η, 0 < p.w η) (hq : ∀ x, Monotone (plusProbability p x))
    (q : FinProb Ω) (blocks : Ω → Finset V) (t : ℝ) (ht : 0 ≤ t)
    (α : FinProb (Config V)) (hα : Monotone (density p α)) (k : ℕ) :
    StochLE (evolve p hp univ ((k : ℝ) * t) α) (colorRun p hp q blocks t α k) := by
  induction k with
  | zero => simpa [colorRun] using StochLE.refl α
  | succ k ih =>
    have hkt : 0 ≤ (k : ℝ) * t := mul_nonneg (Nat.cast_nonneg _) ht
    have hden := evolve_density_monotone p hp hq univ ((k : ℝ)*t) hkt α hα
    have hh := (colorStep_censoring_increasing p hp hq q blocks t ht _ hden).trans
      (colorStep_monotone p hp hq q blocks t ht ih)
    rw [evolve_add p hp univ ((k : ℝ)*t) t hkt ht] at hh
    simpa only [colorRun, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hh

theorem colorRun_censoring_decreasing {Ω : Type*} [Fintype Ω] (p : FinProb (Config V))
    (hp : ∀ η, 0 < p.w η) (hq : ∀ x, Monotone (plusProbability p x))
    (q : FinProb Ω) (blocks : Ω → Finset V) (t : ℝ) (ht : 0 ≤ t)
    (α : FinProb (Config V)) (hα : Antitone (density p α)) (k : ℕ) :
    StochLE (colorRun p hp q blocks t α k) (evolve p hp univ ((k : ℝ) * t) α) := by
  induction k with
  | zero => simpa [colorRun] using StochLE.refl α
  | succ k ih =>
    have hkt : 0 ≤ (k : ℝ) * t := mul_nonneg (Nat.cast_nonneg _) ht
    have hden := evolve_density_antitone p hp hq univ ((k : ℝ)*t) hkt α hα
    have hh := (colorStep_monotone p hp hq q blocks t ht ih).trans
      (colorStep_censoring_decreasing p hp hq q blocks t ht _ hden)
    rw [evolve_add p hp univ ((k : ℝ)*t) t hkt ht] at hh
    simpa only [colorRun, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hh

/-- Source (3.21) after averaging independent color choices and evolving the
actual retained-clock semigroups. All three stochastic inequalities are proved. -/
theorem ising_ct_censoring_colors {Ω : Type*} [Fintype Ω]
    (Λ : Lattice V) (h : V → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (T : Finset V) (φ : Config V) (q : FinProb Ω) (blocks : Ω → Finset V)
    (t : ℝ) (ht : 0 ≤ t) (k : ℕ) :
    let p := gibbs Λ h β univ T φ
    let hp := gibbs_positive Λ h β T φ
    StochLE (colorRun p hp q blocks t (dirac ⊥) k)
      (heatBathTransition p ((k : ℝ)*t) ⊥) ∧
    StochLE (heatBathTransition p ((k : ℝ)*t) ⊥)
      (heatBathTransition p ((k : ℝ)*t) ⊤) ∧
    StochLE (heatBathTransition p ((k : ℝ)*t) ⊤)
      (colorRun p hp q blocks t (dirac ⊤) k) := by
  dsimp only
  let p := gibbs Λ h β univ T φ
  let hp := gibbs_positive Λ h β T φ
  have hq (x : V) : Monotone (plusProbability p x) := gibbs_plusProbability_monotone Λ h β hβ T φ x
  have he (η : Config V) : evolve p hp univ ((k : ℝ)*t) (dirac η) =
      heatBathTransition p ((k : ℝ)*t) η := by
    apply law_ext
    intro ξ
    unfold evolve MarkovKernel.push dirac
    simp only [ite_mul, zero_mul, sum_ite_eq', mem_univ, if_true, one_mul]
    exact congrArg (fun law : FinProb (Config V) => law.w ξ) (siteTransition_univ p hp ((k : ℝ)*t) η)
  refine ⟨?_, ?_, ?_⟩
  · rw [← he ⊥]
    exact colorRun_censoring_decreasing p hp hq q blocks t ht _ (bottom_density_antitone p hp) k
  · rw [← he ⊥, ← he ⊤]
    apply evolve_monotone p hp hq univ ((k : ℝ)*t) (mul_nonneg (Nat.cast_nonneg _) ht)
    intro f hf
    rw [dirac_expect, dirac_expect]
    exact hf bot_le
  · rw [← he ⊤]
    exact colorRun_censoring_increasing p hp hq q blocks t ht _ (top_density_monotone p hp) k

end Censoring
end Paper09
