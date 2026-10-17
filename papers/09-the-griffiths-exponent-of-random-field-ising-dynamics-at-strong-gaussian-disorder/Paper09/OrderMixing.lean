/-
Copyright (c) 2026. Finite stochastic-order bounds for worst-start mixing.
These estimates use actual event masses and do not assume a monotone-coupling
existence theorem.
-/
import Paper09.Coupling
import Paper09.Markov

open Finset BigOperators Classical Real
noncomputable section
namespace Paper09.OrderMixing
variable {V : Type*} [Fintype V]

/-- The number of plus spins. -/
def rankNat (η : Config V) : ℕ := ∑ x, (η x).val

def rank (η : Config V) : ℝ := rankNat η

theorem rankNat_strict {η ξ : Config V} (hle : η ≤ ξ) (hne : η ≠ ξ) :
    rankNat η < rankNat ξ := by
  have hex : ∃ x, η x ≠ ξ x := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  obtain ⟨x,hx⟩ := hex
  apply Finset.sum_lt_sum
  · intro y _
    exact hle y
  · exact ⟨x,mem_univ _,lt_of_le_of_ne (hle x) (fun hv => hx (Fin.ext hv))⟩

theorem rank_monotone : Monotone (rank (V := V)) := by
  intro η ξ h
  change (rankNat η : ℝ) ≤ (rankNat ξ : ℝ)
  exact_mod_cast (Finset.sum_le_sum (fun x _ => h x) : rankNat η ≤ rankNat ξ)

/-- Adding the plus-spin rank makes any `[0,1]` statistic increasing. -/
theorem rank_add_monotone (f : Config V → ℝ) (hf0 : ∀ η, 0 ≤ f η)
    (hf1 : ∀ η, f η ≤ 1) : Monotone (fun η => rank η + f η) := by
  intro η ξ hle
  by_cases heq : η = ξ
  · subst ξ; exact le_rfl
  · have hnat : rankNat η + 1 ≤ rankNat ξ := rankNat_strict hle heq
    have hr : rank η + 1 ≤ rank ξ := by
      change (rankNat η : ℝ) + 1 ≤ (rankNat ξ : ℝ)
      exact_mod_cast hnat
    linarith [hf0 ξ,hf1 η]

/-- Stochastic comparison tested by increasing real statistics. This is the
same dual order used by the actual censoring construction. -/
def StochLE (p q : FinProb (Config V)) : Prop :=
  ∀ f : Config V → ℝ, Monotone f → p.expect f ≤ q.expect f

/-- Total variation is the mass excess on the actual positive-difference set. -/
theorem tvDist_positive_event (p q : FinProb (Config V)) :
    tvDist p q = p.expect (fun η => if q.w η ≤ p.w η then 1 else 0) -
      q.expect (fun η => if q.w η ≤ p.w η then 1 else 0) := by
  have habs (η : Config V) : |p.w η-q.w η| =
      2 * ((p.w η-q.w η) * (if q.w η ≤ p.w η then 1 else 0)) - (p.w η-q.w η) := by
    by_cases h : q.w η ≤ p.w η
    · rw [if_pos h,abs_of_nonneg (sub_nonneg.mpr h)]; ring
    · rw [if_neg h,abs_of_neg (sub_neg.mpr (lt_of_not_ge h))]; ring
  unfold tvDist FinProb.expect
  simp_rw [habs]
  rw [sum_sub_distrib, ← mul_sum, sum_sub_distrib, p.sum_one,q.sum_one]
  simp only [sub_self, sub_zero]
  rw [← sum_sub_distrib]
  simp_rw [← sub_mul]
  ring

/-- For ordered laws, total variation is at most the increase in the expected
number of plus spins. Every premise concerns actual finite probability laws. -/
theorem tvDist_le_rank_gap (p q : FinProb (Config V)) (hpq : StochLE p q) :
    tvDist p q ≤ q.expect rank - p.expect rank := by
  let f : Config V → ℝ := fun η => if q.w η ≤ p.w η then 1 else 0
  have hf0 : ∀ η, 0 ≤ f η := by intro η; dsimp [f]; split_ifs <;> norm_num
  have hf1 : ∀ η, f η ≤ 1 := by intro η; dsimp [f]; split_ifs <;> norm_num
  have hh := hpq (fun η => rank η + f η) (rank_add_monotone f hf0 hf1)
  rw [FinProb.expect_add,FinProb.expect_add] at hh
  rw [tvDist_positive_event]
  change p.expect f - q.expect f ≤ _
  linarith

/-- Any two laws between common stochastic extremes have small TV distance
when the extreme expected-coordinate gap is small. -/
theorem tvDist_le_of_sandwich (l u p q : FinProb (Config V))
    (hlp : StochLE l p) (hpu : StochLE p u)
    (hlq : StochLE l q) (hqu : StochLE q u) :
    tvDist p q ≤ 2 * (u.expect rank - l.expect rank) := by
  have hp := tvDist_le_rank_gap l p hlp
  have hq := tvDist_le_rank_gap l q hlq
  have hpr := hpu rank rank_monotone
  have hqr := hqu rank rank_monotone
  have ht := tvDist_triangle p l q
  rw [tvDist_comm p l] at ht
  linarith

/-- The rank difference equals the expected-spin expression in (3.22). -/
theorem rank_gap_eq_spin_difference (p q : FinProb (Config V)) :
    q.expect rank - p.expect rank = spinExpectationDifference p q := by
  have hspin (s : Spin) : spinVal s = 2*(s.val : ℝ)-1 := by
    fin_cases s <;> norm_num [spinVal]
  have he (η : Config V) : rank η =
      (1/2:ℝ)*(∑ x, spinVal (η x)) + (Fintype.card V : ℝ)/2 := by
    simp only [rank,rankNat,Nat.cast_sum,hspin,sum_sub_distrib,← mul_sum]
    simp only [sum_const, card_univ, nsmul_eq_mul, mul_one]
    ring
  unfold spinExpectationDifference
  change q.expect (fun η => rank η) - p.expect (fun η => rank η) = _
  simp_rw [he,FinProb.expect_add,FinProb.expect_const,FinProb.expect_smul]
  have hsum (r : FinProb (Config V)) :
      r.expect (fun η => ∑ x, spinVal (η x)) = ∑ x, r.expect (fun η => spinVal (η x)) := by
    unfold FinProb.expect
    simp only [mul_sum]
    rw [sum_comm]
  rw [hsum,hsum,Finset.sum_sub_distrib]
  ring

/-- The extremal Wasserstein estimate controls every pair sandwiched between
these laws, without an unproved transport/order equivalence. -/
theorem tvDist_le_extremal_transport (l u p q : FinProb (Config V))
    (hlp : StochLE l p) (hpu : StochLE p u)
    (hlq : StochLE l q) (hqu : StochLE q u) :
    tvDist p q ≤ 2 * hammingWasserstein l u := by
  apply (tvDist_le_of_sandwich l u p q hlp hpu hlq hqu).trans
  rw [rank_gap_eq_spin_difference]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Wasserstein.lower_bound spinExpectationDifference_le_cost

/-- Iterated expectation for the actual kernel action. -/
theorem expect_bind (p : FinProb (Config V)) (K : Config V → FinProb (Config V))
    (f : Config V → ℝ) : (p.bind K).expect f = p.expect (fun η => (K η).expect f) := by
  unfold FinProb.expect FinProb.bind
  simp only [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro η _
  rw [mul_sum]
  apply sum_congr rfl
  intro ξ _
  ring

/-- Stochastic bounds pass through actual mixtures, including the stationary
mixture of all possible initial configurations. -/
theorem mixture_sandwich (K : Config V → FinProb (Config V)) (p l u : FinProb (Config V))
    (hl : ∀ η, StochLE l (K η)) (hu : ∀ η, StochLE (K η) u) :
    StochLE l (p.bind K) ∧ StochLE (p.bind K) u := by
  constructor
  · intro f hf
    rw [expect_bind]
    calc l.expect f = p.expect (fun _ => l.expect f) := (p.expect_const _).symm
      _ ≤ _ := FinProb.expect_mono (fun η => hl η f hf)
  · intro f hf
    rw [expect_bind]
    calc p.expect (fun η => (K η).expect f) ≤ p.expect (fun _ => u.expect f) :=
          FinProb.expect_mono (fun η => hu η f hf)
      _ = _ := p.expect_const _

/-- A censored extreme pair controls the actual worst-initial-state distance
of any attractive stationary kernel. The premise is precisely the stochastic
sandwich supplied by censoring; its consequence uses actual TV masses. -/
theorem worst_start_tv_from_censoring
    (K : Config V → FinProb (Config V)) (p l u : FinProb (Config V))
    (hstationary : p.bind K = p)
    (hattractive : ∀ η ξ, η ≤ ξ → StochLE (K η) (K ξ))
    (hl : StochLE l (K (fun _ => 0))) (hu : StochLE (K (fun _ => 1)) u) :
    ∀ η, tvDist (K η) p ≤ 2 * hammingWasserstein l u := by
  have hbottom (η : Config V) : (fun _ => (0 : Spin)) ≤ η := fun x => Nat.zero_le _
  have htop (η : Config V) : η ≤ (fun _ => (1 : Spin)) := by
    intro x
    have hh := (η x).isLt
    change (η x).val ≤ 1
    omega
  have hlall : ∀ η, StochLE l (K η) := by
    intro η f hf
    exact (hl f hf).trans (hattractive _ _ (hbottom η) f hf)
  have huall : ∀ η, StochLE (K η) u := by
    intro η f hf
    exact (hattractive _ _ (htop η) f hf).trans (hu f hf)
  have hst := mixture_sandwich K p l u hlall huall
  rw [hstationary] at hst
  intro η
  exact tvDist_le_extremal_transport l u (K η) p (hlall η) (huall η) hst.1 hst.2

end Paper09.OrderMixing
