import MEJF.Asymmetric

/-! The arbitrary-covariate containment and actual rank-Pareto conclusion of
Theorem 6.2. These statements retain the quantifier over every queried x. -/
namespace MEJF.AsymmetricFrontier
open MEJF.Setup
noncomputable section
variable {X : Type*} [MeasurableSpace X] {m n : ℕ}

def lowerAt (A : Learner X n) (Z : Fin (m+1) → Block X n)
    (i : Fin (m+1)) (x : X) (t ell : ℕ) (ht : 1≤t ∧ t≤n) (he : 1≤ell ∧ ell≤m) : ℝ :=
  OrderStatistics.stat (fun k : Fin m =>
    pairPrediction A Z i (i.succAbove k) x-radius A Z (i.succAbove k) i t ht)
    (lowerIndex m ell he)

def upperAt (A : Learner X n) (Z : Fin (m+1) → Block X n)
    (i : Fin (m+1)) (x : X) (t ell : ℕ) (ht : 1≤t ∧ t≤n) (he : 1≤ell ∧ ell≤m) : ℝ :=
  OrderStatistics.stat (fun k : Fin m =>
    pairPrediction A Z i (i.succAbove k) x+radius A Z (i.succAbove k) i t ht)
    (upperIndex m ell he)

def intervalAt (A : Learner X n) (Z : Fin (m+1) → Block X n)
    (i : Fin (m+1)) (x : X) (t lm lp : ℕ) (ht : 1≤t ∧ t≤n)
    (hm : 1≤lm ∧ lm≤m) (hp : 1≤lp ∧ lp≤m) : Set ℝ :=
  Set.Icc (lowerAt A Z i x t lm ht hm) (upperAt A Z i x t lp ht hp)

@[simp] theorem intervalAt_observed (A : Learner X n) (Z : Fin (m+1) → Block X n)
    (i : Fin (m+1)) (j : Fin n) (t lm lp : ℕ) (ht : 1≤t ∧ t≤n)
    (hm : 1≤lm ∧ lm≤m) (hp : 1≤lp ∧ lp≤m) :
    intervalAt A Z i (Z i j).1 t lm lp ht hm hp =
      Asymmetric.interval A Z i j t lm lp ht hm hp := rfl

/-- Equation (6.17) at every covariate, for every actual data array and fit. -/
theorem symmetric_interval_subset (A : Learner X n) (Z : Fin (m+1) → Block X n)
    (i : Fin (m+1)) (x : X) (t lm lp : ℕ) (ht : 1≤t ∧ t≤n)
    (hm : 1≤lm ∧ lm≤m) (hp : 1≤lp ∧ lp≤m) :
    intervalAt A Z i x t (max lm lp) (max lm lp) ht
      (Asymmetric.maxRankProof hm hp) (Asymmetric.maxRankProof hm hp) ⊆
      intervalAt A Z i x t lm lp ht hm hp := by
  apply Set.Icc_subset_Icc
  · apply OrderStatistics.stat_monotone_rank
    change lm-1 ≤ max lm lp-1
    omega
  · apply OrderStatistics.stat_monotone_rank
    change m-max lm lp ≤ m-lp
    omega

/-- Validity defined through the independently defined asymmetric statistical
supremum; finite rank proofs are existentially packaged. -/
def OuterValid (m n : ℕ) (alpha delta : ℝ) (t lm lp : ℕ) (ht : 1≤t ∧ t≤n) : Prop :=
  ∃ (hm : 1≤lm ∧ lm≤m) (hp : 1≤lp ∧ lp≤m),
    Asymmetric.gamma m n alpha t lm lp ht hm hp ≤ delta

def OuterPareto (m n : ℕ) (alpha delta : ℝ) (t lm lp : ℕ) (ht : 1≤t ∧ t≤n) : Prop :=
  OuterValid m n alpha delta t lm lp ht ∧
    ∀ lm' lp', OuterValid m n alpha delta t lm' lp' ht → lm≤lm' → lp≤lp' → lm'=lm ∧ lp'=lp

/-- Every maximal valid outer-rank pair is symmetric, as asserted in 6.2. -/
theorem outer_pareto_symmetric (m n : ℕ) (alpha delta : ℝ)
    (ha : 0≤alpha) (ha1 : alpha<1) (t lm lp : ℕ) (ht : 1≤t ∧ t≤n)
    (h : OuterPareto m n alpha delta t lm lp ht) : lm=lp := by
  obtain ⟨hm,hp,hv⟩ := h.1
  have hmax : OuterValid m n alpha delta t (max lm lp) (max lm lp) ht := by
    refine ⟨Asymmetric.maxRankProof hm hp,Asymmetric.maxRankProof hm hp,?_⟩
    rw [Asymmetric.gamma_eq m n alpha ha ha1] at hv ⊢
    simpa only [max_self] using hv
  have hh := h.2 (max lm lp) (max lm lp) hmax (le_max_left _ _) (le_max_right _ _)
  omega

end
end MEJF.AsymmetricFrontier
