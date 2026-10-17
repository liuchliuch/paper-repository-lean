import MEJF.MainExact

/-! Source-indexed consequences of the actual statistical minimax identity. -/
namespace MEJF.MainResults
open MEJF.Setup MEJF.RankFrontier
noncomputable section

/-- Theorem 3.1, the two exact finite-rank branches of the statistical law. -/
theorem exact_failure_law (m n : ℕ) (alpha : ℝ) (ha : 0 ≤ alpha) (ha1 : alpha < 1)
    (t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    finiteRankGamma m n alpha t ell ht he =
      if failureRank alpha n < t then 1 else
        min 1 ((2 * (capacity m (failureRank alpha n) t ell : ℝ)+1) / (m+1 : ℕ)) := by
  rw [MainExact.finiteRankGamma_eq m n alpha ha ha1 t ell ht he]
  split_ifs with h
  · exact failureRate_high_inner h
  · exact failureRate_eq_min (by omega)

/-- Corollary 3.2, stated for the actual statistical supremum and its exact
finite-sample floor. All positive finite ranks occur in this equivalence. -/
theorem finite_validity_criterion (m n : ℕ) (alpha delta : ℝ)
    (ha : 0 ≤ alpha) (ha1 : alpha < 1) (hd : 0 < delta) (hd1 : delta < 1)
    (t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m)
    (hD : 1 ≤ ⌊delta * (m+1 : ℕ)⌋₊) :
    finiteRankGamma m n alpha t ell ht he ≤ delta ↔
      t ≤ failureRank alpha n ∧ ell ≤ halfCeil ⌊delta * (m+1 : ℕ)⌋₊ ∧
      halfCeil ⌊delta * (m+1 : ℕ)⌋₊ * (t-1)+1 ≤
        failureRank alpha n * (halfCeil ⌊delta * (m+1 : ℕ)⌋₊-ell+1) := by
  rw [MainExact.finiteRankGamma_eq m n alpha ha ha1 t ell ht he]
  exact RankFrontier.finite_validity_criterion hd hd1 ht.1 he.1 hD

/-- The zero-budget impossibility in Corollary 3.2. -/
theorem zero_floor_impossible (m n : ℕ) (alpha delta : ℝ)
    (ha : 0 ≤ alpha) (ha1 : alpha < 1) (hd : 0 ≤ delta)
    (t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m)
    (hD : ⌊delta * (m+1 : ℕ)⌋₊ = 0) :
    ¬ finiteRankGamma m n alpha t ell ht he ≤ delta := by
  rw [MainExact.finiteRankGamma_eq m n alpha ha ha1 t ell ht he]
  exact RankFrontier.zero_floor_impossible hd hD

/-- Corollary 3.6's finite-sample complete-failure phase for the actual Γ. -/
theorem complete_failure_iff (m n : ℕ) (alpha : ℝ) (ha : 0 ≤ alpha) (ha1 : alpha < 1)
    (t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    finiteRankGamma m n alpha t ell ht he = 1 ↔
      failureRank alpha n < t ∨
      (t ≤ failureRank alpha n ∧
        (failureRank alpha n-t+1)*halfCeil m ≤ failureRank alpha n*(ell-1)) := by
  rw [MainExact.finiteRankGamma_eq m n alpha ha ha1 t ell ht he]
  exact complete_failure_rate_iff

/-- The exact floor relation for (2.7) in the finite-rank regime. -/
theorem exact_law_at_levels (m n : ℕ) (alpha a b : ℝ) (ha : 0 ≤ alpha) (ha1 : alpha < 1)
    (ht : 1 ≤ innerRank a n ∧ innerRank a n ≤ n)
    (he : 1 ≤ outerRank b m ∧ outerRank b m ≤ m) :
    finiteRankGamma m n alpha (innerRank a n) (outerRank b m) ht he =
      failureRate m (failureRank alpha n) (innerRank a n) (outerRank b m) :=
  MainExact.finiteRankGamma_eq m n alpha ha ha1 _ _ ht he

/-- Remark 3.5, outer rank one has the smallest possible positive finite failure rate. -/
theorem one_outer (m n : ℕ) (alpha : ℝ) (ha : 0 ≤ alpha) (ha1 : alpha < 1)
    (t : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (hm : 1 ≤ m) (htF : t ≤ failureRank alpha n) :
    finiteRankGamma m n alpha t 1 ht ⟨le_rfl,hm⟩ = 1/(m+1 : ℕ) := by
  rw [MainExact.finiteRankGamma_eq m n alpha ha ha1 t 1 ht ⟨le_rfl,hm⟩]
  exact failureRate_one_outer htF

/-- Proposition 7.1: the ordinary outer factor-two allocation fails completely. -/
theorem ordinary_factor_two_failure :
    finiteRankGamma 19 200 (1/5) 40 2 (by norm_num) (by norm_num) = 1 := by
  rw [MainExact.finiteRankGamma_eq 19 200 (1/5) (by norm_num) (by norm_num)]
  norm_num [failureRank, failureRate, failureCount, capacity]

/-- Proposition 7.2's statistical validity value at the non-extreme pair. -/
theorem nonextreme_validity :
    finiteRankGamma 19 19 (1/5) 2 2 (by norm_num) (by norm_num) = 3/20 ∧
    finiteRankGamma 19 19 (1/5) 2 2 (by norm_num) (by norm_num) < 1/5 := by
  have hv : finiteRankGamma 19 19 (1/5) 2 2 (by norm_num) (by norm_num) = 3/20 := by
    rw [MainExact.finiteRankGamma_eq 19 19 (1/5) (by norm_num) (by norm_num)]
    have hf : failureRank (1/5) 19 = 4 := by
      have hh : ⌊(1/5:ℝ)*19⌋₊ = 3 := by
        apply (Nat.floor_eq_iff (by norm_num)).mpr
        constructor <;> norm_num
      simpa [failureRank] using congrArg (fun x : ℕ => x+1) hh
    rw [hf]
    exact RankFrontier.nonextreme_example
  exact ⟨hv, by rw [hv]; norm_num⟩

end
end MEJF.MainResults
