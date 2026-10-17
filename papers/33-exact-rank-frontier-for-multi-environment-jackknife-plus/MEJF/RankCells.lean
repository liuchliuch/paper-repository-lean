import MEJF.AsymmetricFrontier
import MEJF.ActualAsymptotic

/-! Exact rank cells (3.11), pathwise monotonicity at every covariate,
and the source-level numerical instance in Proposition 7.1. -/
namespace MEJF.RankCells
open MEJF.Setup MEJF.AsymmetricFrontier
noncomputable section

/-- The exact left-closed, right-open floor cell, including the zero cell. -/
theorem shifted_rank_cell (v k : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    ⌊a*((v:ℝ)+1)⌋₊=k ↔ (k:ℝ)/(v+1:ℝ) ≤ a ∧ a < ((k:ℝ)+1)/(v+1:ℝ) := by
  have hp : (0:ℝ) < (v:ℝ)+1 := by positivity
  rw [Nat.floor_eq_iff (mul_nonneg ha hp.le)]
  constructor
  · rintro ⟨h1,h2⟩
    exact ⟨(div_le_iff₀ hp).mpr (by nlinarith),(lt_div_iff₀ hp).mpr (by nlinarith)⟩
  · rintro ⟨h1,h2⟩
    exact ⟨by have := (div_le_iff₀ hp).mp h1; nlinarith,
      by have := (lt_div_iff₀ hp).mp h2; nlinarith⟩

variable {X : Type*} [MeasurableSpace X] {m n : ℕ}

lemma radius_antitone_inner (A : Learner X n) (Z : Fin (m+1) → Block X n)
    (i k : Fin (m+1)) (t r : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (hr : 1 ≤ r ∧ r ≤ n) (htr : t ≤ r) :
    radius A Z i k r hr  ≤  radius A Z i k t ht := by
  apply OrderStatistics.stat_monotone_rank
  change n-r  ≤  n-t
  omega

/-- Increasing either positive trimming rank shrinks the actual endpoint
interval, for every fixed data array and every queried covariate x. -/
theorem intervalAt_antitone (A : Learner X n) (Z : Fin (m+1) → Block X n)
    (i : Fin (m+1)) (x : X) (t r ell q : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (hr : 1 ≤ r ∧ r ≤ n)
    (he : 1 ≤ ell ∧ ell ≤ m) (hq : 1 ≤ q ∧ q ≤ m) (htr : t ≤ r) (heq : ell ≤ q) :
    intervalAt A Z i x r q q hr hq hq ⊆ intervalAt A Z i x t ell ell ht he he := by
  apply Set.Icc_subset_Icc
  · calc
      lowerAt A Z i x t ell ht he  ≤  lowerAt A Z i x r ell hr he := by
        apply OrderStatistics.stat_mono
        intro k
        exact sub_le_sub_left (radius_antitone_inner A Z (i.succAbove k) i t r ht hr htr) _
      _  ≤  lowerAt A Z i x r q hr hq := by
        apply OrderStatistics.stat_monotone_rank
        change ell-1 ≤ q-1
        omega
  · calc
      upperAt A Z i x r q hr hq  ≤  upperAt A Z i x r ell hr he := by
        apply OrderStatistics.stat_monotone_rank
        change m-q ≤ m-ell
        omega
      _  ≤  upperAt A Z i x t ell ht he := by
        apply OrderStatistics.stat_mono
        intro k
        exact add_le_add_left (radius_antitone_inner A Z (i.succAbove k) i t r ht hr htr) _

/-- Continuous levels have no additional pathwise effect inside one rank cell. -/
theorem interval_constant_on_cell (A : Learner X n) (Z : Fin (m+1) → Block X n)
    (i : Fin (m+1)) (x : X) (a a' b b' : ℝ)
    (hta : 1 ≤ innerRank a n ∧ innerRank a n ≤ n)
    (hta' : 1 ≤ innerRank a' n ∧ innerRank a' n ≤ n)
    (heb : 1 ≤ outerRank b m ∧ outerRank b m ≤ m)
    (heb' : 1 ≤ outerRank b' m ∧ outerRank b' m ≤ m)
    (ha : innerRank a n=innerRank a' n) (hb : outerRank b m=outerRank b' m) :
    intervalAt A Z i x (innerRank a n) (outerRank b m) (outerRank b m) hta heb heb =
      intervalAt A Z i x (innerRank a' n) (outerRank b' m) (outerRank b' m) hta' heb' heb' := by
  have hi : innerIndex n (innerRank a n) hta = innerIndex n (innerRank a' n) hta' := by
    apply Fin.ext
    simp only [innerIndex, ha]
  have hl : lowerIndex m (outerRank b m) heb = lowerIndex m (outerRank b' m) heb' := by
    apply Fin.ext
    simp only [lowerIndex, hb]
  have hu : upperIndex m (outerRank b m) heb = upperIndex m (outerRank b' m) heb' := by
    apply Fin.ext
    simp only [upperIndex, hb]
  have hr : ∀ u v : Fin (m+1), radius A Z u v (innerRank a n) hta =
      radius A Z u v (innerRank a' n) hta' := by
    intro u v
    unfold radius
    rw [hi]
  unfold intervalAt lowerAt upperAt
  simp_rw [hr]
  rw [hl, hu]

/-- Proposition 7.1 at the literal continuous levels, including all floors. -/
theorem ordinary_factor_two_at_levels :
    ActualAsymptotic.Gamma 19 200 (1/5) (1/5) (1/10)=1 := by
  have ht : innerRank (1/5) 200 = 40 := by
    unfold innerRank
    apply (Nat.floor_eq_iff (by norm_num)).mpr
    constructor  <;> norm_num
  have he : outerRank (1/10) 19 = 2 := by norm_num [outerRank]
  rw [ActualAsymptotic.Gamma_law 19 200 (1/5) (1/5) (1/10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), ht, he]
  norm_num [innerRank,outerRank,failureRank,RankFrontier.failureRate,
    RankFrontier.failureCount,RankFrontier.capacity]

end
end MEJF.RankCells
