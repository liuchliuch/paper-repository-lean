import MEJF.MainResults

/-! The Pareto antichain of the actual finite-rank statistical problem. -/
namespace MEJF.ActualPareto
open MEJF.Setup MEJF.RankFrontier Finset
noncomputable section
attribute [local instance] Classical.propDecidable

def Valid (m n : ℕ) (alpha delta : ℝ) (t ell : ℕ) : Prop :=
  (1 ≤ t ∧ t ≤ n) ∧ (1 ≤ ell ∧ ell ≤ m) ∧
    ∀ (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m),
      finiteRankGamma m n alpha t ell ht he ≤ delta

def Pareto (m n : ℕ) (alpha delta : ℝ) (t ell : ℕ) : Prop :=
  Valid m n alpha delta t ell ∧
    ∀ t' ell', Valid m n alpha delta t' ell' → t ≤ t' → ell ≤ ell' → t'=t ∧ ell'=ell

def ranks (m n : ℕ) (alpha delta : ℝ) : Finset (ℕ × ℕ) :=
  ((Icc 1 n) ×ˢ (Icc 1 m)).filter fun p => Pareto m n alpha delta p.1 p.2

lemma failureRank_bounds {n : ℕ} {alpha : ℝ} (hn : 0 < n)
    (ha : 0 ≤ alpha) (ha1 : alpha < 1) : 1 ≤ failureRank alpha n ∧ failureRank alpha n ≤ n := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hlt : ⌊alpha * n⌋₊ < n :=
    (Nat.floor_lt (mul_nonneg ha hnR.le)).mpr (by nlinarith)
  unfold failureRank
  omega

/-- Source Corollary 3.2 identifies exactly the positive validity cells, even
when validity is defined directly by the minimax supremum. -/
theorem valid_iff_lattice {m n : ℕ} {alpha delta : ℝ}
    (hn : 0 < n) (ha : 0 ≤ alpha) (ha1 : alpha < 1)
    (hd : 0 < delta) (hd1 : delta < 1) (hD : 1 ≤ ⌊delta*(m+1:ℕ)⌋₊) (t ell : ℕ) :
    Valid m n alpha delta t ell ↔
      LatticeValid (failureRank alpha n) (halfCeil ⌊delta*(m+1:ℕ)⌋₊) t ell := by
  have hF := failureRank_bounds hn ha ha1
  have hqm : halfCeil ⌊delta*(m+1:ℕ)⌋₊ ≤ m :=
    le_trans halfCeil_le (floor_budget_le_m hd.le hd1)
  constructor
  · rintro ⟨ht, he, hv⟩
    have hh := (MainResults.finite_validity_criterion m n alpha delta ha ha1 hd hd1 t ell ht he hD).mp (hv ht he)
    exact ⟨ht.1,hh.1,he.1,hh.2.1,by omega⟩
  · intro h
    have ht : 1 ≤ t ∧ t ≤ n := ⟨h.1, le_trans h.2.1 hF.2⟩
    have he : 1 ≤ ell ∧ ell ≤ m := ⟨h.2.2.1, le_trans h.2.2.2.1 hqm⟩
    refine ⟨ht,he,fun ht he => ?_⟩
    exact (MainResults.finite_validity_criterion m n alpha delta ha ha1 hd hd1 t ell ht he hD).mpr
      ⟨h.2.1,h.2.2.2.1,Nat.succ_le_of_lt h.2.2.2.2⟩

lemma pareto_iff_lattice {m n : ℕ} {alpha delta : ℝ}
    (hn : 0 < n) (ha : 0 ≤ alpha) (ha1 : alpha < 1)
    (hd : 0 < delta) (hd1 : delta < 1) (hD : 1 ≤ ⌊delta*(m+1:ℕ)⌋₊) (t ell : ℕ) :
    Pareto m n alpha delta t ell ↔
      RankFrontier.Pareto (failureRank alpha n) (halfCeil ⌊delta*(m+1:ℕ)⌋₊) t ell := by
  unfold Pareto RankFrontier.Pareto
  simp only [valid_iff_lattice hn ha ha1 hd hd1 hD]

/-- Equality of the actual statistical antichain with the explicitly enumerated
integer antichain. This also checks the finite bounds `t ≤ n`, `ell ≤ m`. -/
theorem ranks_eq_lattice {m n : ℕ} {alpha delta : ℝ}
    (hn : 0 < n) (ha : 0 ≤ alpha) (ha1 : alpha < 1)
    (hd : 0 < delta) (hd1 : delta < 1) (hD : 1 ≤ ⌊delta*(m+1:ℕ)⌋₊) :
    ranks m n alpha delta = paretoRanks (failureRank alpha n) (halfCeil ⌊delta*(m+1:ℕ)⌋₊) := by
  ext p
  rcases p with ⟨t,ell⟩
  rw [mem_paretoRanks]
  simp only [ranks, mem_filter, mem_product, mem_Icc]
  constructor
  · intro h
    exact (pareto_iff_lattice hn ha ha1 hd hd1 hD t ell).mp h.2
  · intro h
    have hp := (pareto_iff_lattice hn ha ha1 hd hd1 hD t ell).mpr h
    exact ⟨⟨hp.1.1,hp.1.2.1⟩,hp⟩

/-- Corollary 3.3's exact cardinality for actual statistically valid rank pairs. -/
theorem ranks_card {m n : ℕ} {alpha delta : ℝ}
    (hn : 0 < n) (ha : 0 ≤ alpha) (ha1 : alpha < 1)
    (hd : 0 < delta) (hd1 : delta < 1) (hD : 1 ≤ ⌊delta*(m+1:ℕ)⌋₊) :
    (ranks m n alpha delta).card = min (failureRank alpha n) (halfCeil ⌊delta*(m+1:ℕ)⌋₊) := by
  rw [ranks_eq_lattice hn ha ha1 hd hd1 hD]
  exact paretoRanks_card (by unfold failureRank; omega) (halfCeil_pos (by omega))

end
end MEJF.ActualPareto
