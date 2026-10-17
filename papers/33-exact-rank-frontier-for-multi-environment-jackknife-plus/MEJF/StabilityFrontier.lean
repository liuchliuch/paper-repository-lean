import MEJF.StabilityExtended
import MEJF.RankFrontier

/-! The actual stable-class finite validity set and its unique maximal pair. -/
namespace MEJF.StabilityFrontier
open StabilityExtended Finset
noncomputable section

/-- Positive finite-rank validity for the actual stable-class statistical supremum. -/
def Valid (m n F : ℕ) (ε δ : ℝ) (r : ℕ × ℕ) : Prop :=
  1 ≤ r.1 ∧ r.1 ≤ n ∧ 1 ≤ r.2 ∧ r.2 ≤ m ∧ gamma m n F r.1 r.2 ε ≤ δ

lemma outer_rate_le_floor (m ell : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) :
    (ell : ℝ)/(m+1 : ℕ) ≤ δ ↔ ell ≤ ⌊δ*(m+1 : ℕ)⌋₊ := by
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (m+1 : ℕ))]
  exact (Nat.le_floor_iff (mul_nonneg hδ (by positivity))).symm

/-- Exact finite stable validity is a rectangle of integer ranks. -/
theorem valid_iff (m n F t ell : ℕ) (ε δ : ℝ) (hε : 0 ≤ ε)
    (hF : 1 ≤ F) (hFn : F ≤ n) (hδ : 0 ≤ δ) (hδ1 : δ < 1) :
    Valid m n F ε δ (t,ell) ↔
      1 ≤ t ∧ t ≤ F ∧ 1 ≤ ell ∧ ell ≤ ⌊δ*(m+1 : ℕ)⌋₊ := by
  constructor
  · rintro ⟨ht, htn, he, helm, hg⟩
    have hgamma := gamma_eq m n F t ell ε hε hF hFn htn helm
    rw [if_neg (by omega : ¬ (t = 0 ∨ ell = 0))] at hgamma
    have htF : t ≤ F := by
      by_contra! hFt
      rw [if_pos hFt] at hgamma
      linarith
    rw [if_neg (not_lt.mpr htF)] at hgamma
    refine ⟨ht, htF, he, ?_⟩
    exact (outer_rate_le_floor m ell δ hδ).mp (by rwa [← hgamma])
  · rintro ⟨ht, htF, he, hD⟩
    have helm : ell ≤ m := hD.trans (RankFrontier.floor_budget_le_m hδ hδ1)
    have htn := htF.trans hFn
    refine ⟨ht, htn, he, helm, ?_⟩
    rw [gamma_eq m n F t ell ε hε hF hFn htn helm,
      if_neg (by omega : ¬ (t = 0 ∨ ell = 0)), if_neg (not_lt.mpr htF)]
    exact (outer_rate_le_floor m ell δ hδ).mpr hD

/-- Source (6.31): the unique greatest stable valid finite-rank pair. -/
theorem greatest_valid_pair (m n F : ℕ) (ε δ : ℝ) (hε : 0 ≤ ε)
    (hF : 1 ≤ F) (hFn : F ≤ n) (hδ : 0 ≤ δ) (hδ1 : δ < 1)
    (hD : 1 ≤ ⌊δ*(m+1 : ℕ)⌋₊) :
    IsGreatest {r | Valid m n F ε δ r} (F, ⌊δ*(m+1 : ℕ)⌋₊) := by
  constructor
  · exact (valid_iff m n F F _ ε δ hε hF hFn hδ hδ1).mpr ⟨hF, le_rfl, hD, le_rfl⟩
  · rintro ⟨t, ell⟩ hr
    have hh := (valid_iff m n F t ell ε δ hε hF hFn hδ hδ1).mp hr
    exact ⟨hh.2.1, hh.2.2.2⟩

/-- The greatest pair is the unique coordinatewise maximal valid pair. -/
theorem maximal_valid_pair_iff (m n F t ell : ℕ) (ε δ : ℝ) (hε : 0 ≤ ε)
    (hF : 1 ≤ F) (hFn : F ≤ n) (hδ : 0 ≤ δ) (hδ1 : δ < 1)
    (hD : 1 ≤ ⌊δ*(m+1 : ℕ)⌋₊) :
    (Valid m n F ε δ (t,ell) ∧
      ∀ u v, Valid m n F ε δ (u,v) → t ≤ u → ell ≤ v → u ≤ t ∧ v ≤ ell) ↔
      t = F ∧ ell = ⌊δ*(m+1 : ℕ)⌋₊ := by
  have hg := greatest_valid_pair m n F ε δ hε hF hFn hδ hδ1 hD
  constructor
  · rintro ⟨hv, hmax⟩
    have hb := hg.2 hv
    have hh := hmax F _ hg.1 hb.1 hb.2
    exact ⟨le_antisymm hb.1 hh.1, le_antisymm hb.2 hh.2⟩
  · rintro ⟨rfl, rfl⟩
    refine ⟨hg.1, ?_⟩
    intro u v huv _ _
    exact hg.2 huv

end
end MEJF.StabilityFrontier
