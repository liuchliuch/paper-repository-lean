import GeometricMedianCoresets.LowerTransfer
import Mathlib.Analysis.Asymptotics.Theta

/-! The least uniform-sampling thresholds and their precise quadratic order. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open Filter
namespace GeometricMedianCoresets

/-- The paper's threshold is a guarantee for every dimension and every larger sample size. -/
def ValidThreshold (X : ℕ → Type) (D : (d : ℕ) → Dist (X d)) (ε : ℝ) (M : ℕ) : Prop :=
  0 < M ∧ ∀ (d n m : ℕ), 0 < d → 0 < n → M ≤ m → m ≤ n → ∀ P : Dataset (X d) n,
    ((((Finset.univ : Finset (Fin n)).powersetCard m).filter
      (fun I => IsStableCoreset (D d) P (indexedSample P I) ε (17 * ε))).card : ℝ) /
      (n.choose m : ℝ) ≥ 4/5

/-- Least positive threshold, as specified in §1.1. -/
def sampleThreshold (X : ℕ → Type) (D : (d : ℕ) → Dist (X d)) (ε : ℝ) : ℕ :=
  sInf {M | ValidThreshold X D ε M}

lemma fraction_complement {n m : ℕ} (hmn : m ≤ n) (E : Finset (Fin n) → Prop) :
    ((((Finset.univ : Finset (Fin n)).powersetCard m).filter E).card : ℝ) / (n.choose m : ℝ) +
      ((((Finset.univ : Finset (Fin n)).powersetCard m).filter (fun I => ¬ E I)).card : ℝ) /
        (n.choose m : ℝ) = 1 := by
  have hc := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset (Fin n)).powersetCard m) E
  have hcard :
      (((Finset.univ : Finset (Fin n)).powersetCard m).filter E).card +
        (((Finset.univ : Finset (Fin n)).powersetCard m).filter (fun I => ¬ E I)).card = n.choose m := by
    simpa using hc
  have hcardR :
      ((((Finset.univ : Finset (Fin n)).powersetCard m).filter E).card : ℝ) +
        ((((Finset.univ : Finset (Fin n)).powersetCard m).filter (fun I => ¬ E I)).card : ℝ) = n.choose m := by
    exact_mod_cast hcard
  rw [← add_div, hcardR, div_self (by exact_mod_cast (Nat.choose_pos hmn).ne')]

namespace Euclidean

def threshold (ε : ℝ) : ℕ := sampleThreshold Space (fun d => normDist (Space d)) ε

lemma valid_ceil {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1/4) :
    ValidThreshold Space (fun d => normDist (Space d)) ε ⌈20 / (ε * ε)⌉₊ := by
  have hpos : 0 < ⌈20 / (ε * ε)⌉₊ := Nat.ceil_pos.2 (by positivity)
  refine ⟨hpos, ?_⟩
  intro d n m _ hn hM hmn P
  exact thm_1_2_i hn (lt_of_lt_of_le hpos hM) hmn P hε hε' hM

/-- The minimum threshold is attained in the set of valid positive integers. -/
theorem threshold_valid {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1/4) :
    ValidThreshold Space (fun d => normDist (Space d)) ε (threshold ε) :=
  Nat.sInf_mem (s := {M | ValidThreshold Space (fun d => normDist (Space d)) ε M})
    ⟨_, valid_ceil hε hε'⟩

/-- Quantitative form of the `Θ(ε⁻²)` assertion following Theorem 1.2. -/
theorem threshold_bounds {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1/100) :
    1 / (24200 * ε ^ 2) < (threshold ε : ℝ) ∧ (threshold ε : ℝ) ≤ 21 / ε ^ 2 := by
  have heps : ε < 1/4 := by linarith
  have hv := threshold_valid hε heps
  constructor
  · by_contra hnot
    have hsmall : (threshold ε : ℝ) ≤ 1 / (24200 * ε ^ 2) := le_of_not_gt hnot
    obtain ⟨n, P, hn, hmn, _hinj, hfail⟩ := thm_1_2_ii hε hε' hv.1 hsmall
    have hsuccess := hv.2 1 n (threshold ε) (by norm_num) hn le_rfl hmn P
    have hsum := fraction_complement hmn
      (fun I => IsStableCoreset (normDist (Space 1)) P (indexedSample P I) ε (17 * ε))
    linarith
  · have hle : threshold ε ≤ ⌈20 / (ε * ε)⌉₊ := Nat.sInf_le (valid_ceil hε heps)
    have hleR : (threshold ε : ℝ) ≤ (⌈20 / (ε * ε)⌉₊ : ℝ) := by exact_mod_cast hle
    have hceil := Nat.ceil_lt_add_one (by positivity : 0 ≤ 20 / (ε * ε))
    have hepssq : ε ^ 2 ≤ 1 := by nlinarith
    have hlast : 20 / (ε * ε) + 1 ≤ 21 / ε ^ 2 := by
      apply (le_div_iff₀ (by positivity : 0 < ε ^ 2)).2
      have heq : 20 / (ε * ε) * ε ^ 2 = 20 := by field_simp
      nlinarith
    exact hleR.trans (hceil.le.trans hlast)
end Euclidean

namespace L1

def threshold (ε : ℝ) : ℕ := sampleThreshold Space (fun d => normDist (Space d)) ε

lemma valid_ceil {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1/4) :
    ValidThreshold Space (fun d => normDist (Space d)) ε ⌈20 / (ε * ε)⌉₊ := by
  have hpos : 0 < ⌈20 / (ε * ε)⌉₊ := Nat.ceil_pos.2 (by positivity)
  refine ⟨hpos, ?_⟩
  intro d n m _ hn hM hmn P
  exact uniform_stable_4_5 hn (lt_of_lt_of_le hpos hM) hmn P hε hε' hM

theorem threshold_valid {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1/4) :
    ValidThreshold Space (fun d => normDist (Space d)) ε (threshold ε) :=
  Nat.sInf_mem (s := {M | ValidThreshold Space (fun d => normDist (Space d)) ε M})
    ⟨_, valid_ceil hε hε'⟩

/-- Quantitative form of Corollary 4.2. -/
theorem threshold_bounds {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1/100) :
    1 / (24200 * ε ^ 2) < (threshold ε : ℝ) ∧ (threshold ε : ℝ) ≤ 21 / ε ^ 2 := by
  have heps : ε < 1/4 := by linarith
  have hv := threshold_valid hε heps
  constructor
  · by_contra hnot
    have hsmall : (threshold ε : ℝ) ≤ 1 / (24200 * ε ^ 2) := le_of_not_gt hnot
    obtain ⟨n, P, hn, hmn, _hinj, hfail⟩ := lower_bound hε hε' hv.1 hsmall
    have hsuccess := hv.2 1 n (threshold ε) (by norm_num) hn le_rfl hmn P
    have hsum := fraction_complement hmn
      (fun I => IsStableCoreset (normDist (Space 1)) P (indexedSample P I) ε (17 * ε))
    linarith
  · have hle : threshold ε ≤ ⌈20 / (ε * ε)⌉₊ := Nat.sInf_le (valid_ceil hε heps)
    have hleR : (threshold ε : ℝ) ≤ (⌈20 / (ε * ε)⌉₊ : ℝ) := by exact_mod_cast hle
    have hceil := Nat.ceil_lt_add_one (by positivity : 0 ≤ 20 / (ε * ε))
    have hepssq : ε ^ 2 ≤ 1 := by nlinarith
    have hlast : 20 / (ε * ε) + 1 ≤ 21 / ε ^ 2 := by
      apply (le_div_iff₀ (by positivity : 0 < ε ^ 2)).2
      have heq : 20 / (ε * ε) * ε ^ 2 = 20 := by field_simp
      nlinarith
    exact hleR.trans (hceil.le.trans hlast)
end L1

end GeometricMedianCoresets
