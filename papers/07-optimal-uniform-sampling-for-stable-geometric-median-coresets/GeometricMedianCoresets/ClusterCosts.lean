import GeometricMedianCoresets.NormedMedian
import GeometricMedianCoresets.LabelLaw

/-! Stability failure from actual perturbed two-cluster data, with all cost bounds proved. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace GeometricMedianCoresets.LowerBound

/-- Locations at zero and one before the distinct-point perturbation. -/
def base {n : ℕ} (mark : Fin n → Bool) : Dataset ℝ n := fun i => if mark i then 0 else 1

/-- Moving each indexed point by at most `ρ` changes every average cost by at most `ρ`. -/
theorem cost_perturb_bound {n : ℕ} (hn : 0 < n) (P R : Dataset ℝ n) {ρ : ℝ}
    (hpert : ∀ i, |P i - R i| ≤ ρ) (z : ℝ) :
    |(normDist ℝ).cost P z - (normDist ℝ).cost R z| ≤ ρ := by
  have hpoint : ∀ i, |‖z - P i‖ - ‖z - R i‖| ≤ ρ := by
    intro i
    have h := abs_norm_sub_norm_le (z - P i) (z - R i)
    have heq : (z - P i) - (z - R i) = -(P i - R i) := by ring
    rw [heq, norm_neg, Real.norm_eq_abs] at h
    exact h.trans (hpert i)
  have hs := (Finset.abs_sum_le_sum_abs (fun i => ‖z - P i‖ - ‖z - R i‖) Finset.univ).trans
    (Finset.sum_le_sum (fun i _ => hpoint i))
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  unfold Dist.cost normDist
  rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_nonneg hnR.le]
  apply (div_le_iff₀ hnR).2
  simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using hs

/-- The ideal cost at one is exactly the fraction of indices in the zero-cluster. -/
lemma base_cost_one {n : ℕ} (mark : Fin n → Bool) :
    (normDist ℝ).cost (base mark) 1 =
      (((Finset.univ : Finset (Fin n)).filter (fun i => mark i = true)).card : ℝ) / n := by
  unfold Dist.cost normDist base
  have heq : ∀ i : Fin n, ‖(1:ℝ) - (if mark i then 0 else 1)‖ = if mark i = true then 1 else 0 := by
    intro i
    cases mark i <;> norm_num
  simp_rw [heq]
  simp [Finset.sum_ite]

lemma base_cost_zero {n : ℕ} (hn : 0 < n) (mark : Fin n → Bool) :
    (normDist ℝ).cost (base mark) 0 =
      1 - (((Finset.univ : Finset (Fin n)).filter (fun i => mark i = true)).card : ℝ) / n := by
  unfold Dist.cost normDist base
  have heq : ∀ i : Fin n, ‖(0:ℝ) - (if mark i then 0 else 1)‖ = if mark i = false then 1 else 0 := by
    intro i
    cases mark i <;> norm_num
  simp_rw [heq]
  have hs : (∑ i : Fin n, if mark i = false then (1:ℝ) else 0) =
      (((Finset.univ : Finset (Fin n)).filter (fun i => mark i = false)).card : ℝ) := by
    simp [Finset.sum_ite]
  rw [hs]
  have hc := LabelLaw.false_card mark
  have hcR :
      (((Finset.univ : Finset (Fin n)).filter (fun i => mark i = true)).card : ℝ) +
      (((Finset.univ : Finset (Fin n)).filter (fun i => mark i = false)).card : ℝ) = n := by
    exact_mod_cast hc
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  linarith

/-- The ideal cluster fraction in an enumerated actual sample equals its index count. -/
lemma sample_base_fraction {n : ℕ} (mark : Fin n → Bool) (I : Finset (Fin n)) :
    (normDist ℝ).cost (indexedSample (base mark) I) 1 =
      ((I.filter (fun i => mark i = true)).card : ℝ) / I.card := by
  unfold Dist.cost normDist
  rw [sum_indexedSample]
  have heq : ∀ i ∈ I, ‖(1:ℝ) - base mark i‖ = if mark i = true then 1 else 0 := by
    intro i _
    cases hi : mark i <;> norm_num [base, hi]
  rw [Finset.sum_congr rfl heq]
  simp [Finset.sum_ite]

/-- A uniform sample with a zero-cluster majority violates the stable-coreset implication. -/
theorem majority_not_stable {n : ℕ} (hn : 0 < n) (mark : Fin n → Bool) (P : Dataset ℝ n)
    {ε θ : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1/100) (hθ : 10 * ε ≤ θ)
    (hp : ((((Finset.univ : Finset (Fin n)).filter (fun i => mark i = true)).card : ℝ) / n) =
      (1 - θ) / 2)
    (hpert : ∀ i, |P i - base mark i| ≤ ε ^ 2 / 100)
    (I : Finset (Fin n)) (hI : 0 < I.card)
    (hmajority : I.card ≤ 2 * (I.filter (fun i => mark i = true)).card) :
    ¬ IsStableCoreset (normDist ℝ) P (indexedSample P I) ε (17 * ε) := by
  have hpop0 := (abs_le.1 (cost_perturb_bound hn P (base mark) hpert 0)).1
  have hpop1 := (abs_le.1 (cost_perturb_bound hn P (base mark) hpert 1)).2
  rw [base_cost_zero hn mark, hp] at hpop0
  rw [base_cost_one mark, hp] at hpop1
  have hθmul := mul_le_mul_of_nonneg_left hθ (by linarith : 0 ≤ 1 + 17 * ε / 2)
  have hgap : (1 + 17 * ε) * (normDist ℝ).cost P 1 < (normDist ℝ).cost P 0 := by
    have hmul := mul_le_mul_of_nonneg_left hpop1 (by linarith : 0 ≤ 1 + 17 * ε)
    have hepssq : ε ^ 2 ≤ ε / 100 := by nlinarith
    have hsmall : ε * (ε ^ 2 / 100) ≤ ε ^ 2 / 10000 := by nlinarith
    nlinarith
  let Q := indexedSample P I
  let R := indexedSample (base mark) I
  let markQ : Fin I.card → Bool := fun j => mark ((I.equivFin.symm j).val)
  have hR : R = base markQ := rfl
  have hpertQ : ∀ j, |Q j - R j| ≤ ε ^ 2 / 100 :=
    fun j => hpert ((I.equivFin.symm j).val)
  have hs0 := (abs_le.1 (cost_perturb_bound hI Q R hpertQ 0)).2
  have hs1 := (abs_le.1 (cost_perturb_bound hI Q R hpertQ 1)).1
  have hRone := sample_base_fraction mark I
  change (normDist ℝ).cost R 1 = _ at hRone
  have hRzero : (normDist ℝ).cost R 0 = 1 - (normDist ℝ).cost R 1 := by
    rw [hR, base_cost_zero hI markQ, base_cost_one markQ]
  have hsampleR : (1/2:ℝ) ≤ (normDist ℝ).cost R 1 := by
    rw [hRone]
    apply (le_div_iff₀ (by exact_mod_cast hI : (0:ℝ) < I.card)).2
    have hmR : (I.card:ℝ) ≤ 2 * ((I.filter (fun i => mark i = true)).card : ℝ) := by
      exact_mod_cast hmajority
    linarith
  have hs0' : (normDist ℝ).cost Q 0 ≤ 1/2 + ε ^ 2 / 100 := by linarith
  have hs1' : 1/2 - ε ^ 2 / 100 ≤ (normDist ℝ).cost Q 1 := by linarith
  have hcomp : (normDist ℝ).cost Q 0 ≤ (1 + ε) * (normDist ℝ).cost Q 1 := by
    have hmul := mul_le_mul_of_nonneg_left hs1' (by linarith : 0 ≤ 1 + ε)
    have hepssq : ε ^ 2 ≤ ε / 100 := by nlinarith
    have hsmall : ε * (ε ^ 2 / 100) ≤ ε ^ 2 / 10000 := by nlinarith
    nlinarith
  intro hstable
  have hc := hstable 0 1 hcomp
  linarith

end GeometricMedianCoresets.LowerBound
