import Paper29.BlockConcentration
import Paper29.ProductLawTools

noncomputable section
open scoped BigOperators Classical
namespace Paper29.HardDistribution

/-- Bad block event on a single actual Bernoulli block. -/
def blockGood {N : ℕ} (β : ℝ) (s : Bool) (y : Fin N → Bool) : Prop :=
  β/2 ≤ sign s * ((∑ k, bit (y k))/(N:ℝ)-1/2)

theorem centeredSum_eq {N : ℕ} (p : ℝ) (y : Fin N → Bool) :
    centeredSum p y = (∑ k, bit (y k))-(N:ℝ)*p := by
  simp [centeredSum, Finset.sum_sub_distrib]

/-- Genuine finite-law Hoeffding bound for each sign, before weakening its
exponent to the numerical e^-5 used by the lower bound. -/
theorem single_bad_block_bound {N : ℕ} (hN : 0 < N) (β : ℝ)
    (hβ : 0 ≤ β) (hβhi : β ≤ 1/2) (s : Bool) :
    Sampling.eventMass (blockMass (1/2+β*sign s))
      (Finset.univ.filter (fun y : Fin N → Bool => ¬blockGood β s y)) ≤
        Real.exp (-(N:ℝ)*β^2/2) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hp : 0 ≤ 1/2+β*sign s := by cases s <;> simp [sign] <;> linarith
  have hp1 : 1/2+β*sign s ≤ 1 := by cases s <;> simp [sign] <;> linarith
  have h := block_hoeffding (N:=N) (1/2+β*sign s) hp hp1 (β/2) (by linarith)
  have he : -2*(N:ℝ)*(β/2)^2 = -(N:ℝ)*β^2/2 := by ring
  rw [he] at h
  cases s with
  | false =>
    apply (ProcessTools.eventMass_mono _ (blockMass_nonneg _ hp hp1) ?_).trans h.2
    intro y hy
    have hh := (Finset.mem_filter.mp hy).2
    simp only [blockGood, sign, Bool.false_eq_true, ↓reduceIte, neg_mul, one_mul, not_le] at hh
    have hm : (N:ℝ)*(1/2-β/2) < ∑ k, bit (y k) := by
      have hd : 1/2-β/2 < (∑ k, bit (y k))/(N:ℝ) := by linarith
      simpa only [mul_comm] using (lt_div_iff₀ hNR).1 hd
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [centeredSum_eq]
    simp only [sign, Bool.false_eq_true, ↓reduceIte, mul_neg, mul_one]
    linarith
  | true =>
    apply (ProcessTools.eventMass_mono _ (blockMass_nonneg _ hp hp1) ?_).trans h.1
    intro y hy
    have hh := (Finset.mem_filter.mp hy).2
    simp only [blockGood, sign, ↓reduceIte, one_mul, not_le] at hh
    have hm : (∑ k, bit (y k)) < (1/2+β/2)*(N:ℝ) := by
      apply (div_lt_iff₀ hNR).1
      linarith
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [centeredSum_eq]
    simp only [sign, ↓reduceIte, mul_one]
    linarith

/-- The true conditional product law has the required single-block marginal. -/
theorem conditional_block_expectation {r N : ℕ} (β : ℝ) (s : Signs r)
    (j : Fin r) (g : (Fin N → Bool) → ℝ) :
    (∑ y : Bits r N, conditionalMass β s y * g (fun k => y (j,k))) =
      ∑ v : Fin N → Bool, blockMass (1/2+β*sign (s j)) v*g v := by
  have he (v : Fin r → Fin N → Bool) : conditionalMass β s ((Equiv.curry (Fin r) (Fin N) Bool).symm v) =
      ∏ a, blockMass (1/2+β*sign (s a)) (v a) := by
    unfold conditionalMass blockMass
    exact Fintype.prod_prod_type (fun a : Fin r × Fin N => bitMass (1/2+β*sign (s a.1)) (v a.1 a.2))
  have hsum := (Equiv.curry (Fin r) (Fin N) Bool).symm.sum_comp
    (fun y : Bits r N => conditionalMass β s y*g (fun k => y (j,k)))
  rw [← hsum]
  simp only [he]
  simpa only [Equiv.curry_symm_apply] using Sampling.product_coordinate_expectation (fun a : Fin r => blockMass (1/2+β*sign (s a)))
    (fun a => blockMass_total N _) g j

/-- Original good-block probability, under each actual conditional hard law. -/
theorem conditional_bad_block_bound {r N : ℕ} (hN : 0 < N) (β : ℝ)
    (hβ : 0 ≤ β) (hβhi : β ≤ 1/2) (hscale : 10 ≤ (N:ℝ)*β^2)
    (s : Signs r) (j : Fin r) :
    Sampling.eventMass (conditionalMass β s)
      (Finset.univ.filter (fun y : Bits r N => ¬GoodBlock β s y j)) ≤ Real.exp (-5) := by
  have he : Sampling.eventMass (conditionalMass β s)
      (Finset.univ.filter (fun y : Bits r N => ¬GoodBlock β s y j)) =
      Sampling.eventMass (blockMass (1/2+β*sign (s j)))
        (Finset.univ.filter (fun v : Fin N → Bool => ¬blockGood β (s j) v)) := by
    simp only [Sampling.eventMass, Finset.sum_filter]
    have hh := conditional_block_expectation (N:=N) β s j (fun v => if ¬blockGood β (s j) v then 1 else 0)
    simpa only [GoodBlock, blockMean, blockGood, mul_ite, mul_one, mul_zero] using hh
  rw [he]
  exact (single_bad_block_bound hN β hβ hβhi (s j)).trans (Real.exp_le_exp.mpr (by linarith))

end Paper29.HardDistribution
