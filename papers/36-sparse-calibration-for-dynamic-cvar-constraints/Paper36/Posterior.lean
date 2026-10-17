import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Probability.Martingale.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Real.Sqrt
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Kernel.CondDistrib

/-!
# Probability ingredients for P36

This file formalizes Appendix C.3 on arbitrary probability spaces using actual
Mathlib conditional expectations. It does not postulate concentration events or
posterior simulation bounds. The episode variables are numbered from zero, so
`Z k` is measurable at time `k + 1` and its conditional mean is taken at time `k`.
-/

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal

namespace Paper36.Posterior

/-- The chord bound used in the exponential argument for Appendix C.3. -/
theorem exp_neg_le_one_sub_half {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    Real.exp (-z) ≤ 1 - z / 2 := by
  have he : Real.exp (-1) ≤ (1 : ℝ) / 2 := by
    have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp 1) (Real.exp_pos (-1)).le
    have hmul : Real.exp 1 * Real.exp (-1) = 1 := by
      rw [← Real.exp_add]
      norm_num
    rw [hmul] at h
    linarith
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-1 : ℝ))
    (sub_nonneg.mpr hz1) hz0 (by ring : (1 - z) + z = 1)
  simp only [smul_eq_mul, mul_zero, zero_add, mul_neg, mul_one, Real.exp_zero] at h
  nlinarith

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- A measurable random variable in `[0,1]` is integrable. -/
theorem integrable_unit_interval {Z : Ω → ℝ} (hZ : AEStronglyMeasurable[m0] Z μ)
    (hbound : ∀ᵐ ω ∂μ, 0 ≤ Z ω ∧ Z ω ≤ 1) : Integrable Z μ := by
  apply Integrable.of_bound hZ 1
  filter_upwards [hbound] with ω hω
  simpa only [Real.norm_eq_abs, abs_of_nonneg hω.1] using hω.2

/-- Conditional means preserve the almost-sure interval `[0,1]`. -/
theorem condExp_unit_interval {m : MeasurableSpace Ω} (hm : m ≤ m0) {Z : Ω → ℝ}
    (hZ : Integrable Z μ) (hbound : ∀ᵐ ω ∂μ, 0 ≤ Z ω ∧ Z ω ≤ 1) :
    ∀ᵐ ω ∂μ, 0 ≤ (μ[Z | m]) ω ∧ (μ[Z | m]) ω ≤ 1 := by
  have hlo : 0 ≤ᵐ[μ] μ[Z | m] := condExp_nonneg (hbound.mono fun _ h => h.1)
  have hhi := condExp_mono (m := m) hZ (integrable_const (1 : ℝ))
    (hbound.mono fun _ h => h.2)
  rw [condExp_const hm] at hhi
  filter_upwards [hlo, hhi] with ω hlo hhi
  exact ⟨hlo, hhi⟩

/-- The conditional one-step exponential estimate, proved from the chord bound. -/
theorem condExp_exp_neg_le {m : MeasurableSpace Ω} (hm : m ≤ m0) {Z : Ω → ℝ}
    (hZ : AEStronglyMeasurable[m0] Z μ)
    (hbound : ∀ᵐ ω ∂μ, 0 ≤ Z ω ∧ Z ω ≤ 1) :
    μ[fun ω => Real.exp (-Z ω) | m] ≤ᵐ[μ]
      fun ω => Real.exp (-(μ[Z | m] ω) / 2) := by
  have hZi := integrable_unit_interval hZ hbound
  have hEi : Integrable (fun ω => Real.exp (-Z ω)) μ := by
    apply Integrable.of_bound (hZ.neg.aemeasurable.exp.aestronglyMeasurable) 1
    filter_upwards [hbound] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hω.1)
  have hlin : Integrable (fun ω => 1 - Z ω / 2) μ := by
    exact (integrable_const (1 : ℝ)).sub (hZi.div_const 2)
  have hmono := condExp_mono (m := m) hEi hlin
    (hbound.mono fun _ h => exp_neg_le_one_sub_half h.1 h.2)
  have hce : μ[fun ω => 1 - Z ω / 2 | m] =ᵐ[μ]
      fun ω => 1 - (μ[Z | m] ω) / 2 := by
    have hsub := condExp_sub (integrable_const (1 : ℝ)) (hZi.div_const 2) m
    have hsmul : μ[fun ω => Z ω / 2|m] =ᵐ[μ]
        (fun ω => (μ[Z|m]) ω / 2) := by
      have hfun : (1 / 2 : ℝ) • Z = fun ω => Z ω / 2 := by
        funext ω
        simp [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
      have h := condExp_smul (μ := μ) (1 / 2 : ℝ) Z m
      rw [hfun] at h
      filter_upwards [h] with ω hω
      simpa [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm] using hω
    rw [condExp_const hm] at hsub
    filter_upwards [hsub, hsmul] with ω hs hmul
    simp only [Pi.sub_apply] at hs
    rw [hmul] at hs
    exact hs
  filter_upwards [hmono, hce] with ω hmono hce
  rw [hce] at hmono
  exact hmono.trans (by linarith [Real.add_one_le_exp (-(μ[Z|m] ω) / 2)])

/-- The actual conditional mean, indexed before the next episode. -/
noncomputable def predictableMean (ℱ : Filtration ℕ m0) (Z : ℕ → Ω → ℝ) (k : ℕ) : Ω → ℝ :=
  μ[Z k | ℱ k]

/-- The exponential process used to prove the predictable-to-realized bound. -/
noncomputable def exponentialProcess (ℱ : Filtration ℕ m0) (Z : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  Real.exp (∑ k ∈ Finset.range n, (predictableMean (μ := μ) ℱ Z k ω / 2 - Z k ω))

section Normalized

variable (ℱ : Filtration ℕ m0) (Z : ℕ → Ω → ℝ) (K : ℕ)
  (hZ : ∀ k < K, StronglyMeasurable[ℱ (k + 1)] (Z k))
  (hbound : ∀ k < K, ∀ᵐ ω ∂μ, 0 ≤ Z k ω ∧ Z k ω ≤ 1)

include hZ hbound

private theorem z_integrable (k : ℕ) (hk : k < K) : Integrable (Z k) μ :=
  integrable_unit_interval ((hZ k hk).mono (ℱ.le _)).aestronglyMeasurable (hbound k hk)

private theorem mean_bound (k : ℕ) (hk : k < K) :
    ∀ᵐ ω ∂μ, 0 ≤ predictableMean (μ := μ) ℱ Z k ω ∧
      predictableMean (μ := μ) ℱ Z k ω ≤ 1 :=
  condExp_unit_interval (ℱ.le k) (z_integrable ℱ Z K hZ hbound k hk) (hbound k hk)

private theorem partialSum_measurable (n : ℕ) (hn : n ≤ K) :
    StronglyMeasurable[ℱ n]
      (fun ω => ∑ k ∈ Finset.range n, (predictableMean (μ := μ) ℱ Z k ω / 2 - Z k ω)) := by
  apply Finset.stronglyMeasurable_fun_sum
  intro k hk
  have hkn : k < n := Finset.mem_range.mp hk
  simpa only [predictableMean, div_eq_mul_inv, one_div, one_mul, Pi.sub_apply] using
    (((stronglyMeasurable_condExp (μ := μ) (f := Z k) (m := ℱ k)).mono
      (ℱ.mono hkn.le)).mul_const (1 / 2 : ℝ)).sub
      ((hZ k (hkn.trans_le hn)).mono (ℱ.mono hkn))

private theorem process_integrable (n : ℕ) (hn : n ≤ K) :
    Integrable (exponentialProcess (μ := μ) ℱ Z n) μ := by
  have hmeas := (Real.continuous_exp.comp_stronglyMeasurable (partialSum_measurable ℱ Z K hZ hbound n hn)).mono (ℱ.le n)
  apply Integrable.of_bound hmeas.aestronglyMeasurable (Real.exp n)
  have hall : ∀ᵐ ω ∂μ, ∀ k < n,
      0 ≤ Z k ω ∧ Z k ω ≤ 1 ∧ predictableMean (μ := μ) ℱ Z k ω ≤ 1 := by
    apply (ae_all_iff).2
    intro k
    by_cases hk : k < n
    · filter_upwards [hbound k (hk.trans_le hn), mean_bound ℱ Z K hZ hbound k (hk.trans_le hn)]
        with ω hω hm
      exact fun _ => ⟨hω.1, hω.2, hm.2⟩
    · exact ae_of_all _ (fun _ h => False.elim (hk h))
  filter_upwards [hall] with ω hω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    (∑ k ∈ Finset.range n, (predictableMean (μ := μ) ℱ Z k ω / 2 - Z k ω)) ≤
        ∑ _k ∈ Finset.range n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      obtain ⟨hz, _, hm⟩ := hω k (Finset.mem_range.mp hk)
      linarith
    _ = n := by simp

/-- The terminal exponential moment is at most one. No moment bound is assumed. -/
theorem exponentialProcess_integral_le_one (n : ℕ) (hn : n ≤ K) :
    (∫ ω, exponentialProcess (μ := μ) ℱ Z n ω ∂μ) ≤ 1 := by
  induction n with
  | zero => simp [exponentialProcess]
  | succ n ih =>
    have hnK : n < K := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn
    have hnle : n ≤ K := hnK.le
    have hSn := partialSum_measurable (μ := μ) ℱ Z K hZ hbound n hnle
    let F : Ω → ℝ := fun ω => Real.exp
      ((∑ k ∈ Finset.range n, (predictableMean (μ := μ) ℱ Z k ω / 2 - Z k ω)) +
        predictableMean (μ := μ) ℱ Z n ω / 2)
    let G : Ω → ℝ := fun ω => Real.exp (-Z n ω)
    have hmmeas : StronglyMeasurable[ℱ n]
        (fun ω => predictableMean (μ := μ) ℱ Z n ω / 2) := by
      simpa only [predictableMean, div_eq_mul_inv, one_div, one_mul, Pi.sub_apply] using
        (stronglyMeasurable_condExp (μ := μ) (f := Z n) (m := ℱ n)).mul_const (1 / 2 : ℝ)
    have hFmeas : StronglyMeasurable[ℱ n] F :=
      Real.continuous_exp.comp_stronglyMeasurable (hSn.add hmmeas)
    have hprod : F * G = exponentialProcess (μ := μ) ℱ Z (n + 1) := by
      funext ω
      simp only [F, G, Pi.mul_apply, exponentialProcess, Finset.sum_range_succ]
      rw [← Real.exp_add]
      congr 1
      ring
    have hGi : Integrable G μ := by
      apply Integrable.of_bound (((hZ n hnK).mono (ℱ.le _)).neg.measurable.exp.aestronglyMeasurable) 1
      filter_upwards [hbound n hnK] with ω hω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hω.1)
    have hFGi : Integrable (F * G) μ := hprod ▸ process_integrable ℱ Z K hZ hbound (n+1) hn
    have hpull := condExp_mul_of_stronglyMeasurable_left hFmeas hFGi hGi
    have hce := condExp_exp_neg_le (ℱ.le n)
      ((hZ n hnK).mono (ℱ.le _)).aestronglyMeasurable (hbound n hnK)
    have hle : μ[F * G | ℱ n] ≤ᵐ[μ] exponentialProcess (μ := μ) ℱ Z n := by
      filter_upwards [hpull, hce] with ω hp hc
      rw [hp]
      calc
        F ω * (μ[G | ℱ n]) ω ≤ F ω * Real.exp (-predictableMean (μ := μ) ℱ Z n ω / 2) :=
          mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le
        _ = exponentialProcess (μ := μ) ℱ Z n ω := by
          simp only [F, exponentialProcess]
          rw [← Real.exp_add]
          congr 1
          ring
    calc
      ∫ ω, exponentialProcess (μ := μ) ℱ Z (n + 1) ω ∂μ = ∫ ω, (F * G) ω ∂μ := by rw [hprod]
      _ = ∫ ω, (μ[F * G | ℱ n]) ω ∂μ := (integral_condExp (ℱ.le n)).symm
      _ ≤ ∫ ω, exponentialProcess (μ := μ) ℱ Z n ω ∂μ :=
        integral_mono_ae integrable_condExp (process_integrable ℱ Z K hZ hbound n hnle) hle
      _ ≤ 1 := ih hnle

/-- Appendix C.3 for normalized observations, in exceptional-probability form. -/
theorem predictable_to_realized_unit {ell : ℝ} (hell : 0 < ell) :
    μ.real {ω | 2 * (∑ k ∈ Finset.range K, Z k ω) + 2 * ell <
      ∑ k ∈ Finset.range K, predictableMean (μ := μ) ℱ Z k ω} ≤ Real.exp (-ell) := by
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ fun ω => (Real.exp_pos _).le)
    (process_integrable ℱ Z K hZ hbound K le_rfl) (Real.exp ell)
  have hmoment := exponentialProcess_integral_le_one ℱ Z K hZ hbound K le_rfl
  have hprob : μ.real {ω | Real.exp ell ≤ exponentialProcess (μ := μ) ℱ Z K ω} ≤
      Real.exp (-ell) := by
    apply (mul_le_mul_left (Real.exp_pos ell)).mp
    calc
      Real.exp ell * μ.real {ω | Real.exp ell ≤ exponentialProcess (μ := μ) ℱ Z K ω} ≤ 1 :=
        hmarkov.trans hmoment
      _ = Real.exp ell * Real.exp (-ell) := by rw [← Real.exp_add]; simp
  apply le_trans ?_ hprob
  refine measureReal_mono ?_ (measure_ne_top μ _)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω
  apply Real.exp_le_exp.mpr
  dsimp [exponentialProcess]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div]
  linarith

end Normalized

/-- Appendix C.3 on an arbitrary probability space. The bound is the probability
of the exceptional event; equivalently, the displayed upper inequality holds
with probability at least `1 - exp (-ell)`. -/
theorem predictable_to_realized (ℱ : Filtration ℕ m0) (Z : ℕ → Ω → ℝ) (K : ℕ)
    {b ell : ℝ} (hb : 0 ≤ b) (hell : 0 < ell)
    (hZ : ∀ k < K, StronglyMeasurable[ℱ (k + 1)] (Z k))
    (hbound : ∀ k < K, ∀ᵐ ω ∂μ, 0 ≤ Z k ω ∧ Z k ω ≤ b) :
    μ.real {ω | 2 * (∑ k ∈ Finset.range K, Z k ω) + 2 * b * ell <
      ∑ k ∈ Finset.range K, predictableMean (μ := μ) ℱ Z k ω} ≤ Real.exp (-ell) := by
  by_cases hb0 : b = 0
  · have hz : ∀ k < K, Z k =ᵐ[μ] 0 := by
      intro k hk
      filter_upwards [hbound k hk] with ω hω
      simp only [Pi.zero_apply]
      rw [hb0] at hω
      linarith [hω.1, hω.2]
    have hm : ∀ k < K, predictableMean (μ := μ) ℱ Z k =ᵐ[μ] 0 := by
      intro k hk
      have h := condExp_congr_ae (m := ℱ k) (hz k hk)
      simpa only [predictableMean, condExp_zero] using h
    have hall : ∀ᵐ ω ∂μ, ∀ k, k < K →
        Z k ω = 0 ∧ predictableMean (μ := μ) ℱ Z k ω = 0 := by
      apply ae_all_iff.2
      intro k
      by_cases hk : k < K
      · filter_upwards [hz k hk, hm k hk] with ω hz hm
        exact fun _ => ⟨hz, hm⟩
      · exact ae_of_all _ (fun _ h => False.elim (hk h))
    have hempty :
        {ω | 2 * (∑ k ∈ Finset.range K, Z k ω) + 2 * b * ell <
          ∑ k ∈ Finset.range K, predictableMean (μ := μ) ℱ Z k ω} =ᵐ[μ] (∅ : Set Ω) := by
      filter_upwards [hall] with ω hω
      have hzsum : (∑ k ∈ Finset.range K, Z k ω) = 0 :=
        Finset.sum_eq_zero (fun k hk => (hω k (Finset.mem_range.mp hk)).1)
      have hmsum : (∑ k ∈ Finset.range K, predictableMean (μ := μ) ℱ Z k ω) = 0 :=
        Finset.sum_eq_zero (fun k hk => (hω k (Finset.mem_range.mp hk)).2)
      change ((2 * (∑ k ∈ Finset.range K, Z k ω) + 2 * b * ell <
        ∑ k ∈ Finset.range K, predictableMean (μ := μ) ℱ Z k ω) = False)
      simp [hzsum, hmsum, hb0]
    simp only [measureReal_def, measure_congr hempty, measure_empty, ENNReal.toReal_zero]
    exact (Real.exp_pos _).le
  · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    let Y : ℕ → Ω → ℝ := fun k ω => Z k ω / b
    have hY : ∀ k < K, StronglyMeasurable[ℱ (k + 1)] (Y k) := by
      intro k hk
      simpa only [Y, div_eq_mul_inv] using (hZ k hk).mul_const b⁻¹
    have hYbound : ∀ k < K, ∀ᵐ ω ∂μ, 0 ≤ Y k ω ∧ Y k ω ≤ 1 := by
      intro k hk
      filter_upwards [hbound k hk] with ω hω
      exact ⟨div_nonneg hω.1 hb, (div_le_one hbpos).mpr hω.2⟩
    have hunit := predictable_to_realized_unit (μ := μ) ℱ Y K hY hYbound hell
    have hmeans : ∀ᵐ ω ∂μ, ∀ k, predictableMean (μ := μ) ℱ Y k ω =
        predictableMean (μ := μ) ℱ Z k ω / b := by
      apply ae_all_iff.2
      intro k
      have hfun : b⁻¹ • Z k = fun ω => Z k ω / b := by
        funext ω
        simp [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
      have h := condExp_smul (μ := μ) b⁻¹ (Z k) (ℱ k)
      rw [hfun] at h
      filter_upwards [h] with ω hω
      simpa [predictableMean, Y, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm] using hω
    have hevent :
        {ω | 2 * (∑ k ∈ Finset.range K, Z k ω) + 2 * b * ell <
          ∑ k ∈ Finset.range K, predictableMean (μ := μ) ℱ Z k ω} ≤ᵐ[μ]
        {ω | 2 * (∑ k ∈ Finset.range K, Y k ω) + 2 * ell <
          ∑ k ∈ Finset.range K, predictableMean (μ := μ) ℱ Y k ω} := by
      filter_upwards [hmeans] with ω hm
      intro hω
      change 2 * (∑ k ∈ Finset.range K, Z k ω) + 2 * b * ell <
        ∑ k ∈ Finset.range K, predictableMean (μ := μ) ℱ Z k ω at hω
      change 2 * (∑ k ∈ Finset.range K, Y k ω) + 2 * ell <
        ∑ k ∈ Finset.range K, predictableMean (μ := μ) ℱ Y k ω
      rw [Finset.sum_congr rfl (fun k _ => hm k)]
      simp only [Y, ← Finset.sum_div]
      have h := (div_lt_div_iff_of_pos_right hbpos).mpr hω
      convert h using 1 <;> field_simp <;> ring
    exact (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hevent)).trans hunit

section PosteriorSymmetry

variable {History Model : Type*} [MeasurableSpace History] [MeasurableSpace Model]
  [StandardBorelSpace Model] [Nonempty Model]
  {history : Ω → History} {latent sampled : Ω → Model}

/-- Equal conditional posterior laws give equal joint laws with the observed history.
Conditional independence is stronger than needed for this conclusion. -/
theorem posterior_joint_identDistrib (hh : AEMeasurable history μ)
    (hl : AEMeasurable latent μ) (hs : AEMeasurable sampled μ)
    (hposterior : condDistrib latent history μ =ᵐ[μ.map history]
      condDistrib sampled history μ) :
    IdentDistrib (fun ω => (history ω, latent ω)) (fun ω => (history ω, sampled ω)) μ μ := by
  refine ⟨hh.prodMk hl, hh.prodMk hs, ?_⟩
  calc
    μ.map (fun ω => (history ω, latent ω)) =
        (μ.map history) ⊗ₘ condDistrib latent history μ := (compProd_map_condDistrib hl).symm
    _ = (μ.map history) ⊗ₘ condDistrib sampled history μ := Measure.compProd_congr hposterior
    _ = μ.map (fun ω => (history ω, sampled ω)) := compProd_map_condDistrib hs

/-- The conditional posterior identity applies to any integrable function of both
the history and kernel, including history-dependent Borel confidence sets. -/
theorem posterior_conditional_expectation (hh : Measurable history)
    (hl : AEMeasurable latent μ) (hs : AEMeasurable sampled μ)
    (hposterior : condDistrib latent history μ =ᵐ[μ.map history]
      condDistrib sampled history μ)
    {f : History × Model → ℝ} (hf : StronglyMeasurable f)
    (hfl : Integrable (fun ω => f (history ω, latent ω)) μ)
    (hfs : Integrable (fun ω => f (history ω, sampled ω)) μ) :
    μ[fun ω => f (history ω, sampled ω) | MeasurableSpace.comap history inferInstance] =ᵐ[μ]
      μ[fun ω => f (history ω, latent ω) | MeasurableSpace.comap history inferInstance] := by
  have hlce := condExp_prod_ae_eq_integral_condDistrib hh hl hf hfl
  have hsce := condExp_prod_ae_eq_integral_condDistrib hh hs hf hfs
  have hp := ae_of_ae_map hh.aemeasurable hposterior
  filter_upwards [hlce, hsce, hp] with ω hlce hsce hp
  rw [hlce, hsce, hp]

/-- Unconditional form of (C.4): a history-dependent Borel confidence event has
the same failure probability for the latent and sampled kernels. -/
theorem posterior_failure_probability (hh : AEMeasurable history μ)
    (hl : AEMeasurable latent μ) (hs : AEMeasurable sampled μ)
    (hposterior : condDistrib latent history μ =ᵐ[μ.map history]
      condDistrib sampled history μ)
    {C : Set (History × Model)} (hC : MeasurableSet C) :
    μ {ω | (history ω, sampled ω) ∉ C} = μ {ω | (history ω, latent ω) ∉ C} :=
  (posterior_joint_identDistrib hh hl hs hposterior).symm.measure_mem_eq hC.compl

/-- Posterior symmetry also matches expectations of measurable kernel/history
functionals; it supplies the per-episode symmetry term in the reward proof. -/
theorem posterior_expectation_eq (hh : AEMeasurable history μ)
    (hl : AEMeasurable latent μ) (hs : AEMeasurable sampled μ)
    (hposterior : condDistrib latent history μ =ᵐ[μ.map history]
      condDistrib sampled history μ)
    {f : History × Model → ℝ} (hf : Measurable f) :
    (∫ ω, f (history ω, latent ω) ∂μ) = ∫ ω, f (history ω, sampled ω) ∂μ :=
  ((posterior_joint_identDistrib hh hl hs hposterior).comp hf).integral_eq

end PosteriorSymmetry

/-- Weighted tower identity underlying (C.8). The actual identification of a
trajectory's conditional visit count with its nominal occupancy is separate. -/
theorem weighted_conditional_expectation {m : MeasurableSpace Ω} (hm : m ≤ m0)
    {count weight : Ω → ℝ} (hw : StronglyMeasurable[m] weight)
    (hc : Integrable count μ) (hwc : Integrable (weight * count) μ) :
    (∫ ω, weight ω * (μ[count|m]) ω ∂μ) = ∫ ω, weight ω * count ω ∂μ := by
  have hpull := condExp_mul_of_stronglyMeasurable_left hw hwc hc
  calc
    ∫ ω, weight ω * (μ[count|m]) ω ∂μ = ∫ ω, (μ[weight * count|m]) ω ∂μ :=
      integral_congr_ae hpull.symm
    _ = ∫ ω, weight ω * count ω ∂μ := integral_condExp hm

/-- Episode-start count, with all visits in one episode charged at the same count. -/
def countBefore (visits : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, visits k

/-- The low-count charge for one row is strictly less than `2H`, including an
entire final episode whose start count is below `H`. -/
theorem frozen_low_count_charge (visits : ℕ → ℕ) {H : ℕ} (hH : 0 < H)
    (hvisits : ∀ k, visits k ≤ H) (K : ℕ) :
    (∑ k ∈ Finset.range K, if countBefore visits k < H then visits k else 0) < 2 * H := by
  have hinv : ∀ n : ℕ,
      (countBefore visits n < H →
        (∑ k ∈ Finset.range n, if countBefore visits k < H then visits k else 0) =
          countBefore visits n) ∧
      (H ≤ countBefore visits n →
        (∑ k ∈ Finset.range n, if countBefore visits k < H then visits k else 0) < 2 * H) := by
    intro n
    induction n with
    | zero => simp [countBefore, hH]
    | succ n ih =>
      have hrec : countBefore visits (n+1) = countBefore visits n + visits n := by
        simp only [countBefore, Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      by_cases hn : countBefore visits n < H
      · rw [if_pos hn, ih.1 hn]
        constructor
        · intro _
          exact hrec.symm
        · intro _
          have hv := hvisits n
          omega
      · rw [if_neg hn, add_zero]
        constructor
        · intro hnext
          omega
        · intro _
          exact ih.2 (Nat.le_of_not_gt hn)
  by_cases hlast : countBefore visits K < H
  · rw [(hinv K).1 hlast]
    omega
  · exact (hinv K).2 (Nat.le_of_not_gt hlast)

/-- The high-count logarithmic potential step used after (C.8) and in (C.12). -/
theorem frozen_count_log_step {N n : ℝ} (hN : 0 < N) (hn : 0 ≤ n) (hnN : n ≤ N) :
    n / N ≤ 2 * Real.log ((N + n) / N) := by
  let t := n / N
  have ht0 : 0 ≤ t := div_nonneg hn hN.le
  have ht1 : t ≤ 1 := (div_le_one hN).mpr hnN
  have hp : 0 < t + 2 := by linarith
  have hfrac : t / 2 ≤ 2 * t / (t + 2) := by
    apply (le_div_iff₀ hp).mpr
    nlinarith
  have hlog := Real.le_log_one_add_of_nonneg ht0
  have heq : (N + n) / N = 1 + t := by
    dsimp [t]
    field_simp
  rw [heq]
  change t ≤ 2 * Real.log (1 + t)
  linarith

/-- The square-root potential step in the reward simulation proof (Appendix C). -/
theorem frozen_count_sqrt_step {N n : ℝ} (hN : 0 < N) (hn : 0 ≤ n) (hnN : n ≤ N) :
    n / Real.sqrt N ≤ 3 * (Real.sqrt (N + n) - Real.sqrt N) := by
  have ha := Real.sqrt_nonneg N
  have hb := Real.sqrt_nonneg (N + n)
  have hasq := Real.sq_sqrt hN.le
  have hbsq := Real.sq_sqrt (show 0 ≤ N + n by linarith)
  have hab : Real.sqrt N ≤ Real.sqrt (N + n) := Real.sqrt_le_sqrt (by linarith)
  have hb2 : Real.sqrt (N + n) ≤ 2 * Real.sqrt N := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith
  have hprod := mul_le_mul_of_nonneg_left (show
    Real.sqrt (N + n) + Real.sqrt N ≤ 3 * Real.sqrt N by linarith)
    (sub_nonneg.mpr hab)
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hN)).mpr
  nlinarith

end Paper36.Posterior
