import Paper08.FPTASAlgorithm
import Paper08.EfficientIdentity

/-! # Correctness of the constructed rational FPTAS

This module keeps common nonvanishing explicit in its reusable conditional
algorithm lemmas. CubeZeroFreeMain proves it from original model promises,
and OriginalTheorems publishes the resulting original-hypothesis contracts.
Every subsequent coefficient, quadrature, rounding, recurrence, support sum,
parameter choice, and final output is the actual program from Section 4.
-/
noncomputable section
open scoped BigOperators
open Metric
set_option maxHeartbeats 1200000
namespace Paper08.FPTASCorrectness
open FPTASAlgorithm

lemma signed_error (a b : ℝ) (k : ℕ) :
    |(-1 : ℝ)^k * a - (-1 : ℝ)^k * b| = |a-b| := by
  rw [← mul_sub, abs_mul]
  simp

/-- The finite support-subset assembly has the actual pair-count error,
including the alternating signs of support extraction. -/
theorem pair_sum_error {n m r c s p : ℕ} (scopes : Fin m → Finset (Fin n))
    (a b : Finset (Fin m) → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (herr : ∀ AB ∈ pairs scopes r c s p, |a AB.2-b AB.2| ≤ δ) :
    |(∑ AB ∈ pairs scopes r c s p, (-1 : ℝ)^(AB.1.card-AB.2.card)*a AB.2) -
      ∑ AB ∈ pairs scopes r c s p, (-1 : ℝ)^(AB.1.card-AB.2.card)*b AB.2| ≤
        (m * (8 * degreeBound r c)^s : ℕ) * δ := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ AB ∈ pairs scopes r c s p,
        |(-1 : ℝ)^(AB.1.card-AB.2.card)*a AB.2 -
          (-1 : ℝ)^(AB.1.card-AB.2.card)*b AB.2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _AB ∈ pairs scopes r c s p, δ := by
      apply Finset.sum_le_sum
      intro AB hAB
      rw [signed_error]
      exact herr AB hAB
    _ = (pairs scopes r c s p).card * δ := by simp
    _ ≤ (m * (8 * degreeBound r c)^s : ℕ) * δ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast pairs_card scopes) hδ

/-- Certified *fixed parameter bounds*, as supplied in Assumption 1.1.
No accuracy statement or program-output certificate is stored here. -/
structure FixedBounds (p : FPTAS.Params) (fixed : Parameters.Fixed) : Prop where
  q_upper : p.q ≤ (fixed.qPlus : ℝ)
  radius : (fixed.R : ℝ) < FPTAS.beta p
  supports : 8 * degreeBound p.r p.c ≤ fixed.A0
  stability : 4 * Real.exp (Coeff.kappa (fixed.R : ℝ) p.q) ≤ (fixed.F : ℝ)
  budget_two : 2 ≤ fixed.C
  budget_range : 2 * p.q ≤ (fixed.C : ℝ)
  budget_lip : 6 * Real.sqrt p.r * p.K ≤ (fixed.C : ℝ)

/-- The common-disk property used by the conditional analytic algorithm.
It is proved from original model promises in CubeZeroFreeMain. -/
def CommonNonvanishing {n m : ℕ} (p : FPTAS.Params) (E : FactorFamily n p.r m) : Prop :=
  ∀ B : Finset (Fin m), ∀ z ∈ ball (0 : ℂ) (FPTAS.beta p), ZeroFree.Q E B z ≠ 0

/-- The actually assembled rational approximation of log Z has coefficient
error at most the middle ε/3 budget. -/
theorem logApprox_error {n m : ℕ} (p : FPTAS.Params) (fixed : Parameters.Fixed)
    (hb : FixedBounds p fixed) (E : FactorFamily n p.r m)
    (O : (e : Fin m) → Oracle.Oracle (E e).scope.card (E e).psi.toFun)
    (hc : FamilyBoundedOccurrence E p.c)
    (hE : ∀ e, (E e).RangeOk p.q) (hLip : ∀ e, (E e).LipOk p.K)
    (hne : CommonNonvanishing p E) {ε : ℚ} (hm : 1 ≤ m)
    (hε : 0 < ε) (hεu : ε ≤ 1/2) :
    let s := Parameters.truncationOrder fixed m ε
    let τ := Parameters.primitiveTolerance fixed m ε
    |(logApprox (fun e => (E e).scope) (fun e => (O e).query) p.r p.c s fixed.C τ : ℝ) -
      ∑ j ∈ Finset.Icc 1 s, ModelSupport.logCoeff E Finset.univ j| ≤ (ε : ℝ)/3 := by
  let s := Parameters.truncationOrder fixed m ε
  let τ := Parameters.primitiveTolerance fixed m ε
  let δ : ℝ := (fixed.F : ℝ)^s * (4^s * (τ : ℝ))
  have hs := Parameters.truncationOrder_pos fixed m ε
  have hτ := Parameters.primitiveTolerance_pos fixed hm hε
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hR : (1 : ℝ) < fixed.R := by exact_mod_cast fixed.R_gt_one
  have hprec : (4 : ℝ)^s * (τ : ℝ) ≤ ((fixed.F : ℝ)^s)⁻¹ := by
    have hh := Parameters.primitiveTolerance_stability_real fixed hm hε hεu
    dsimp only at hh
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ fixed.F), Real.rpow_natCast] at hh
    exact hh
  have hlocal : ∀ j ∈ Finset.Icc 1 s, ∀ AB ∈ pairs (fun e => (E e).scope) p.r p.c s j,
      |(localCoeff (fun e => (E e).scope) (fun e => (O e).query) AB.2 j s fixed.C τ : ℝ) -
        ModelSupport.logCoeff E AB.2 j| ≤ δ := by
    intro j hj AB hAB
    have hpair := pair_subset (fun e => (E e).scope) hAB
    exact localCoeff_error E O AB.2 ((Finset.card_le_card hpair.1).trans hpair.2)
      (Finset.mem_Icc.mp hj).2 hs p.q_pos (FPTAS.q_lt_third p) p.K_pos.le hR hb.radius
      hE hLip (hne AB.2) hb.budget_two hb.budget_range hb.budget_lip hb.stability τ hτ hprec
  have heq : (∑ j ∈ Finset.Icc 1 s, ModelSupport.logCoeff E Finset.univ j) =
      ∑ j ∈ Finset.Icc 1 s,
        ∑ AB ∈ pairs (fun e => (E e).scope) p.r p.c s j,
          (-1 : ℝ)^(AB.1.card-AB.2.card) * ModelSupport.logCoeff E AB.2 j := by
    apply Finset.sum_congr rfl
    intro j hj
    -- Executable candidates cover all connected supports; every extra
    -- disconnected or excessive-degree contribution is proved to vanish.
    exact EfficientIdentity.factor_pairs_identity E hc (Finset.mem_Icc.mp hj).2
  dsimp only
  rw [heq]
  simp only [logApprox, Rat.cast_sum, Rat.cast_mul, Rat.cast_pow, Rat.cast_neg, Rat.cast_one]
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ Finset.Icc 1 s,
        |(∑ AB ∈ pairs (fun e => (E e).scope) p.r p.c s j,
          (-1 : ℝ)^(AB.1.card-AB.2.card) *
            (localCoeff (fun e => (E e).scope) (fun e => (O e).query) AB.2 j s fixed.C τ : ℝ)) -
         ∑ AB ∈ pairs (fun e => (E e).scope) p.r p.c s j,
          (-1 : ℝ)^(AB.1.card-AB.2.card) * ModelSupport.logCoeff E AB.2 j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.Icc 1 s, (m * fixed.A0^s : ℕ) * δ := by
      apply Finset.sum_le_sum
      intro j hj
      apply (pair_sum_error (r := p.r) (c := p.c) (s := s) (p := j)
        (fun e => (E e).scope)
        (fun B => (localCoeff (fun e => (E e).scope) (fun e => (O e).query) B j s fixed.C τ : ℝ))
        (fun B => ModelSupport.logCoeff E B j) hδ (hlocal j hj)).trans
      apply mul_le_mul_of_nonneg_right _ hδ
      exact_mod_cast Nat.mul_le_mul_left m (Nat.pow_le_pow_left hb.supports s)
    _ = (s : ℝ) * m * (fixed.A0 : ℝ)^s * (fixed.F : ℝ)^s * 4^s * (τ : ℝ) := by
      simp [δ, Nat.card_Icc, mul_assoc]
    _ = (ε : ℝ)/3 := Parameters.primitiveTolerance_errorBudget_real fixed hm hε


/-- The actual Taylor truncation uses the rational order selected by the
program and the certified rational upper bound on q. -/
theorem truncation_error {n m : ℕ} (p : FPTAS.Params) (fixed : Parameters.Fixed)
    (hb : FixedBounds p fixed) (E : FactorFamily n p.r m)
    (hE : ∀ e, (E e).RangeOk p.q) (hLip : ∀ e, (E e).LipOk p.K)
    (hne : CommonNonvanishing p E) {ε : ℚ} (hε : 0 < ε) :
    let s := Parameters.truncationOrder fixed m ε
    |(∑ j ∈ Finset.Icc 1 s, ModelSupport.logCoeff E Finset.univ j) -
      Real.log (Integral.partitionFunctionFactor E)| ≤ (ε : ℝ)/3 := by
  classical
  let s := Parameters.truncationOrder fixed m ε
  have hR : (1 : ℝ) < fixed.R := by exact_mod_cast fixed.R_gt_one
  have hRp : (0 : ℝ) < fixed.R := by linarith
  have hZ : 0 < Integral.partitionFunctionFactor E := by
    have hh := ZeroFree.Q_real_pos E Finset.univ (fun e _ => hE e) (fun e _ => hLip e) 1
    simpa only [Complex.ofReal_one, ZeroFree.Q_one_eq_partitionFunction E hE,
      Complex.ofReal_re] using hh
  have hnorm : ‖ZeroFree.Q E Finset.univ 1‖ = Integral.partitionFunctionFactor E := by
    rw [ZeroFree.Q_one_eq_partitionFunction E hE, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZ]
  have hzero : ModelSupport.logCoeff E Finset.univ 0 = 0 := by
    rw [LogRecurrence.model_logCoeff_eq_realOutput E Finset.univ
      (fun e _ => hE e) (fun e _ => hLip e)]
    exact (LogRecurrence.realOutput_recurrence _).1
  have hrange : (∑ j ∈ Finset.range (s+1), ModelSupport.logCoeff E Finset.univ j) =
      ∑ j ∈ Finset.Icc 1 s, ModelSupport.logCoeff E Finset.univ j := by
    symm
    apply Finset.sum_subset
    · intro j hj
      exact Finset.mem_range.mpr (by have := Finset.mem_Icc.mp hj; omega)
    · intro j hj hjnot
      have hj0 : j = 0 := by
        have := Finset.mem_range.mp hj
        simp only [Finset.mem_Icc, not_and_or, not_le] at hjnot
        omega
      simpa [hj0] using hzero
  have htail := LogRecurrence.model_logCoeff_truncation E Finset.univ p.q_pos.le hR hb.radius
    (fun e _ => hE e) (fun e _ => hLip e) (hne Finset.univ) s
  rw [hnorm, hrange, Finset.card_univ, Fintype.card_fin] at htail
  have hbq : (2 * (fixed.R : ℝ) * m * (fixed.qPlus : ℝ) / ((fixed.R : ℝ)-1)) /
      (fixed.R : ℝ)^s ≤ (ε : ℝ)/3 := by
    exact_mod_cast Parameters.truncationOrder_sufficient fixed m ε hε
  dsimp only
  rw [abs_sub_comm]
  apply htail.trans
  calc
    _ ≤ (2 * (fixed.R : ℝ) * m * (fixed.qPlus : ℝ) / ((fixed.R : ℝ)-1)) *
        (fixed.R : ℝ)⁻¹^s := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (inv_nonneg.mpr hRp.le) s)
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hb.q_upper (by positivity)) (by linarith)
    _ = (2 * (fixed.R : ℝ) * m * (fixed.qPlus : ℝ) / ((fixed.R : ℝ)-1)) /
        (fixed.R : ℝ)^s := by simp only [inv_pow, div_eq_mul_inv]
    _ ≤ (ε : ℝ)/3 := hbq

/-- Conditional accuracy for the constructed rational program. The public
OriginalTheorems.execute_correct discharges the common-disk premise. -/
theorem run_correct_of_common_nonvanishing {n m : ℕ} (p : FPTAS.Params)
    (fixed : Parameters.Fixed) (hb : FixedBounds p fixed) (E : FactorFamily n p.r m)
    (O : (e : Fin m) → Oracle.Oracle (E e).scope.card (E e).psi.toFun)
    (hc : FamilyBoundedOccurrence E p.c)
    (hE : ∀ e, (E e).RangeOk p.q) (hLip : ∀ e, (E e).LipOk p.K)
    (hne : CommonNonvanishing p E) {ε : ℚ} (hε : 0 < ε) (hεu : ε ≤ 1/2) :
    FPTAS.Accurate
      (run fixed (fun e => (E e).scope) (fun e => (O e).query) p.r p.c ε : ℝ)
      (Integral.partitionFunctionFactor E) (ε : ℝ) := by
  classical
  by_cases hm0 : m = 0
  · subst m
    have hZ : Integral.partitionFunctionFactor E = 1 := by
      simp [Integral.partitionFunctionFactor, Integral.partitionFunction]
    simp [run, hZ, FPTAS.Accurate, hε.le]
  have hm : 1 ≤ m := by omega
  let s := Parameters.truncationOrder fixed m ε
  let τ := Parameters.primitiveTolerance fixed m ε
  let L := logApprox (fun e => (E e).scope) (fun e => (O e).query) p.r p.c s fixed.C τ
  have hmid := logApprox_error p fixed hb E O hc hE hLip hne hm hε hεu
  have htail := truncation_error p fixed hb E hE hLip hne hε
  have hexp := Algorithm.rationalExp_spec L ε hε hεu
  have hZ : 0 < Integral.partitionFunctionFactor E := by
    have hh := ZeroFree.Q_real_pos E Finset.univ (fun e _ => hE e) (fun e _ => hLip e) 1
    simpa only [Complex.ofReal_one, ZeroFree.Q_one_eq_partitionFunction E hE,
      Complex.ofReal_re] using hh
  refine ⟨hZ, ?_, ?_⟩
  · simpa only [run, if_neg hm0] using (show (0 : ℝ) < Algorithm.rationalExp L ε by
      exact_mod_cast hexp.1)
  · simp only [run, if_neg hm0]
    exact Coeff.three_term_split hexp.2 hmid htail

/-- The original multiplicative accuracy conclusion, for this exact program. -/
theorem run_exp_bounds {n m : ℕ} (p : FPTAS.Params) (fixed : Parameters.Fixed)
    (hb : FixedBounds p fixed) (E : FactorFamily n p.r m)
    (O : (e : Fin m) → Oracle.Oracle (E e).scope.card (E e).psi.toFun)
    (hc : FamilyBoundedOccurrence E p.c)
    (hE : ∀ e, (E e).RangeOk p.q) (hLip : ∀ e, (E e).LipOk p.K)
    (hne : CommonNonvanishing p E) {ε : ℚ} (hε : 0 < ε) (hεu : ε ≤ 1/2) :
    Real.exp (-(ε : ℝ)) ≤
      (run fixed (fun e => (E e).scope) (fun e => (O e).query) p.r p.c ε : ℝ) /
        Integral.partitionFunctionFactor E ∧
    (run fixed (fun e => (E e).scope) (fun e => (O e).query) p.r p.c ε : ℝ) /
        Integral.partitionFunctionFactor E ≤ Real.exp (ε : ℝ) :=
  FPTAS.accurate_exp_form (run_correct_of_common_nonvanishing p fixed hb E O hc hE hLip hne hε hεu)


/-- The original model has 0≤log Z≤m q, without using a zero-free theorem. -/
theorem partition_log_range {n r m : ℕ} (E : FactorFamily n r m) {q K : ℝ}
    (hE : ∀ e, (E e).RangeOk q) (hLip : ∀ e, (E e).LipOk K) :
    0 ≤ Real.log (Integral.partitionFunctionFactor E) ∧
      Real.log (Integral.partitionFunctionFactor E) ≤ m*q := by
  let f := fun x => Real.exp (ZeroFree.sumEll E Finset.univ x)
  have hInt : MeasureTheory.IntegrableOn f (Integral.cube n) :=
    (Real.continuous_exp.comp_continuousOn
      (ZeroFree.continuousOn_sumEll E Finset.univ (fun e _ => hE e) (fun e _ => hLip e))).integrableOn_compact
        (ZeroFree.isCompact_cube n)
  have heq : Integral.cubeIntegral f = Integral.partitionFunctionFactor E := by
    apply Complex.ofReal_injective
    have hh := (ZeroFree.Q_real E Finset.univ 1).symm.trans
      (by simpa only [Complex.ofReal_one] using ZeroFree.Q_one_eq_partitionFunction E hE)
    simpa only [f, one_mul] using hh
  have hlo : 1 ≤ Integral.partitionFunctionFactor E := by
    rw [← heq]
    apply Integral.le_cubeIntegral hInt
    intro x hx
    exact Real.one_le_exp_iff.mpr (ZeroFree.sumEll_range E Finset.univ (fun e _ => hE e) hx).1
  have hpos : 0 < Integral.partitionFunctionFactor E := by linarith
  refine ⟨Real.log_nonneg hlo, ?_⟩
  have hu := ZeroFree.norm_Q_le E Finset.univ (fun e _ => hE e) 1
  rw [ZeroFree.Q_one_eq_partitionFunction E hE, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hpos] at hu
  simp only [norm_one, Finset.card_univ, Fintype.card_fin, one_mul] at hu
  exact (Real.log_le_log hpos hu).trans_eq (Real.log_exp _)

/-- The computed argument of the final exponential is only linear in m,
so the scaling power in the actual rational exponentiation is polynomial. -/
theorem logApprox_abs_le {n m : ℕ} (p : FPTAS.Params) (fixed : Parameters.Fixed)
    (hb : FixedBounds p fixed) (E : FactorFamily n p.r m)
    (O : (e : Fin m) → Oracle.Oracle (E e).scope.card (E e).psi.toFun)
    (hc : FamilyBoundedOccurrence E p.c)
    (hE : ∀ e, (E e).RangeOk p.q) (hLip : ∀ e, (E e).LipOk p.K)
    (hne : CommonNonvanishing p E) {ε : ℚ} (hm : 1 ≤ m)
    (hε : 0 < ε) (hεu : ε ≤ 1/2) :
    |(logApprox (fun e => (E e).scope) (fun e => (O e).query) p.r p.c
      (Parameters.truncationOrder fixed m ε) fixed.C
      (Parameters.primitiveTolerance fixed m ε) : ℝ)| ≤ m*p.q+1 := by
  have hmid := logApprox_error p fixed hb E O hc hE hLip hne hm hε hεu
  have htail := truncation_error p fixed hb E hE hLip hne hε
  dsimp only at hmid htail
  have herr := (abs_sub_le _ _ _).trans (add_le_add hmid htail)
  have hz := partition_log_range E hE hLip
  have heR : (ε : ℝ) ≤ 1/2 := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hεu
    norm_num at hh
    exact hh
  have hlower := abs_le.mp herr
  rw [abs_le]
  constructor <;> linarith

end Paper08.FPTASCorrectness
