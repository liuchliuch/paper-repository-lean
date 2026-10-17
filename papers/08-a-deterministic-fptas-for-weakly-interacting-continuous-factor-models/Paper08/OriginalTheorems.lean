import Paper08.CubeZeroFreeMain
import Paper08.FullCorollary

/-! # The original main theorem and primal-degree corollary

The actual finite-cube nonvanishing theorem is proved from the original
factor promises and supplied internally to the verified rational algorithm.
These public contracts contain no model-specific nonvanishing assumption.
-/
noncomputable section
open scoped BigOperators
namespace Paper08.OriginalTheorems
open FullAlgorithm

/-- Accuracy of the actual implemented answer in every dimension, obtained
from the original factor promises. -/
theorem execute_correct {n m : ℕ} (p : FPTAS.Params) (fixed : Parameters.Fixed)
    (hb : FPTASCorrectness.FixedBounds p fixed) (E : FactorFamily n p.r m)
    (O : (e : Fin m) → Oracle.Oracle (E e).scope.card (E e).psi.toFun)
    (hc : FamilyBoundedOccurrence E p.c)
    (hE : ∀ e, (E e).RangeOk p.q) (hLip : ∀ e, (E e).LipOk p.K)
    {ε : ℚ} (hε : 0 < ε) (hεu : ε ≤ 1/2) :
    FPTAS.Accurate
      ((FullAlgorithm.execute fixed (fun e => (E e).scope)
        (fun e => (O e).query) p.r p.c ε).1 : ℝ)
      (Integral.partitionFunctionFactor E) (ε : ℝ) :=
  FullAlgorithm.execute_correct p fixed hb E O hc hE hLip
    (CubeZeroFreeMain.common_nonvanishing p E hc hE hLip) hε hεu

/-- Theorem 1.2 from exactly the original weak-interaction, range, Lipschitz,
occurrence and effective-access input promises. The exponent is uniform in
all oracle polynomial degrees and all model inputs. -/
theorem theorem_1_2 (p : FPTAS.Params) :
    ∃ fixed : Parameters.Fixed, FPTASCorrectness.FixedBounds p fixed ∧
      ∃ C : ℕ, ∀ A degree : ℕ, ∃ B D : ℕ, 0 < B ∧
        ∀ {n m L : ℕ} (E : FactorFamily n p.r m) (labels : Fin m → ℕ)
        (O : (e : Fin m) → EffectiveAccess.Oracle (E e).scope.card (E e).psi.toFun A degree (labels e))
        (_hlabels : ∀ e, labels e ≤ L) (_hc : FamilyBoundedOccurrence E p.c)
        (_hE : ∀ e, (E e).RangeOk p.q) (_hLip : ∀ e, (E e).LipOk p.K)
        {ε : ℚ}
        (_hn : 1 ≤ n) (_hε : 0 < ε) (_hεu : ε ≤ 1/2)
        (_hbits : BitComplexity.rationalBits ε ≤ L),
        FPTAS.Accurate
          ((execute fixed (fun e => (E e).scope) (fun e => (O e).valueOracle.query) p.r p.c ε).1 : ℝ)
          (Integral.partitionFunctionFactor E) (ε : ℝ) ∧
        ((FPTASCost.runWithCost fixed (fun e => (E e).scope)
          (fun e => (O e).valueOracle.query) p.r p.c ε).2 : ℚ) ≤ ((n:ℚ)/ε)^C ∧
        (1 ≤ m → Parameters.level fixed m ε ≤ C*Parameters.inputLog n ε ∧
          Parameters.precision fixed m ε ≤ C*Parameters.inputLog n ε) ∧
        ((execute fixed (fun e => (E e).scope) (fun e => (O e).valueOracle.query) p.r p.c ε).2 : ℚ) ≤
          (B:ℚ)*((L:ℚ)+1)^D*((n:ℚ)/ε)^C ∧
        (totalWork fixed (fun e => (E e).scope) (fun e => (E e).psi.toFun)
          labels O p.r p.c ε : ℚ) ≤ (B:ℚ)*((L:ℚ)+1)^D*((n:ℚ)/ε)^C := by
  obtain ⟨fixed, hb, C, hp⟩ := FullAlgorithm.theorem_1_2_uniform p
  refine ⟨fixed, hb, C, ?_⟩
  intro A degree
  obtain ⟨B, D, hB, hp⟩ := hp A degree
  refine ⟨B, D, hB, ?_⟩
  intro n m L E labels O hlabels hc hE hLip ε hn hε hεu hbits
  exact hp E labels O hlabels hc hE hLip
    (CubeZeroFreeMain.common_nonvanishing p E hc hE hLip) hn hε hεu hbits

/-- Corollary 1.3 for η≥2 from the original primal-degree model, preserving
its actual integral and oracle handles, with no extra nonvanishing input. -/
theorem corollary_1_3_ge_two {Δ η : ℕ} {k δ : ℝ}
    (hΔ : 1 ≤ Δ) (hη : 2 ≤ η) (hk : 0 < k) (hδ : 0 < δ ∧ δ < 1)
    (hρ : 1 < FPTAS.gamarnikSmediraRho Δ η δ) :
    let p := FPTAS.Params.ofGamarnikSmedira hΔ hη hk hδ hρ
    ∃ fixed : Parameters.Fixed, FPTASCorrectness.FixedBounds p fixed ∧
      ∃ C : ℕ, ∀ A degree : ℕ, ∃ B D : ℕ, 0 < B ∧
        ∀ {n r m L : ℕ} (E : FactorFamily n r m) (labels : Fin m → ℕ)
        (O : (e : Fin m) → EffectiveAccess.Oracle (E e).scope.card (E e).psi.toFun A degree (labels e))
        (_hlabels : ∀ e, labels e ≤ L) (_hdegree : FamilyPrimalDegreeLe E η)
        (_hocc : FamilyBoundedOccurrence E Δ)
        (_hrange : ∀ e x, x ∈ Integral.cube (E e).scope.card →
          1 ≤ (E e).psi.toFun x ∧ (E e).psi.toFun x ≤ FPTAS.gamarnikSmediraRho Δ η δ)
        (_hLip : ∀ e, (E e).LipOk k)
        {ε : ℚ} (_hn : 1 ≤ n) (_hε : 0 < ε) (_hεu : ε ≤ 1/2)
        (_hbits : BitComplexity.rationalBits ε ≤ L),
        FPTAS.Accurate
          ((FullAlgorithm.execute fixed (fun e => (E e).scope)
            (fun e => (O e).valueOracle.query) (η+1) Δ ε).1 : ℝ)
          (Integral.partitionFunctionFactor E) (ε : ℝ) ∧
        ((FPTASCost.runWithCost fixed (fun e => (E e).scope)
          (fun e => (O e).valueOracle.query) (η+1) Δ ε).2 : ℚ) ≤ ((n:ℚ)/ε)^C ∧
        (1 ≤ m → Parameters.level fixed m ε ≤ C*Parameters.inputLog n ε ∧
          Parameters.precision fixed m ε ≤ C*Parameters.inputLog n ε) ∧
        ((FullAlgorithm.execute fixed (fun e => (E e).scope)
          (fun e => (O e).valueOracle.query) (η+1) Δ ε).2 : ℚ) ≤
          (B:ℚ)*((L:ℚ)+1)^D*((n:ℚ)/ε)^C ∧
        (FullAlgorithm.totalWork fixed (fun e => (E e).scope) (fun e => (E e).psi.toFun)
          labels O (η+1) Δ ε : ℚ) ≤ (B:ℚ)*((L:ℚ)+1)^D*((n:ℚ)/ε)^C := by
  let p := FPTAS.Params.ofGamarnikSmedira hΔ hη hk hδ hρ
  obtain ⟨fixed,hb,C,hprogram⟩ := theorem_1_2 p
  refine ⟨fixed,hb,C,?_⟩
  intro A degree
  obtain ⟨B,D,hB,hprogram⟩ := hprogram A degree
  refine ⟨B,D,hB,?_⟩
  intro n r m L E labels O hlabels hdegree hocc hrange hLip ε hn hε hεu hbits
  let E' := PrimalArity.rebound E hdegree
  have hE : ∀ e, (E' e).RangeOk p.q := by
    intro e
    constructor
    · intro x hx
      have hh := hrange e x (Integral.mem_cube.mpr hx)
      change |(E e).psi.toFun x| ≤ Real.exp (Real.log (FPTAS.gamarnikSmediraRho Δ η δ))
      rw [Real.exp_log (by linarith : 0 < FPTAS.gamarnikSmediraRho Δ η δ),
        abs_of_nonneg (by linarith : 0 ≤ (E e).psi.toFun x)]
      exact hh.2
    · intro x hx
      exact (hrange e x (Integral.mem_cube.mpr hx)).1
  have hocc' : FamilyBoundedOccurrence E' p.c := hocc
  have hlip' : ∀ e, (E' e).LipOk p.K := hLip
  exact hprogram E' labels O hlabels hocc' hE hlip' hn hε hεu hbits


/-- Lemma 2.2: an actual normalized analytic logarithm, coefficient bounds,
Taylor truncation and half-disk lower bounds, from the original input alone. -/
theorem lemma_2_2 {n m : ℕ} (p : FPTAS.Params) (E : FactorFamily n p.r m)
    (hc : FamilyBoundedOccurrence E p.c)
    (hE : ∀ e, (E e).RangeOk p.q) (hLip : ∀ e, (E e).LipOk p.K)
    (B : Finset (Fin m)) {R : ℝ} (hR : 1 < R) (hRβ : R < FPTAS.beta p) :
    ∃ L : ℂ → ℂ, L 0 = 0 ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) R, DifferentiableAt ℂ L z) ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) R, Complex.exp (L z) = ZeroFree.Q E B z) ∧
      (∀ j : ℕ, 1 ≤ j → ‖Analytic.cauchyCoeff L R j‖ ≤
        2 * R * B.card * p.q * R⁻¹ ^ j) ∧
      (∀ s : ℕ, ‖L 1 - ∑ p ∈ Finset.range (s + 1), Analytic.cauchyCoeff L R p‖ ≤
        (2 * R * B.card * p.q / (R - 1)) * R⁻¹ ^ s) ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 / 2 → ‖L z‖ ≤ Coeff.kappa R p.q * B.card ∧
        Real.exp (-(Coeff.kappa R p.q * B.card)) ≤ ‖ZeroFree.Q E B z‖) :=
  Coeff.analytic_bounds_Q_of_nonvanishing E B p.q_pos.le hR hRβ
    (fun e _ => hE e) (fun e _ => hLip e)
    (CubeZeroFreeMain.common_nonvanishing p E hc hE hLip B)

/-- The actual local moment recurrence form of Lemma 4.1, with its analytic
nonvanishing dependency discharged from the original model conditions. -/
theorem lemma_4_1 {n m : ℕ} (p : FPTAS.Params) (E : FactorFamily n p.r m)
    (hc : FamilyBoundedOccurrence E p.c)
    (hE : ∀ e, (E e).RangeOk p.q) (hLip : ∀ e, (E e).LipOk p.K)
    (B : Finset (Fin m)) {R F ξ : ℝ} {s j : ℕ}
    (hR : 1 < R) (hRβ : R < FPTAS.beta p)
    (hB : B.card ≤ s) (hs : 1 ≤ s) (hj : j ≤ s)
    (hF : 4 * Real.exp (Coeff.kappa R p.q) ≤ F)
    (hprecision : ξ ≤ (F ^ s)⁻¹) (Mtilde : ℕ → ℝ) (hMt : Mtilde 0 = 1)
    (herrors : ∀ i, 1 ≤ i → i ≤ s →
      |Mtilde i - MomentSeries.realMoment E B i| ≤ ξ) :
    |LogRecurrence.realOutput Mtilde j - ModelSupport.logCoeff E B j| ≤ F ^ s * ξ :=
  LogRecurrence.model_logCoeff_stability E B p.q_pos hR hRβ
    (fun e _ => hE e) (fun e _ => hLip e)
    (CubeZeroFreeMain.common_nonvanishing p E hc hE hLip B)
    hB hs hj hF hprecision Mtilde hMt herrors

end Paper08.OriginalTheorems
