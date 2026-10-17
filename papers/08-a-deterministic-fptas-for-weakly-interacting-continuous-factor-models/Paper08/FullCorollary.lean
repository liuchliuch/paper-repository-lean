import Paper08.FullAlgorithm
import Paper08.PrimalArity
import Paper08.LowDegreeGuarantee

/-! # Conditional primal-degree corollary and the direct low-degree branch

The η≥2 result uses precisely the original primal-degree input and preserves
its actual factor values, oracle handles and partition integral. The η=1
result is the independent complete direct-component guarantee imported above.
-/
noncomputable section
namespace Paper08.FullCorollary

/-- Conditional helper for Corollary 1.3 for η≥2 with actual execution and bit
cost. OriginalTheorems discharges its common-disk premise. Its numerical exponent is chosen before all uniform oracle polynomials. -/
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
        (_hne : ∀ B : Finset (Fin m), ∀ z ∈ Metric.ball (0 : ℂ) (FPTAS.beta p),
          ZeroFree.Q E B z ≠ 0) {ε : ℚ} (_hn : 1 ≤ n) (_hε : 0 < ε) (_hεu : ε ≤ 1/2)
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
  obtain ⟨fixed,hb,C,hprogram⟩ := FullAlgorithm.theorem_1_2_uniform p
  refine ⟨fixed,hb,C,?_⟩
  intro A degree
  obtain ⟨B,D,hB,hprogram⟩ := hprogram A degree
  refine ⟨B,D,hB,?_⟩
  intro n r m L E labels O hlabels hdegree hocc hrange hLip hne ε hn hε hεu hbits
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
  have hne' : FPTASCorrectness.CommonNonvanishing p E' := hne
  exact hprogram E' labels O hlabels hocc' hE hlip' hne' hn hε hεu hbits

end Paper08.FullCorollary
