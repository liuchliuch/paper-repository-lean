import Paper08.FPTASCorrectness
import Paper08.Cor13

/-!
# Existence of certified fixed numerical constants

The structural parameters alone provide a rational radius and integer upper
bounds for every fixed constant required by the actual program. No accuracy
or output certificate is postulated.
-/

noncomputable section
open scoped NNReal

namespace Paper08.CertifiedConstants

/-- The fixed numerical bounds used by the rational program always exist
under precisely the weak-interaction parameter assumptions. -/
theorem exists_fixedBounds (p : FPTAS.Params) :
    ∃ fixed : Parameters.Fixed, FPTASCorrectness.FixedBounds p fixed := by
  obtain ⟨R, hRone, hRbeta⟩ := exists_rat_btwn (FPTAS.beta_gt_one p)
  let qPlus : ℚ := (⌈p.q⌉₊ + 1 : ℕ)
  let A0 : ℕ := 8 * FPTASAlgorithm.degreeBound p.r p.c
  let F : ℕ := max 1 ⌈4 * Real.exp (Coeff.kappa (R : ℝ) p.q)⌉₊
  let C : ℕ := 2 + ⌈2 * p.q⌉₊ + ⌈6 * Real.sqrt p.r * p.K⌉₊
  have hA : 1 ≤ A0 := by
    have hd : 1 ≤ FPTASAlgorithm.degreeBound p.r p.c := le_max_left _ _
    dsimp [A0]
    omega
  have hF : 1 ≤ F := le_max_left _ _
  have hC : 1 ≤ C := by dsimp [C]; omega
  let fixed : Parameters.Fixed := {
    R := R
    qPlus := qPlus
    A0 := A0
    F := F
    C := C
    R_gt_one := by exact_mod_cast hRone
    qPlus_pos := by dsimp [qPlus]; positivity
    A0_pos := hA
    F_pos := hF
    C_pos := hC }
  refine ⟨fixed, ?_⟩
  constructor
  · change p.q ≤ (qPlus : ℝ)
    have h := Nat.le_ceil p.q
    dsimp [qPlus]
    push_cast
    linarith
  · exact hRbeta
  · exact le_refl A0
  · change 4 * Real.exp (Coeff.kappa (R : ℝ) p.q) ≤ (F : ℝ)
    exact (Nat.le_ceil _).trans (by
      exact_mod_cast (le_max_right 1 ⌈4 * Real.exp (Coeff.kappa (R : ℝ) p.q)⌉₊))
  · change 2 ≤ C
    dsimp [C]
    omega
  · change 2 * p.q ≤ (C : ℝ)
    have h := Nat.le_ceil (2 * p.q)
    have hn : (0 : ℝ) ≤ ⌈6 * Real.sqrt p.r * p.K⌉₊ := Nat.cast_nonneg _
    dsimp [C]
    push_cast
    linarith
  · change 6 * Real.sqrt p.r * p.K ≤ (C : ℝ)
    have h := Nat.le_ceil (6 * Real.sqrt p.r * p.K)
    have hn : (0 : ℝ) ≤ ⌈2 * p.q⌉₊ := Nat.cast_nonneg _
    dsimp [C]
    push_cast
    linarith

/-- One choice of fixed constants works for every model and every requested
accuracy with these structural parameters. No existence of fixed bounds is
an input to this actual-program correctness statement. -/
theorem exists_fixed_run_correct (p : FPTAS.Params) :
    ∃ fixed : Parameters.Fixed, FPTASCorrectness.FixedBounds p fixed ∧
      ∀ {n m : ℕ} (E : FactorFamily n p.r m)
        (O : (e : Fin m) → Oracle.Oracle (E e).scope.card (E e).psi.toFun)
        (_hc : FamilyBoundedOccurrence E p.c)
        (_hE : ∀ e, (E e).RangeOk p.q) (_hLip : ∀ e, (E e).LipOk p.K)
        (_hne : FPTASCorrectness.CommonNonvanishing p E)
        {ε : ℚ} (_hε : 0 < ε) (_hεu : ε ≤ 1 / 2),
        FPTAS.Accurate
          (FPTASAlgorithm.run fixed (fun e => (E e).scope) (fun e => (O e).query) p.r p.c ε : ℝ)
          (Integral.partitionFunctionFactor E) (ε : ℝ) := by
  obtain ⟨fixed, hb⟩ := exists_fixedBounds p
  refine ⟨fixed, hb, ?_⟩
  intro n m E O hc hE hLip hne ε hε hεu
  exact FPTASCorrectness.run_correct_of_common_nonvanishing p fixed hb E O hc hE hLip hne hε hεu

/-- Corollary 1.3 for `η ≥ 2`: the converted source parameters have actual
fixed rational program constants, and the actual program has the claimed
accuracy under an explicit common-disk premise. OriginalTheorems now
discharges this premise from the original model promises. -/
theorem gamarnikSmedira_exists_run_correct {Δ η : ℕ} {k δ : ℝ}
    (hΔ : 1 ≤ Δ) (hη : 2 ≤ η) (hk : 0 < k) (hδ : 0 < δ ∧ δ < 1)
    (hρ : 1 < FPTAS.gamarnikSmediraRho Δ η δ) :
    let p := FPTAS.Params.ofGamarnikSmedira hΔ hη hk hδ hρ
    ∃ fixed : Parameters.Fixed, FPTASCorrectness.FixedBounds p fixed ∧
      ∀ {n m : ℕ} (E : FactorFamily n p.r m)
        (O : (e : Fin m) → Oracle.Oracle (E e).scope.card (E e).psi.toFun)
        (_hc : FamilyBoundedOccurrence E p.c)
        (_hE : ∀ e, (E e).RangeOk p.q) (_hLip : ∀ e, (E e).LipOk p.K)
        (_hne : FPTASCorrectness.CommonNonvanishing p E)
        {ε : ℚ} (_hε : 0 < ε) (_hεu : ε ≤ 1 / 2),
        FPTAS.Accurate
          (FPTASAlgorithm.run fixed (fun e => (E e).scope) (fun e => (O e).query) p.r p.c ε : ℝ)
          (Integral.partitionFunctionFactor E) (ε : ℝ) :=
  exists_fixed_run_correct (FPTAS.Params.ofGamarnikSmedira hΔ hη hk hδ hρ)


end Paper08.CertifiedConstants
