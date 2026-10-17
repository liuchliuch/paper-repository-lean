import Paper08.MainTheorem

/-! # The original primal-degree input of Corollary 1.3

Changing a verified arity bound preserves scopes, value functions, query
handles, incidence counts and the original partition integral. This allows
Corollary 1.3 to take its primal-degree hypothesis directly.
-/
noncomputable section
namespace Paper08.PrimalArity

/-- Reuse the original input data with the arity bound proved from its primal graph. -/
def rebound {n r m η : ℕ} (E : FactorFamily n r m) (hη : FamilyPrimalDegreeLe E η) :
    FactorFamily n (η+1) m := fun e => {
  scope := (E e).scope
  nonempty := (E e).nonempty
  card_le := scope_card_le_primalDegree_add_one E hη e
  psi := (E e).psi }

@[simp] theorem partition_rebound {n r m η : ℕ} (E : FactorFamily n r m)
    (hη : FamilyPrimalDegreeLe E η) :
    Integral.partitionFunctionFactor (rebound E hη) = Integral.partitionFunctionFactor E := rfl

/-- The full nontrivial branch of Corollary 1.3, accepting precisely the
original primal-degree, occurrence, range and Lipschitz promises. The one
set of fixed program constants serves all inputs of all initial arities. -/
theorem corollary_1_3_ge_two {Δ η : ℕ} {k δ : ℝ}
    (hΔ : 1 ≤ Δ) (hη : 2 ≤ η) (hk : 0 < k) (hδ : 0 < δ ∧ δ < 1)
    (hρ : 1 < FPTAS.gamarnikSmediraRho Δ η δ) :
    let p := FPTAS.Params.ofGamarnikSmedira hΔ hη hk hδ hρ
    ∃ fixed : Parameters.Fixed, FPTASCorrectness.FixedBounds p fixed ∧
      ∃ C : ℕ, ∀ {n r m : ℕ} (E : FactorFamily n r m)
        (O : (e : Fin m) → Oracle.Oracle (E e).scope.card (E e).psi.toFun)
        (_hdegree : FamilyPrimalDegreeLe E η) (_hocc : FamilyBoundedOccurrence E Δ)
        (_hrange : ∀ e x, x ∈ Integral.cube (E e).scope.card →
          1 ≤ (E e).psi.toFun x ∧ (E e).psi.toFun x ≤ FPTAS.gamarnikSmediraRho Δ η δ)
        (_hLip : ∀ e, (E e).LipOk k)
        (_hne : ∀ B : Finset (Fin m), ∀ z ∈ Metric.ball (0 : ℂ) (FPTAS.beta p),
          ZeroFree.Q E B z ≠ 0) {ε : ℚ} (_hε : 0 < ε) (_hεu : ε ≤ 1/2),
        FPTAS.Accurate
          (FPTASAlgorithm.run fixed (fun e => (E e).scope) (fun e => (O e).query) (η+1) Δ ε : ℝ)
          (Integral.partitionFunctionFactor E) (ε : ℝ) ∧
        ((FPTASCost.runWithCost fixed (fun e => (E e).scope) (fun e => (O e).query) (η+1) Δ ε).2 : ℚ) ≤
          ((n:ℚ)/ε)^C ∧
        (1 ≤ m → Parameters.level fixed m ε ≤ C*Parameters.inputLog n ε ∧
          Parameters.precision fixed m ε ≤ C*Parameters.inputLog n ε) := by
  let p := FPTAS.Params.ofGamarnikSmedira hΔ hη hk hδ hρ
  obtain ⟨fixed, hb, C, hprogram⟩ := MainTheorem.theorem_1_2_modulo_external p
  refine ⟨fixed, hb, C, ?_⟩
  intro n r m E O hdegree hocc hrange hLip hne ε hε hεu
  let E' := rebound E hdegree
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
  exact hprogram E' O hocc' hE hlip' hne' hε hεu

end Paper08.PrimalArity
