import Paper08.CertifiedConstants
import Paper08.FPTASCost
import Paper08.MomentArithmetic

/-! # Uniform accuracy, polynomial queries, and logarithmic precision

The constants below depend only on the fixed structural parameters. These
conditional helpers retain common nonvanishing explicitly; CubeZeroFreeMain
proves that property and OriginalTheorems gives the complete original-input
contracts. All algorithms in the conclusions are actual rational programs.
-/
noncomputable section
open scoped BigOperators
namespace Paper08.MainTheorem

/-- Absorb a fixed multiplicative constant into a polynomial degree when
`n/ε≥2`, as in the original accuracy range. -/
lemma absorb_constant {x a : ℚ} {D : ℕ} (hx : 2 ≤ x) (ha : 0 ≤ a) :
    (a*x)^D ≤ x^((Parameters.binaryLog a+1)*D) := by
  have hb := Parameters.binaryLog_pow a
  have hp : (2 : ℚ)^Parameters.binaryLog a ≤ x^Parameters.binaryLog a :=
    pow_le_pow_left₀ (by norm_num) hx _
  have ha' : a*x ≤ x^(Parameters.binaryLog a+1) := by
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_right (hb.trans hp) (by linarith)
  have hh := pow_le_pow_left₀ (mul_nonneg ha (by linarith)) ha' D
  simpa only [← pow_mul] using hh

/-- The same concrete instrumented program has the exact `(n/ε)^C` query
bound of Theorem 1.2, for a degree depending only on fixed parameters. -/
theorem query_bound {n m r c : ℕ} (fixed : Parameters.Fixed)
    (scopes : Fin m → Finset (Fin n)) (hscopes : ∀ e, (scopes e).card ≤ r)
    (hocc : m ≤ c*n) (query : PrimitiveMomentsQ.Queries scopes)
    {ε : ℚ} (hn : 1 ≤ n) (hε : 0 < ε) (hεu : ε ≤ 1/2) :
    ((FPTASCost.runWithCost fixed scopes query r c ε).2 : ℚ) ≤
      ((n : ℚ)/ε)^((Parameters.binaryLog ((8*(c+1):ℕ):ℚ)+1)*
        FPTASCost.queryDegree fixed r c) := by
  have hx : (2 : ℚ) ≤ (n : ℚ)/ε := by
    apply (le_div_iff₀ hε).mpr
    have hnq : (1 : ℚ) ≤ n := by exact_mod_cast hn
    linarith
  have hq := FPTASCost.runWithCost_queries_variables fixed scopes hscopes hocc query ε hε
    (by linarith : ε ≤ 1)
  have hbase : 4*((c+1:ℕ):ℚ)*(((n+1:ℕ):ℚ)/ε) ≤
      ((8*(c+1):ℕ):ℚ)*((n:ℚ)/ε) := by
    have hnn : ((n+1:ℕ):ℚ) ≤ 2*(n:ℚ) := by exact_mod_cast (by omega : n+1 ≤ 2*n)
    have hdiv := div_le_div_of_nonneg_right hnn hε.le
    have hh := mul_le_mul_of_nonneg_left hdiv (by positivity : (0:ℚ) ≤ 4*((c+1:ℕ):ℚ))
    convert hh using 1 <;> push_cast <;> ring
  exact hq.trans ((pow_le_pow_left₀ (by positivity) hbase _).trans
    (absorb_constant hx (by positivity)))

/-- A fixed constant controlling both actual precision parameters. -/
def precisionConstant (fixed : Parameters.Fixed) (c : ℕ) : ℕ :=
  max (2*(Parameters.budgetBaseLog fixed+Parameters.momentBaseLog fixed+2)+6)
      (3*Parameters.budgetBaseLog fixed+3*Parameters.momentBaseLog fixed+23) *
    (Parameters.truncationBlock fixed*(Parameters.truncationOffset fixed+1)) *
    (Parameters.binaryLog ((c+1:ℕ):ℚ)+1)

/-- The actually selected dyadic coordinate precision and oracle precision
are both logarithmic in the variable count and inverse accuracy. -/
theorem precision_bound {n m c : ℕ} (fixed : Parameters.Fixed) {ε : ℚ}
    (hm : 1 ≤ m) (hocc : m ≤ c*n) (hε : 0 < ε) :
    Parameters.level fixed m ε ≤ precisionConstant fixed c * Parameters.inputLog n ε ∧
    Parameters.precision fixed m ε ≤ precisionConstant fixed c * Parameters.inputLog n ε := by
  obtain ⟨D, hD, hJ, hP⟩ := Parameters.level_precision_linear fixed hm hε
  have hi := Parameters.inputLog_le_variables hocc hε
  have hk : 1 ≤ Parameters.inputLog n ε := Parameters.binaryLog_pos _
  have hlog : Parameters.inputLog m ε ≤
      (Parameters.binaryLog ((c+1:ℕ):ℚ)+1)*Parameters.inputLog n ε := by
    nlinarith
  have hmaxJ := le_max_left
    (2*(Parameters.budgetBaseLog fixed+Parameters.momentBaseLog fixed+2)+6)
    (3*Parameters.budgetBaseLog fixed+3*Parameters.momentBaseLog fixed+23)
  have hmaxP := le_max_right
    (2*(Parameters.budgetBaseLog fixed+Parameters.momentBaseLog fixed+2)+6)
    (3*Parameters.budgetBaseLog fixed+3*Parameters.momentBaseLog fixed+23)
  subst D
  constructor
  · apply hJ.trans
    unfold precisionConstant
    calc
      _ ≤ max _ _ * (Parameters.truncationBlock fixed*(Parameters.truncationOffset fixed+1)) *
          ((Parameters.binaryLog ((c+1:ℕ):ℚ)+1)*Parameters.inputLog n ε) := by gcongr
      _ = _ := by ring
  · apply hP.trans
    unfold precisionConstant
    calc
      _ ≤ max _ _ * (Parameters.truncationBlock fixed*(Parameters.truncationOffset fixed+1)) *
          ((Parameters.binaryLog ((c+1:ℕ):ℚ)+1)*Parameters.inputLog n ε) := by gcongr
      _ = _ := by ring

/-- There is one choice of fixed rational program constants for *all* inputs
with the specified structural parameters, with actual output accuracy,
polynomial oracle queries and logarithmic growing precision. -/
theorem theorem_1_2_modulo_external (p : FPTAS.Params) :
    ∃ fixed : Parameters.Fixed, FPTASCorrectness.FixedBounds p fixed ∧
      ∃ C : ℕ, ∀ {n m : ℕ} (E : FactorFamily n p.r m)
        (O : (e : Fin m) → Oracle.Oracle (E e).scope.card (E e).psi.toFun)
        (_hc : FamilyBoundedOccurrence E p.c)
        (_hE : ∀ e, (E e).RangeOk p.q) (_hLip : ∀ e, (E e).LipOk p.K)
        (_hne : FPTASCorrectness.CommonNonvanishing p E)
        {ε : ℚ} (_hε : 0 < ε) (_hεu : ε ≤ 1/2),
        FPTAS.Accurate
          (FPTASAlgorithm.run fixed (fun e => (E e).scope) (fun e => (O e).query) p.r p.c ε : ℝ)
          (Integral.partitionFunctionFactor E) (ε : ℝ) ∧
        ((FPTASCost.runWithCost fixed (fun e => (E e).scope) (fun e => (O e).query) p.r p.c ε).2 : ℚ) ≤
          ((n:ℚ)/ε)^C ∧
        (1 ≤ m → Parameters.level fixed m ε ≤ C*Parameters.inputLog n ε ∧
          Parameters.precision fixed m ε ≤ C*Parameters.inputLog n ε) := by
  obtain ⟨fixed, hb⟩ := CertifiedConstants.exists_fixedBounds p
  let A := (Parameters.binaryLog ((8*(p.c+1):ℕ):ℚ)+1)*FPTASCost.queryDegree fixed p.r p.c
  let B := precisionConstant fixed p.c
  refine ⟨fixed, hb, max A B, ?_⟩
  intro n m E O hc hE hLip hne ε hε hεu
  have hocc := family_card_le_occurrence_mul_variables E hc
  refine ⟨FPTASCorrectness.run_correct_of_common_nonvanishing p fixed hb E O hc hE hLip hne hε hεu,
    ?_, ?_⟩
  · by_cases hn0 : n = 0
    · have hm0 : m = 0 := by simp only [hn0, Nat.mul_zero, Nat.le_zero] at hocc; exact hocc
      subst m
      simp only [FPTASCost.runWithCost, if_pos rfl, Prod.snd, Rat.cast_zero]
      positivity
    · have hn : 1 ≤ n := by omega
      apply (query_bound fixed _ (fun e => (E e).card_le) hocc _ hn hε hεu).trans
      apply pow_le_pow_right₀ _ (le_max_left A B)
      apply (le_div_iff₀ hε).mpr
      have hnq : (1:ℚ) ≤ n := by exact_mod_cast hn
      linarith
  · intro hm
    have hp := precision_bound fixed hm hocc hε
    exact ⟨hp.1.trans (Nat.mul_le_mul_right _ (le_max_right A B)),
      hp.2.trans (Nat.mul_le_mul_right _ (le_max_right A B))⟩

end Paper08.MainTheorem
