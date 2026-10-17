import P31.QuadraticMetric
import P31.QueryProgram

/-! Actual adaptive query-program realization of the supplied-metric
quadratic result.  The known Hilbert routine's constructor takes only the
supplied diagonal weights, initial point, and budget, never the Hessian,
linear term, unknown objective, or minimizer. -/

noncomputable section
open scoped Matrix
namespace P31.QuadraticMetric

abbrev QuadraticQueryProgram (d : ℕ) :=
  QueryProgram.Program (Vec d) (ℝ × Vec d) (Vec d)

/-- The known external theorem is the Hilbert (`p_src=2`) specialization of
Corollary 3, Section 4.1, https://arxiv.org/html/2311.17296v2, in the approved
uniform-numerical-constant `N`-query normalization of its `2N`-iteration bound.
This interface strengthens query accounting by specifying an actual adaptive
query tree and its real execution.  Its target is only the metric dual norm. -/
structure HilbertQueryInput (C : ℝ) where
  routine : ∀d : ℕ, Vec d → Vec d → ℕ → QuadraticQueryProgram d
  rate : ∀ (d : ℕ) (A : Mat d), A.PosSemidef → ∀ (b x₀ xstar w : Vec d),
    (∀i, 0 < w i) → (∀v, dualHilbertNorm w (A *ᵥ v) ≤ hilbertNorm w v) →
    (∀x, objective A b xstar ≤ objective A b x) →
    ∀ (N : ℕ), 0 < N → ∀ (RD : ℝ), 0 ≤ RD → hilbertNorm w (x₀-xstar) ≤ RD →
      ((routine d w x₀ N).run (oracle A b)).calls ≤ N ∧
      dualHilbertNorm w (gradient A b ((routine d w x₀ N).run (oracle A b)).value) ≤
        C*RD/(N:ℝ)^2

/-- Conversion to the frozen Hilbert interface; both fields are extracted
from the same actual query-program execution. -/
def HilbertQueryInput.toHilbertRateInput {C : ℝ} (H : HilbertQueryInput C) (d : ℕ) :
    HilbertRateInput d C where
  run w o x₀ N := ((H.routine d w x₀ N).run o).value
  calls w o x₀ N := ((H.routine d w x₀ N).run o).calls
  rate A hA b x₀ xstar w hw hsmooth hmin N hN RD hRD hradius :=
    H.rate d A hA b x₀ xstar w hw hsmooth hmin N hN RD hRD hradius

def HilbertQueryInput.toUniformRateInput {C : ℝ} (H : HilbertQueryInput C) :
    HilbertUniformRateInput C := H.toHilbertRateInput

/-- Real calls are exactly the length of the actual oracle query list. -/
theorem HilbertQueryInput.calls_eq_queries_length {C : ℝ} (H : HilbertQueryInput C)
    (d : ℕ) (w x₀ : Vec d) (N : ℕ) (o : Vec d → ℝ × Vec d) :
    ((H.routine d w x₀ N).run o).calls = ((H.routine d w x₀ N).run o).queries.length :=
  QueryProgram.Program.calls_eq_length _ _

/-- The positive-norm case of Proposition 7.1 with actual oracle execution,
actual query count, and actual program output, using only the supplied metric. -/
theorem actual_query_proposition71_positive {d : ℕ} (hd : 0 < d) {p C R : ℝ}
    (hp : 2 ≤ p) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (A : Mat d) (hA : A.PosSemidef) (O : OperatorNormInput d p A)
    (hL : 0 < operatorNorm p A) (G : GaussianInput d p) (S : SDPInput d p A)
    (dual : LpDualityInput d p) (H : HilbertQueryInput C)
    (b x₀ xstar : Vec d) (hmin : ∀x, objective A b xstar ≤ objective A b x)
    (hradius : lpNorm p (x₀-xstar) ≤ R) :
    ∃w : Vec d, (∀i, 0 < w i) ∧ (Matrix.diagonal w).PosDef ∧
      (Matrix.diagonal w-A).PosSemidef ∧ metricNorm p w ≤ 2*gamma p*operatorNorm p A ∧
      ∀N : ℕ, 0 < N → ((H.routine d w x₀ N).run (oracle A b)).calls ≤ N ∧
        lpNorm (dualExponent p)
          (gradient A b ((H.routine d w x₀ N).run (oracle A b)).value) ≤
          (2*gamma p*C)*operatorNorm p A*R/(N:ℝ)^2 := by
  exact proposition71_positive hd hp hC hR A hA O hL G S dual (H.toHilbertRateInput d)
    b x₀ xstar hmin hradius

/-- The zero case is a concrete pure-return program with an empty query list. -/
theorem zero_operator_pure_program {d : ℕ} {p : ℝ} (hp : 2 ≤ p)
    (A : Mat d) (O : OperatorNormInput d p A) (hL : operatorNorm p A=0)
    (b x₀ xstar : Vec d) (hmin : ∀x, objective A b xstar ≤ objective A b x) :
    let P : QuadraticQueryProgram d := .pure x₀
    (P.run (oracle A b)).value=x₀ ∧ (P.run (oracle A b)).queries=[] ∧
      (P.run (oracle A b)).calls=0 ∧
      lpNorm (dualExponent p) (gradient A b (P.run (oracle A b)).value)=0 := by
  obtain ⟨_, _, hzero⟩ := zero_operator_gradient hp A O hL b xstar hmin
  simp only [QueryProgram.Program.run_pure]
  refine ⟨True.intro, True.intro, True.intro, ?_⟩
  rw [hzero, lpNorm_zero (dualExponent_pos (by linarith : 1 < p))]

/-- Full actual-query form of Proposition 7.1.  The zero branch is the explicit
zero-query program.  The positive branch derives the diagonal matrix and runs
the known oracle-only routine with that supplied metric and at most `N` queries. -/
theorem actual_query_proposition71 {d : ℕ} (hd : 0 < d) {p C R : ℝ}
    (hp : 2 ≤ p) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (A : Mat d) (hA : A.PosSemidef) (O : OperatorNormInput d p A)
    (G : GaussianInput d p) (S : SDPInput d p A)
    (dual : LpDualityInput d p) (H : HilbertQueryInput C)
    (b x₀ xstar : Vec d) (hmin : ∀x, objective A b xstar ≤ objective A b x)
    (hradius : lpNorm p (x₀-xstar) ≤ R) :
    (operatorNorm p A=0 ∧
      ∃P : QuadraticQueryProgram d, (P.run (oracle A b)).value=x₀ ∧
        (P.run (oracle A b)).queries=[] ∧ (P.run (oracle A b)).calls=0 ∧
        lpNorm (dualExponent p) (gradient A b (P.run (oracle A b)).value)=0) ∨
    (∃w : Vec d, (∀i, 0 < w i) ∧ (Matrix.diagonal w).PosDef ∧
      (Matrix.diagonal w-A).PosSemidef ∧ metricNorm p w ≤ 2*gamma p*operatorNorm p A ∧
      ∀N : ℕ, 0 < N → ((H.routine d w x₀ N).run (oracle A b)).calls ≤ N ∧
        lpNorm (dualExponent p)
          (gradient A b ((H.routine d w x₀ N).run (oracle A b)).value) ≤
          (2*gamma p*C)*operatorNorm p A*R/(N:ℝ)^2) := by
  rcases eq_or_lt_of_le (operatorNorm_nonneg hp A O) with hzero | hpos
  · exact Or.inl ⟨hzero.symm, .pure x₀,
      zero_operator_pure_program hp A O hzero.symm b x₀ xstar hmin⟩
  · exact Or.inr (actual_query_proposition71_positive hd hp hC hR A hA O hpos G S dual H
      b x₀ xstar hmin hradius)

end P31.QuadraticMetric
