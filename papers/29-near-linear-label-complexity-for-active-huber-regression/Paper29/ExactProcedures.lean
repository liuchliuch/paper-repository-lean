import Paper29.NonadaptiveBatch
import Paper29.ProcedureLifting

noncomputable section
open scoped BigOperators Classical ENNReal
open MeasureTheory
namespace Paper29.ProcessTools

def fullQueryProcedure {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) :
    QueryModel.NonadaptiveProcedure Unit n d where
  queried := fun _ => Finset.univ
  output := fun _ labels => WithLp.ofLp (Attainment.minimumNormSelection A (fun _ => 1)
    (fun i => labels ⟨i,Finset.mem_univ i⟩) (fun _ => by norm_num))

theorem fullQueryProcedure_minimizes {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (b : Fin n → ℝ) (ω : Unit) (x : Fin d → ℝ) :
    objective A b ((fullQueryProcedure A).answer ω b) ≤ objective A b x := by
  have hh := (Attainment.minimumNormSelection_spec A (fun _ => 1) b (fun _ => by norm_num)).1
    (WithLp.toLp 2 x)
  simpa only [Attainment.euclideanHuber, Attainment.affineHuber, weightedHuber, one_mul,
    WithLp.ofLp_toLp, objective] using hh

def unitMass (_ : Unit) : ℝ := 1

theorem unitMass_sum : (∑ ω : Unit, unitMass ω) = 1 := by simp [unitMass]

theorem fullQueryProcedure_correct {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    QueryModel.NonadaptiveCorrect (finiteMeasure unitMass (fun _ => by norm_num [unitMass]) unitMass_sum)
      (fullQueryProcedure A) A ε := by
  apply nonadaptiveCorrect_of_finite_probability
  intro b
  have hs (ω : Unit) (x : Fin d → ℝ) :
      Real.sqrt (objective A b ((fullQueryProcedure A).answer ω b)) ≤
        (1+ε)*Real.sqrt (objective A b x) := by
    have hh := Real.sqrt_le_sqrt (fullQueryProcedure_minimizes A b ω x)
    have hp := mul_nonneg hε (Real.sqrt_nonneg (objective A b x))
    nlinarith
  have he : Finset.univ.filter (fun ω : Unit => ∀ x,
      Real.sqrt (objective A b ((fullQueryProcedure A).answer ω b)) ≤
        (1+ε)*Real.sqrt (objective A b x)) = Finset.univ := by simp only [hs, implies_true, Finset.filter_true]
  rw [he]
  norm_num [Sampling.eventMass, unitMass]

def zeroQueryProcedure (n d : ℕ) : QueryModel.NonadaptiveProcedure Unit n d where
  queried := fun _ => ∅
  output := fun _ _ => 0

theorem zeroQueryProcedure_correct {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (hA : A.rank = 0) {ε : ℝ} (hε : 0 ≤ ε) :
    QueryModel.NonadaptiveCorrect (finiteMeasure unitMass (fun _ => by norm_num [unitMass]) unitMass_sum)
      (zeroQueryProcedure n d) A ε := by
  apply nonadaptiveCorrect_of_finite_probability
  intro b
  have hs (ω : Unit) (x : Fin d → ℝ) :
      Real.sqrt (objective A b ((zeroQueryProcedure n d).answer ω b)) ≤
        (1+ε)*Real.sqrt (objective A b x) := by
    have hh := Real.sqrt_le_sqrt (Reduction.rank_zero_optimizer A hA b x)
    have hp := mul_nonneg hε (Real.sqrt_nonneg (objective A b x))
    exact hh.trans (by nlinarith)
  have he : Finset.univ.filter (fun ω : Unit => ∀ x,
      Real.sqrt (objective A b ((zeroQueryProcedure n d).answer ω b)) ≤
        (1+ε)*Real.sqrt (objective A b x)) = Finset.univ := by simp only [hs, implies_true, Finset.filter_true]
  rw [he]
  norm_num [Sampling.eventMass, unitMass]

end Paper29.ProcessTools
