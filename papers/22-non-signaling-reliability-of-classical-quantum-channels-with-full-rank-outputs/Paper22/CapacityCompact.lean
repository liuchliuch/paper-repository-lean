import Paper22.Divergences
import Paper22.ProgramsCompact
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity

/-!
# Attainment of the Holevo capacity (equation (3))

The entropy of the actual channel mixture is continuous even at singular
matrices: it is the real trace of the continuous functional calculus of
`Real.negMulLog`.  The compact probability simplex therefore contains an
input distribution attaining the `sSup` in `holevoCapacity`.
-/

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

noncomputable section
namespace Paper22

variable {n d : ℕ}

local instance capacityMatrixCStarAlgebra (k : ℕ) :
    CStarAlgebra (Matrix (Fin k) (Fin k) ℂ) where

/-- The actual finite input probability simplex. -/
def probabilitySimplex (n : ℕ) : Set (Fin n → ℝ) :=
  {q | (∀ x, 0 ≤ q x) ∧ ∑ x, q x = 1}

/-- Nonnegativity of coordinates and normalization are closed conditions. -/
theorem isClosed_probabilitySimplex (n : ℕ) : IsClosed (probabilitySimplex n) := by
  unfold probabilitySimplex
  simp only [Set.setOf_and, Set.setOf_forall]
  exact (isClosed_iInter fun x => isClosed_le continuous_const (by fun_prop)).inter
    (isClosed_eq (by fun_prop) continuous_const)

/-- The probability simplex is a closed subset of the finite unit cube. -/
theorem isCompact_probabilitySimplex (n : ℕ) : IsCompact (probabilitySimplex n) := by
  have hcube : IsCompact (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  apply hcube.of_isClosed_subset (isClosed_probabilitySimplex n)
  intro q hq x _
  exact ⟨hq.1 x, probability_le_one hq.1 hq.2 x⟩

/-- A uniform distribution witnesses nonemptiness when the input alphabet is nonempty. -/
theorem probabilitySimplex_nonempty (hn : 0 < n) : (probabilitySimplex n).Nonempty :=
  ⟨(ProbDist.uniform n hn).q, (ProbDist.uniform n hn).nonneg,
    (ProbDist.uniform n hn).sum_eq_one⟩

/-- The spectrum of a density matrix lies in the fixed compact interval `[0,1]`. -/
theorem IsDensity.spectrum_real_subset_Icc {ρ : Matrix (Fin d) (Fin d) ℂ}
    (hρ : IsDensity ρ) : spectrum ℝ ρ ⊆ Set.Icc (0 : ℝ) 1 := by
  rw [hρ.isHermitian.spectrum_real_eq_range_eigenvalues]
  rintro t ⟨i, rfl⟩
  exact hρ.eigenvalues_mem_Icc i

/-- The eigenvalue entropy equals the real trace of the actual matrix CFC. -/
theorem vonNeumannEntropy_eq_trace_negMulLog {ρ : Matrix (Fin d) (Fin d) ℂ}
    (hρ : ρ.IsHermitian) :
    vonNeumannEntropy hρ = (1 / Real.log 2) * (cfc Real.negMulLog ρ).trace.re := by
  rw [vonNeumannEntropy_eq_negMulLog, trace_cfc_eq_sum_eigenvalues hρ]
  simp only [Complex.re_sum, Complex.ofReal_re]

/-- Forming a channel mixture is continuous in its real weights. -/
theorem continuous_mixture (V : CQChannel n d) : Continuous (mixture V) := by
  unfold mixture
  fun_prop

/-- `-A log A` is continuous on the actual probability-weighted channel mixtures,
including boundary distributions and singular output states. -/
theorem continuousOn_negMulLog_mixture (V : CQChannel n d) :
    ContinuousOn (fun q => cfc Real.negMulLog (mixture V q)) (probabilitySimplex n) := by
  apply (continuous_mixture V).continuousOn.cfc isCompact_Icc Real.negMulLog
  · intro q hq
    exact (mixture_isDensity V q hq.1 hq.2).spectrum_real_subset_Icc
  · intro q hq
    exact mixture_isHermitian V q hq.1

/-- A proof-independent expression for the Holevo objective, using matrix CFC. -/
def holevoContinuousObjective (V : CQChannel n d) (q : Fin n → ℝ) : ℝ :=
  (1 / Real.log 2) * (cfc Real.negMulLog (mixture V q)).trace.re -
    ∑ x, q x * vonNeumannEntropy (V.density x).isHermitian

/-- The continuous expression is exactly the original eigenvalue objective. -/
theorem holevoContinuousObjective_eq (V : CQChannel n d) (q : Fin n → ℝ)
    (hq : ∀ x, 0 ≤ q x) :
    holevoContinuousObjective V q = holevoObjective V q hq := by
  rw [holevoContinuousObjective, holevoObjective,
    vonNeumannEntropy_eq_trace_negMulLog]

/-- The actual Holevo objective is continuous on the closed probability simplex. -/
theorem continuousOn_holevoObjective (V : CQChannel n d) :
    ContinuousOn (holevoContinuousObjective V) (probabilitySimplex n) := by
  have ht : Continuous (fun A : Matrix (Fin d) (Fin d) ℂ => A.trace.re) := by fun_prop
  have he := ht.comp_continuousOn (continuousOn_negMulLog_mixture V)
  apply (continuousOn_const.mul he).sub
  exact (show Continuous (fun q : Fin n → ℝ =>
    ∑ x, q x * vonNeumannEntropy (V.density x).isHermitian) by fun_prop).continuousOn

/-- Equation (3) is a true maximum over input probability distributions, with
no full-rank assumption or replacement of the actual channel matrices. -/
theorem holevoCapacity_attained (V : CQChannel n d) (hn : 0 < n) :
    ∃ (q : Fin n → ℝ) (hq : ∀ x, 0 ≤ q x), ∑ x, q x = 1 ∧
      holevoCapacity V = holevoObjective V q hq := by
  obtain ⟨q, hq, hmax⟩ := (isCompact_probabilitySimplex n).exists_isMaxOn
    (probabilitySimplex_nonempty hn) (continuousOn_holevoObjective V)
  refine ⟨q, hq.1, hq.2, ?_⟩
  apply IsGreatest.csSup_eq
  refine ⟨⟨q, hq.1, hq.2, rfl⟩, ?_⟩
  rintro s ⟨q', hq', hq1', rfl⟩
  rw [← holevoContinuousObjective_eq V q' hq', ← holevoContinuousObjective_eq V q hq.1]
  exact hmax (show q' ∈ probabilitySimplex n from ⟨hq', hq1'⟩)

/-- A maximizing `ProbDist` exists, in the source's original entropy formula. -/
theorem holevoCapacity_maximum (V : CQChannel n d) (hn : 0 < n) :
    ∃ p : ProbDist n, holevoCapacity V = holevoObjective V p.q p.nonneg ∧
      ∀ p' : ProbDist n, holevoObjective V p'.q p'.nonneg ≤
        holevoObjective V p.q p.nonneg := by
  obtain ⟨q, hq, hq1, hC⟩ := holevoCapacity_attained V hn
  refine ⟨⟨q, hq, hq1⟩, hC, ?_⟩
  have hbounded : BddAbove {s | ∃ q : Fin n → ℝ, ∃ (hq : ∀ i, 0 ≤ q i),
      ∑ i, q i = 1 ∧ s = holevoObjective V q hq} := by
    have hc := (isCompact_probabilitySimplex n).image_of_continuousOn
      (continuousOn_holevoObjective V)
    apply hc.bddAbove.mono
    rintro s ⟨q', hq', hq1', rfl⟩
    exact ⟨q', ⟨hq', hq1'⟩, holevoContinuousObjective_eq V q' hq'⟩
  intro p'
  rw [← hC]
  exact le_csSup hbounded ⟨p'.q, p'.nonneg, p'.sum_eq_one, rfl⟩

/-- The outer maximum in the order-α capacity is attained for full-rank
channels.  No attainment assumption for the inner reference-state infimum is
needed: maximize the closed hypograph on a compact probability/height set. -/
theorem orderAlphaCapacity_attained [NeZero d] (V : CQChannel n d)
    (hn : 0 < n) (_hV : V.FullRank) {α : ℝ} (hα : α ∈ Set.Ioo 0 1) :
    ∃ (q : Fin n → ℝ) (hq : ∀ x, 0 ≤ q x), ∑ x, q x = 1 ∧
      orderAlphaCapacity V α = orderAlphaInf α V q := by
  let σ₀ := maximallyMixed d
  have hσ₀ : IsDensity σ₀ := maximallyMixed_isDensity (NeZero.pos d)
  have hcont (σ : Matrix (Fin d) (Fin d) ℂ) :
      Continuous (fun q : Fin n → ℝ => orderAlphaObj α V q σ) := by
    unfold orderAlphaObj
    fun_prop
  obtain ⟨q₀, hq₀, hmax₀⟩ := (isCompact_probabilitySimplex n).exists_isMaxOn
    (probabilitySimplex_nonempty hn) (hcont σ₀).continuousOn
  let a := (1 / (α - 1)) * log2 (d : ℝ)
  let b := orderAlphaObj α V q₀ σ₀
  let C : Set ((Fin n → ℝ) × ℝ) :=
    (probabilitySimplex n ×ˢ Set.Icc a b) ∩
      {z | ∀ σ : Matrix (Fin d) (Fin d) ℂ, IsDensity σ → z.2 ≤ orderAlphaObj α V z.1 σ}
  have hclosed : IsClosed
      {z : (Fin n → ℝ) × ℝ | ∀ σ : Matrix (Fin d) (Fin d) ℂ,
        IsDensity σ → z.2 ≤ orderAlphaObj α V z.1 σ} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun σ => isClosed_iInter fun _ =>
      isClosed_le continuous_snd ((hcont σ).comp continuous_fst)
  have hcompact : IsCompact C :=
    ((isCompact_probabilitySimplex n).prod isCompact_Icc).inter_right hclosed
  have hpoint (q : Fin n → ℝ) (hq : q ∈ probabilitySimplex n) :
      (q, orderAlphaInf α V q) ∈ C := by
    have hbelow := orderAlpha_values_bddBelow V hα hq.1 hq.2
    have hinf (σ : Matrix (Fin d) (Fin d) ℂ) (hσ : IsDensity σ) :
        orderAlphaInf α V q ≤ orderAlphaObj α V q σ :=
      csInf_le hbelow ⟨σ, hσ, rfl⟩
    have hlow : a ≤ orderAlphaInf α V q := by
      apply le_csInf (orderAlpha_values_nonempty V α q)
      rintro s ⟨σ, hσ, rfl⟩
      calc
        a = ∑ x, q x * a := by rw [← Finset.sum_mul, hq.2, one_mul]
        _ ≤ orderAlphaObj α V q σ :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
            (petzRenyiRe_lower_bound (V.isDensity x) hσ hα) (hq.1 x)
    exact ⟨⟨hq, hlow, (hinf σ₀ hσ₀).trans (hmax₀ hq)⟩, hinf⟩
  have hnonempty : C.Nonempty := ⟨(q₀, orderAlphaInf α V q₀), hpoint q₀ hq₀⟩
  obtain ⟨z, hz, hmax⟩ := hcompact.exists_isMaxOn hnonempty continuous_snd.continuousOn
  have hle : z.2 ≤ orderAlphaInf α V z.1 := by
    apply le_csInf (orderAlpha_values_nonempty V α z.1)
    rintro s ⟨σ, hσ, rfl⟩
    exact hz.2 σ hσ
  refine ⟨z.1, hz.1.1.1, hz.1.1.2, ?_⟩
  apply IsGreatest.csSup_eq
  refine ⟨⟨z.1, hz.1.1.1, hz.1.1.2, rfl⟩, ?_⟩
  rintro t ⟨q, hq, hq1, rfl⟩
  exact (hmax (hpoint q ⟨hq, hq1⟩)).trans hle

end Paper22
end
