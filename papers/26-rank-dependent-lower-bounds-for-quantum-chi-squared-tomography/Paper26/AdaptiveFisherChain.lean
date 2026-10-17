import Paper26.AdaptiveModel
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Native adaptive score energy chain

The generic one-step calculation below uses an actual Markov kernel on arbitrary
measurable spaces. L2 Holder proves cross-term integrability; kernel Fubini and
the conditional score mean0 prove cross-term cancellation. Thus squared Hilbert
norm energies add. Applying this calculation inductively to AdaptiveModel's
actual nested histories and Born prefix laws gives a finite-round energy sum.

Scores are actual jointly measurable Euclidean-vector functions with L2 moments
and conditional mean0. No energy identity or Fisher budget is assumed. Relating
these vectors to derivatives of actual Born/transcript likelihoods is a separate
obligation, as is the single-copy quantum information bound.
-/

noncomputable section

namespace Paper26.AdaptiveFisherChain

open MeasureTheory ProbabilityTheory QuantumModel AdaptiveModel
open scoped ENNReal BigOperators InnerProductSpace

section Generic
variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (μ : Measure α) [IsProbabilityMeasure μ] (κ : Kernel α β) [IsMarkovKernel κ]

/-- The old-history projection preserves measure under a Markov extension. -/
theorem fst_measurePreserving : MeasurePreserving Prod.fst (μ.compProd κ) μ :=
  ⟨measurable_fst, Measure.fst_compProd μ κ⟩

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- L2 functions of the preceding history remain L2 in the extended history. -/
theorem memLp_fst {f : α → E} (hf : MemLp f 2 μ) :
    MemLp (fun z : α × β => f z.1) 2 (μ.compProd κ) :=
  hf.comp_measurePreserving (fst_measurePreserving μ κ)

omit [CompleteSpace E] [IsProbabilityMeasure μ] in
/-- Actual L2 Holder domination of the varying Hilbert inner product. -/
theorem integrable_inner_of_memLp {f g : α → E} (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) : Integrable (fun a => ⟪f a, g a⟫_ℝ) μ := by
  apply (hf.norm.integrable_mul hg.norm).mono'
    (hf.aestronglyMeasurable.inner hg.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun a => norm_inner_le_norm _ _

/-- Conditional mean0 makes every old-history/L2-increment mixed moment zero. -/
theorem integral_inner_fst_eq_zero {f : α → E} {g : α × β → E}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 (μ.compProd κ))
    (hz : ∀ᵐ a ∂μ, (∫ b, g (a, b) ∂κ a) = 0) :
    (∫ z, ⟪f z.1, g z⟫_ℝ ∂μ.compProd κ) = 0 := by
  have hcross := integrable_inner_of_memLp (μ.compProd κ)
    (memLp_fst μ κ hf) hg
  have hgint : Integrable g (μ.compProd κ) := hg.integrable (by norm_num)
  have hcond := (Measure.integrable_compProd_iff hgint.aestronglyMeasurable).1 hgint
  rw [Measure.integral_compProd hcross]
  apply integral_eq_zero_of_ae
  filter_upwards [hcond.1, hz] with a ha haz
  rw [integral_inner ha (f a), haz, inner_zero_right]
  rfl

/-- The exact one-step martingale energy addition theorem. -/
theorem integral_norm_add_sq {f : α → E} {g : α × β → E}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 (μ.compProd κ))
    (hz : ∀ᵐ a ∂μ, (∫ b, g (a, b) ∂κ a) = 0) :
    (∫ z, ‖f z.1 + g z‖ ^ 2 ∂μ.compProd κ) =
      (∫ a, ‖f a‖ ^ 2 ∂μ) + (∫ z, ‖g z‖ ^ 2 ∂μ.compProd κ) := by
  have hfl := memLp_fst μ κ hf
  have hcross := integrable_inner_of_memLp (μ.compProd κ) hfl hg
  have hfsq := hfl.norm.integrable_sq
  have hgsq := hg.norm.integrable_sq
  have hfst : (∫ z : α × β, ‖f z.1‖ ^ 2 ∂μ.compProd κ) =
      ∫ a, ‖f a‖ ^ 2 ∂μ := by
    rw [Measure.integral_compProd hfsq]
    simp
  calc
    (∫ z, ‖f z.1 + g z‖ ^ 2 ∂μ.compProd κ) =
        ∫ z, (‖f z.1‖ ^ 2 + 2 * ⟪f z.1, g z⟫_ℝ) + ‖g z‖ ^ 2 ∂μ.compProd κ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun _ => norm_add_sq_real _ _
    _ = ((∫ z, ‖f z.1‖ ^ 2 ∂μ.compProd κ) +
        2 * (∫ z, ⟪f z.1, g z⟫_ℝ ∂μ.compProd κ)) +
          (∫ z, ‖g z‖ ^ 2 ∂μ.compProd κ) := by
      have hadd1 := integral_add (hfsq.add (hcross.const_mul 2)) hgsq
      have hadd2 := integral_add hfsq (hcross.const_mul 2)
      simp only [Pi.add_apply] at hadd1 hadd2
      rw [hadd1, hadd2, integral_const_mul]
    _ = (∫ a, ‖f a‖ ^ 2 ∂μ) + (∫ z, ‖g z‖ ^ 2 ∂μ.compProd κ) := by
      rw [integral_inner_fst_eq_zero μ κ hf hg hz, hfst]
      ring

end Generic

universe u
variable {ι : Type*} {Seed Ω : Type u} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace Seed] [MeasurableSpace Ω]
  {n p : ℕ} (A : Learner ι Seed Ω n) (ρ : Density ι)

/-- Actual Euclidean score increments on adaptive histories. Finite *joint*
L2 is essential for a finite expected-square identity; pointwise conditional
L2 alone would not imply a finite global second moment. The mean0 requirement
holds a.e. in the preceding actual Born history law. -/
structure ScoreProcess (A : Learner ι Seed Ω n) (ρ : Density ι) (p : ℕ) where
  score : ∀ k : Fin n, History Seed Ω (k.val + 1) → EuclideanSpace ℝ (Fin p)
  measurable_score : ∀ k, Measurable (score k)
  memLp_score : ∀ k, MemLp (score k) 2
    (A.prefixLaw ρ (k.val + 1) (Nat.succ_le_iff.mpr k.isLt))
  conditional_mean_zero : ∀ k : Fin n,
    ∀ᵐ h ∂A.prefixLaw ρ k.val (Nat.le_of_lt k.isLt),
      (∫ y, score k (h, y) ∂(A.step k).bornKernel ρ h) = 0

namespace ScoreProcess
variable {A ρ} (S : ScoreProcess A ρ p)

/-- Accumulated score through exactly k observed copies. -/
def sumScore : (k : ℕ) → k ≤ n → History Seed Ω k → EuclideanSpace ℝ (Fin p)
  | 0, _ => fun _ => 0
  | k + 1, hk => fun z => sumScore k (Nat.le_trans (Nat.le_succ k) hk) z.1 +
      S.score ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩ z

theorem sumScore_measurable (k : ℕ) (hk : k ≤ n) : Measurable (S.sumScore k hk) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
      change Measurable (fun z : History Seed Ω k × Ω =>
        S.sumScore k (Nat.le_trans (Nat.le_succ k) hk) z.1 +
          S.score ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩ z)
      exact ((ih _).comp measurable_fst).add (S.measurable_score _)

theorem sumScore_memLp (k : ℕ) (hk : k ≤ n) :
    MemLp (S.sumScore k hk) 2 (A.prefixLaw ρ k hk) := by
  induction k with
  | zero => exact MemLp.zero'
  | succ k ih =>
      have hs := S.memLp_score ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      change MemLp (fun z : History Seed Ω k × Ω =>
        S.sumScore k (Nat.le_trans (Nat.le_succ k) hk) z.1 +
          S.score ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩ z) 2
        ((A.prefixLaw ρ k (Nat.le_trans (Nat.le_succ k) hk)).compProd
          ((A.step ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩).bornKernel ρ))
      exact (memLp_fst _ _ (ih _)).add hs

/-- The actual expected squared norm of one score increment. -/
def stepEnergy (k : Fin n) : ℝ :=
  ∫ z, ‖S.score k z‖ ^ 2 ∂A.prefixLaw ρ (k.val + 1) (Nat.succ_le_iff.mpr k.isLt)

/-- Each joint increment energy is exactly the expected conditional energy
at the actual preceding Born history. -/
theorem stepEnergy_eq_conditional (k : Fin n) :
    S.stepEnergy k = ∫ h, ∫ y, ‖S.score k (h, y)‖ ^ 2
      ∂(A.step k).bornKernel ρ h ∂A.prefixLaw ρ k.val (Nat.le_of_lt k.isLt) := by
  change (∫ z : History Seed Ω k.val × Ω, ‖S.score k z‖ ^ 2
    ∂(A.prefixLaw ρ k.val (Nat.le_of_lt k.isLt)).compProd
      ((A.step k).bornKernel ρ)) = _
  exact Measure.integral_compProd (S.memLp_score k).norm.integrable_sq

theorem stepEnergy_nonneg (k : Fin n) : 0 ≤ S.stepEnergy k :=
  integral_nonneg fun _ => sq_nonneg _

/-- Each successor energy is the preceding energy plus this step's energy. -/
theorem sumScore_energy_succ (k : ℕ) (hk : k + 1 ≤ n) :
    (∫ z, ‖S.sumScore (k + 1) hk z‖ ^ 2 ∂A.prefixLaw ρ (k + 1) hk) =
      (∫ h, ‖S.sumScore k (Nat.le_trans (Nat.le_succ k) hk) h‖ ^ 2
        ∂A.prefixLaw ρ k (Nat.le_trans (Nat.le_succ k) hk)) +
        S.stepEnergy ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩ := by
  change (∫ z : History Seed Ω k × Ω,
    ‖S.sumScore k (Nat.le_trans (Nat.le_succ k) hk) z.1 +
      S.score ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩ z‖ ^ 2
        ∂(A.prefixLaw ρ k (Nat.le_trans (Nat.le_succ k) hk)).compProd
          ((A.step ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩).bornKernel ρ)) = _
  exact integral_norm_add_sq _ _ (S.sumScore_memLp k _)
    (S.memLp_score ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩)
    (S.conditional_mean_zero ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩)

/-- Exact expected-square additivity for every prefix, proved by induction. -/
theorem sumScore_energy (k : ℕ) (hk : k ≤ n) :
    (∫ z, ‖S.sumScore k hk z‖ ^ 2 ∂A.prefixLaw ρ k hk) =
      ∑ i : Fin k, S.stepEnergy ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ := by
  induction k with
  | zero => simp [sumScore]
  | succ k ih =>
      rw [S.sumScore_energy_succ k hk, ih _, Fin.sum_univ_castSucc]
      rfl

/-- The actual accumulated transcript score. -/
def totalScore : History Seed Ω n → EuclideanSpace ℝ (Fin p) :=
  S.sumScore n (Nat.le_refl n)

/-- Native finite-round martingale energy identity under the actual adaptive
Born transcript law. No chain identity or information budget is an input. -/
theorem totalScore_energy :
    (∫ z, ‖S.totalScore z‖ ^ 2 ∂A.transcriptLaw ρ) =
      ∑ k : Fin n, S.stepEnergy k := by
  simpa only [totalScore, AdaptiveModel.Learner.transcriptLaw] using
    S.sumScore_energy n (Nat.le_refl n)

/-- The usual conditional-energy chain formula on the genuine adaptive
experiment, obtained from the proved joint energy addition and kernel Fubini. -/
theorem totalScore_energy_eq_conditional :
    (∫ z, ‖S.totalScore z‖ ^ 2 ∂A.transcriptLaw ρ) =
      ∑ k : Fin n, ∫ h, ∫ y, ‖S.score k (h, y)‖ ^ 2
        ∂(A.step k).bornKernel ρ h ∂A.prefixLaw ρ k.val (Nat.le_of_lt k.isLt) := by
  rw [S.totalScore_energy]
  exact Finset.sum_congr rfl (fun k _ => S.stepEnergy_eq_conditional k)

/-- A bound on actual expected step energies propagates with the exact copy
count n. No quantum information bound is built into the score process. -/
theorem totalScore_energy_le (B : ℝ) (hB : ∀ k, S.stepEnergy k ≤ B) :
    (∫ z, ‖S.totalScore z‖ ^ 2 ∂A.transcriptLaw ρ) ≤ n * B := by
  rw [S.totalScore_energy]
  calc
    (∑ k : Fin n, S.stepEnergy k) ≤ ∑ _k : Fin n, B :=
      Finset.sum_le_sum fun k _ => hB k
    _ = n * B := by simp

end ScoreProcess
end Paper26.AdaptiveFisherChain
