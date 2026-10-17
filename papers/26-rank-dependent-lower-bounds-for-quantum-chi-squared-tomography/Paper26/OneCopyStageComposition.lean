import Paper26.StagePolicy
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Regrouping actual fresh-copy protocols at stage boundaries

Stage boundaries are copy indices.  The transition between them is composed
from the actual one-copy Born kernels; its action on the actual prefix law is
proved internally.  Conditional stage bounds therefore imply a probability
bound for the original learner with its original total fresh-copy count.
-/

noncomputable section

namespace Paper26.OneCopyStageComposition

open MeasureTheory ProbabilityTheory QuantumModel ContinuousPOVM AdaptiveModel
open scoped BigOperators ENNReal

universe u

variable {ι : Type*} {Seed Ω : Type u} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace Seed] [MeasurableSpace Ω] {N : ℕ}

/-- One actual copy appends its observed outcome to the whole history. -/
def advanceKernel (A : AdaptiveModel.Learner ι Seed Ω N) (ρ : Density ι) (k : Fin N) :
    Kernel (History Seed Ω k.val) (History Seed Ω (k.val + 1)) :=
  Kernel.id.prod ((A.step k).bornKernel ρ)

instance advanceKernel_markov (A : AdaptiveModel.Learner ι Seed Ω N) (ρ : Density ι)
    (k : Fin N) : IsMarkovKernel (advanceKernel A ρ k) := by
  exact Kernel.IsMarkovKernel.prod Kernel.id ((A.step k).bornKernel ρ)

/-- Exactly `k` consecutive genuine one-copy transitions after copy `a`. -/
def intervalKernel (A : AdaptiveModel.Learner ι Seed Ω N) (ρ : Density ι) (a : ℕ) :
    (k : ℕ) → a + k ≤ N → Kernel (History Seed Ω a) (History Seed Ω (a + k))
  | 0, _ => Kernel.id
  | k + 1, hk => (advanceKernel A ρ ⟨a + k, by omega⟩).comp
      (intervalKernel A ρ a k (by omega))

instance intervalKernel_markov (A : AdaptiveModel.Learner ι Seed Ω N) (ρ : Density ι)
    (a k : ℕ) (hk : a + k ≤ N) : IsMarkovKernel (intervalKernel A ρ a k hk) := by
  induction k with
  | zero => change IsMarkovKernel Kernel.id; infer_instance
  | succ k ih =>
      change IsMarkovKernel ((advanceKernel A ρ ⟨a + k, by omega⟩).comp
        (intervalKernel A ρ a k (by omega)))
      letI := ih (by omega)
      letI := advanceKernel_markov A ρ ⟨a + k, by omega⟩
      exact Kernel.IsMarkovKernel.comp _ _

/-- The native boundary law: no IID or protocol-equivalence premise. -/
theorem intervalKernel_comp_prefixLaw (A : AdaptiveModel.Learner ι Seed Ω N)
    (ρ : Density ι) (a k : ℕ) (hk : a + k ≤ N) :
    intervalKernel A ρ a k hk ∘ₘ A.prefixLaw ρ a (by omega) =
      A.prefixLaw ρ (a + k) hk := by
  induction k with
  | zero => exact Measure.id_comp
  | succ k ih =>
      rw [intervalKernel, ← Measure.comp_assoc, ih]
      exact (Measure.compProd_eq_comp_prod
        (A.prefixLaw ρ (a + k) (by omega))
        ((A.step ⟨a + k, by omega⟩).bornKernel ρ)).symm

/-- Reindexing a copy index transports the associated history sigma-algebra. -/
def historyCast {a b : ℕ} (h : a = b) : History Seed Ω a ≃ᵐ History Seed Ω b := by
  subst b
  exact MeasurableEquiv.refl _

theorem prefixLaw_map_historyCast (A : AdaptiveModel.Learner ι Seed Ω N)
    (ρ : Density ι) {a b : ℕ} (h : a = b) (ha : a ≤ N) (hb : b ≤ N) :
    (A.prefixLaw ρ a ha).map (historyCast h) = A.prefixLaw ρ b hb := by
  subst b
  exact Measure.map_id

/-- The actual transition between two possibly equal copy boundaries. -/
def betweenKernel (A : AdaptiveModel.Learner ι Seed Ω N) (ρ : Density ι)
    (a b : ℕ) (hab : a ≤ b) (hb : b ≤ N) :
    Kernel (History Seed Ω a) (History Seed Ω b) :=
  (intervalKernel A ρ a (b - a) (by omega)).map
    (historyCast (Nat.add_sub_of_le hab))

instance betweenKernel_markov (A : AdaptiveModel.Learner ι Seed Ω N) (ρ : Density ι)
    (a b : ℕ) (hab : a ≤ b) (hb : b ≤ N) :
    IsMarkovKernel (betweenKernel A ρ a b hab hb) :=
  Kernel.IsMarkovKernel.map _ (MeasurableEquiv.measurable _)

theorem betweenKernel_comp_prefixLaw (A : AdaptiveModel.Learner ι Seed Ω N)
    (ρ : Density ι) (a b : ℕ) (hab : a ≤ b) (hb : b ≤ N) :
    betweenKernel A ρ a b hab hb ∘ₘ A.prefixLaw ρ a (by omega) =
      A.prefixLaw ρ b hb := by
  rw [betweenKernel, ← Measure.map_comp _ _ (MeasurableEquiv.measurable _),
    intervalKernel_comp_prefixLaw]
  exact prefixLaw_map_historyCast A ρ _ _ _

end Paper26.OneCopyStageComposition

namespace Paper26.StagePolicy

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {H H' : Type*} [MeasurableSpace H] [MeasurableSpace H']

/-- A Markov transition with failure probability at most `δ` on every good
input history increases total failure probability by at most `δ`. -/
theorem transition_failure_le (μ : Measure H) [IsProbabilityMeasure μ]
    (κ : Kernel H H') [IsMarkovKernel κ] (G : Set H) (hG : MeasurableSet G)
    (B : Set H') (hB : MeasurableSet B) (δ : ℝ≥0∞)
    (hc : ∀ h ∈ G, κ h B ≤ δ) :
    (κ ∘ₘ μ) B ≤ μ Gᶜ + δ := by
  rw [Measure.bind_apply hB κ.aemeasurable]
  calc
    _ ≤ ∫⁻ h, δ + Gᶜ.indicator (fun _ => 1) h ∂μ := by
      apply lintegral_mono
      intro h
      dsimp only
      by_cases hh : h ∈ G
      · simpa [hh] using hc h hh
      · simpa [hh] using (show κ h B ≤ δ + 1 from
          (measure_mono (Set.subset_univ B)).trans (by simp))
    _ = μ Gᶜ + δ := by
      have hi := lintegral_indicator_one (μ := μ) hG.compl
      change (∫⁻ h, Gᶜ.indicator (fun _ : H => (1 : ℝ≥0∞)) h ∂μ) = μ Gᶜ at hi
      rw [lintegral_add_left measurable_const, lintegral_const,
        hi, measure_univ, mul_one, add_comm]

end Paper26.StagePolicy

namespace Paper26.OneCopyStageComposition

open MeasureTheory ProbabilityTheory QuantumModel ContinuousPOVM AdaptiveModel
open scoped BigOperators ENNReal

universe u

variable {ι : Type*} {Seed Ω : Type u} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace Seed] [MeasurableSpace Ω] {N L : ℕ}

/-- First-failure accumulation at actual copy boundaries.  Each conditional
bound concerns the native interval kernel of the original learner. -/
theorem boundary_failure_le (A : AdaptiveModel.Learner ι Seed Ω N) (ρ : Density ι)
    (boundary : ℕ → ℕ) (hb : ∀ j, j ≤ L → boundary j ≤ N)
    (hmono : ∀ j, j < L → boundary j ≤ boundary (j + 1))
    (G : ∀ j, Set (History Seed Ω (boundary j))) (hG : ∀ j, MeasurableSet (G j))
    (hG0 : G 0 = Set.univ) (δ : ℕ → ℝ≥0∞)
    (hc : ∀ j (hj : j < L) h, h ∈ G j →
      betweenKernel A ρ (boundary j) (boundary (j + 1)) (hmono j hj)
        (hb (j + 1) (by omega)) h (G (j + 1))ᶜ ≤ δ j)
    (j : ℕ) (hj : j ≤ L) :
    A.prefixLaw ρ (boundary j) (hb j hj) (G j)ᶜ ≤ ∑ k ∈ Finset.range j, δ k := by
  induction j with
  | zero => simp [hG0]
  | succ j ih =>
      rw [Finset.sum_range_succ,
        ← betweenKernel_comp_prefixLaw A ρ (boundary j) (boundary (j + 1))
          (hmono j (by omega)) (hb (j + 1) hj)]
      exact (StagePolicy.transition_failure_le _ _ (G j) (hG j)
        (G (j + 1))ᶜ (hG _).compl (δ j) (hc j (by omega))).trans
          (add_le_add (ih (by omega)) le_rfl)

/-- Total success is bounded at the original learner's true copy count `N`.
The number `L` of stage kernels is never substituted for that copy count. -/
theorem transcript_success_ge (A : AdaptiveModel.Learner ι Seed Ω N) (ρ : Density ι)
    (boundary : ℕ → ℕ) (hb : ∀ j, j ≤ L → boundary j ≤ N)
    (hmono : ∀ j, j < L → boundary j ≤ boundary (j + 1)) (hfinal : boundary L = N)
    (G : ∀ j, Set (History Seed Ω (boundary j))) (hG : ∀ j, MeasurableSet (G j))
    (hG0 : G 0 = Set.univ) (δ : ℕ → ℝ≥0∞)
    (hc : ∀ j (hj : j < L) h, h ∈ G j →
      betweenKernel A ρ (boundary j) (boundary (j + 1)) (hmono j hj)
        (hb (j + 1) (by omega)) h (G (j + 1))ᶜ ≤ δ j)
    (S : Set (History Seed Ω N))
    (hs : historyCast hfinal '' G L ⊆ S) :
    1 - (∑ j ∈ Finset.range L, δ j) ≤ A.transcriptLaw ρ S := by
  have hfail := boundary_failure_le A ρ boundary hb hmono G hG hG0 δ hc L (le_refl L)
  have hsum := measure_add_measure_compl
    (μ := A.prefixLaw ρ (boundary L) (hb L (le_refl L))) (hG L)
  rw [measure_univ] at hsum
  have hgood : 1 - (∑ j ∈ Finset.range L, δ j) ≤
      A.prefixLaw ρ (boundary L) (hb L (le_refl L)) (G L) := by
    apply tsub_le_iff_right.mpr
    rw [← hsum]
    exact add_le_add_left hfail _
  have hp := prefixLaw_map_historyCast A ρ hfinal (hb L (le_refl L)) (le_refl N)
  have he : A.prefixLaw ρ (boundary L) (hb L (le_refl L)) (G L) =
      A.transcriptLaw ρ (historyCast hfinal '' G L) := by
    change _ = A.prefixLaw ρ N (le_refl N) (historyCast hfinal '' G L)
    rw [← hp, Measure.map_apply (MeasurableEquiv.measurable _)
      ((historyCast hfinal).measurableSet_image.mpr (hG L)),
      MeasurableEquiv.preimage_image]
  exact (hgood.trans (le_of_eq he)).trans (measure_mono hs)

/-- A measurable per-copy classical control chooses actual quantum steps.
This constructs the operational learner before any statistical guarantee. -/
def controlledLearner {H : Type*} [MeasurableSpace H]
    (seed : Measure Seed) (hseed : IsProbabilityMeasure seed)
    (M : OneCopyStep ι H Ω) (control : ∀ k : Fin N, History Seed Ω k.val → H)
    (hm : ∀ k, Measurable (control k)) (T : Estimator ι (History Seed Ω N)) :
    AdaptiveModel.Learner ι Seed Ω N where
  seed := seed
  seed_probability := hseed
  step := fun k => StagePolicy.pullbackStep M (control k) (hm k)
  estimator := T

end Paper26.OneCopyStageComposition
