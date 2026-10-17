import Paper26.CollectiveFilterComposition
import Paper26.FrobeniusLearning

/-!
# Actual continuous collective submatrix estimation

The conditional estimators are chosen before the input state. Their physical
POVM is the native continuous projective-filter composition. Only the original
uniform O'Donnell--Wright Frobenius experiment is a supporting input; no
submatrix law, mass rescaling, risk or success bound is assumed.
-/
noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal
namespace Paper26.ContinuousSubmatrixLearning
open MeasureTheory QuantumModel ContinuousPOVM CollectiveFiltering
open CollectiveFilterComposition CollectiveSubmatrix ShellAccounting

local instance matrixMeasurableSpace (m n : Type*) : MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))

section ConditionalRisk
variable {α Ω : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace Ω]
  (ν : Measure Ω) [IsProbabilityMeasure ν]

lemma measurable_frobenius_error (f : Ω → Density α) (hf : Measurable f)
    (τ : Density α) (a w : ℝ) :
    Measurable (fun y => frobeniusSq ((a : ℂ) • (f y).matrix - (w : ℂ) • τ.matrix)) := by
  unfold frobeniusSq
  apply Finset.measurable_sum Finset.univ
  intro i _
  apply Finset.measurable_sum Finset.univ
  intro j _
  exact (((measurable_pi_apply j).comp ((measurable_pi_apply i).comp
    (measurable_density_matrix.comp hf))).const_mul (a : ℂ) |>.sub_const _).norm.pow_const 2

lemma density_difference_sq_le_four (σ τ : Density α) :
    frobeniusSq (σ.matrix - τ.matrix) ≤ 4 := by
  have h := frobeniusSq_add_le σ.matrix (-τ.matrix)
  have hn : frobeniusSq (-τ.matrix) = frobeniusSq τ.matrix := by simp [frobeniusSq]
  rw [hn] at h
  exact h.trans (by linarith [density_frobeniusSq_le_one σ, density_frobeniusSq_le_one τ])

lemma error_integrable (f : Ω → Density α) (hf : Measurable f) (τ : Density α) :
    Integrable (fun y => frobeniusSq ((f y).matrix - τ.matrix)) ν := by
  apply Integrable.mono' (integrable_const (4 : ℝ))
    (by simpa only [Complex.ofReal_one, one_smul] using
      (measurable_frobenius_error f hf τ 1 1).aestronglyMeasurable)
  exact ae_of_all _ fun y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (frobeniusSq_nonneg _)]
    exact density_difference_sq_le_four _ _

/-- Continuous-output version of the native deterministic rescaling bound.
Only the raw normalized-state expectation enters; the count-zero branch
requires no such bound. -/
theorem conditional_count_risk (N : ℕ) (hN : 0 < N) (m : ℕ)
    (f : Ω → Density α) (hf : Measurable f) (τ : Density α) (w : ℝ)
    (hOW : 0 < m → (∫⁻ y, ENNReal.ofReal (frobeniusSq ((f y).matrix - τ.matrix)) ∂ν) ≤
      ENNReal.ofReal (4 * Fintype.card α / (m : ℝ))) :
    (∫⁻ y, ENNReal.ofReal (frobeniusSq
      ((((m : ℝ) / N : ℝ) : ℂ) • (f y).matrix - (w : ℂ) • τ.matrix)) ∂ν) ≤
        ENNReal.ofReal (8 * Fintype.card α * m / (N : ℝ)^2 + 2 * ((m : ℝ) / N - w)^2) := by
  by_cases hm : m = 0
  · subst m
    simp only [Nat.cast_zero, zero_div, Complex.ofReal_zero, zero_smul, zero_sub, frobeniusSq,
      Matrix.neg_apply, norm_neg]
    have he : (∑ i, ∑ j, ‖((w : ℂ) • τ.matrix) i j‖ ^ 2) =
        w^2 * frobeniusSq τ.matrix := frobeniusSq_real_smul w τ.matrix
    rw [he]
    simp only [lintegral_const, measure_univ, mul_one, mul_zero, zero_mul,
      zero_add, zero_sub, neg_sq, zero_div]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [mul_le_mul_of_nonneg_left (density_frobeniusSq_le_one τ) (sq_nonneg w), sq_nonneg w]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hmeas := (measurable_frobenius_error f hf τ 1 1)
    simp only [Complex.ofReal_one, one_smul] at hmeas
    have hpoint : ∀ y, frobeniusSq
        ((((m : ℝ) / N : ℝ) : ℂ) • (f y).matrix - (w : ℂ) • τ.matrix) ≤
        2 * ((m : ℝ) / N)^2 * frobeniusSq ((f y).matrix - τ.matrix) +
          2 * ((m : ℝ) / N - w)^2 := by
      intro y
      have h := rescaling_error (f y) τ ((m : ℝ) / N) w
      have hτ := density_frobeniusSq_le_one τ
      have hc : 0 ≤ 2 * ((m : ℝ) / N - w)^2 := by positivity
      nlinarith
    calc
      _ ≤ ∫⁻ y, ENNReal.ofReal
          (2 * ((m : ℝ) / N)^2 * frobeniusSq ((f y).matrix - τ.matrix) +
            2 * ((m : ℝ) / N - w)^2) ∂ν :=
        lintegral_mono fun y => ENNReal.ofReal_le_ofReal (hpoint y)
      _ = ENNReal.ofReal (2 * ((m : ℝ) / N)^2) *
          (∫⁻ y, ENNReal.ofReal (frobeniusSq ((f y).matrix - τ.matrix)) ∂ν) +
            ENNReal.ofReal (2 * ((m : ℝ) / N - w)^2) := by
        simp_rw [ENNReal.ofReal_add (mul_nonneg (by positivity : 0 ≤ 2 * ((m : ℝ) / N)^2) (frobeniusSq_nonneg _)) (by positivity : 0 ≤ 2 * ((m : ℝ) / N - w)^2),
          ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * ((m : ℝ) / N)^2)]
        rw [lintegral_add_left ((hmeas.ennreal_ofReal).const_mul _),
          lintegral_const_mul _ hmeas.ennreal_ofReal, lintegral_const, measure_univ, mul_one]
      _ ≤ ENNReal.ofReal (2 * ((m : ℝ) / N)^2) *
          ENNReal.ofReal (4 * Fintype.card α / (m : ℝ)) +
            ENNReal.ofReal (2 * ((m : ℝ) / N - w)^2) := by gcongr; exact hOW hmpos
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * ((m : ℝ) / N)^2),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        have hn0 : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
        have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm
        field_simp
        <;> ring

end ConditionalRisk

section CountAverage
variable {N : ℕ} {α β : Type*} [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β]
local instance : MeasurableSpace (Finset (Fin N)) := ⊤
local instance : MeasurableSpace (Fin (N+1)) := ⊤

lemma subset_count_lintegral (ρ : Density (α ⊕ β)) (b : Fin (N+1) → ℝ)
    (hb : ∀ m, 0 ≤ b m) :
    (∑ S : Finset (Fin N), ENNReal.ofReal
      (headMass ρ ^ S.card * (1-headMass ρ)^(N-S.card)) *
        ENNReal.ofReal (b (retainedCount S))) =
      ENNReal.ofReal ((binomialLaw N (headMass ρ) (headMass_nonneg ρ)
        (headMass_le_one ρ)).expectation b) := by
  let ν := (finsetMeasurement (α := α) (β := β) N).outcomeMeasure
    (TensorCopies.density ρ N)
  have hf : Measurable (fun m => ENNReal.ofReal (b m)) := measurable_of_countable _
  have hc : Measurable (retainedCount (N := N)) := measurable_of_countable _
  calc
    _ = ∫⁻ S, ENNReal.ofReal (b (retainedCount S)) ∂ν := by
      dsimp [ν]
      rw [DominatedPOVM.outcomeMeasure, lintegral_withDensity_eq_lintegral_mul _
        ((finsetMeasurement (α := α) (β := β) N).born_measurable _).ennreal_ofReal
        (show Measurable (fun S : Finset (Fin N) => ENNReal.ofReal (b (retainedCount S))) from hf.comp hc)]
      change _ = ∫⁻ S, ENNReal.ofReal ((finsetMeasurement (α := α) (β := β) N).born
        (TensorCopies.density ρ N) S) * ENNReal.ofReal (b (retainedCount S)) ∂Measure.count
      rw [lintegral_count, tsum_fintype]
      apply Finset.sum_congr rfl
      intro S _
      rw [show (finsetMeasurement (α := α) (β := β) N).born
        (TensorCopies.density ρ N) S =
        headMass ρ ^ S.card * (1-headMass ρ)^(N-S.card) from finset_pattern_born ρ S]
    _ = ∫⁻ m, ENNReal.ofReal (b m) ∂(binomialLaw N (headMass ρ)
        (headMass_nonneg ρ) (headMass_le_one ρ)).toPMF.toMeasure := by
      rw [← binomial_count_law N ρ, lintegral_map hf hc]
    _ = _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal Integrable.of_finite
        (ae_of_all _ hb), ← FiniteLaw.expectation_eq_integral]

lemma averaged_count_risk (N : ℕ) (hN : 0 < N) (w : ℝ) (hw : 0 ≤ w) (hw1 : w ≤ 1) :
    (binomialLaw N w hw hw1).expectation (fun m =>
      8 * Fintype.card α * m.val / (N : ℝ)^2 + 2 * ((m.val : ℝ)/N-w)^2) ≤
        2 * (4 * Fintype.card α + 1) * w / N := by
  let p := binomialLaw N w hw hw1
  have hmean := BinomialMoments.binomialMomentsInput.first N w hw hw1
  have hvar := BinomialMoments.binomialMomentsInput.centered_second N w hw hw1
  have he : p.expectation (fun m =>
      8 * Fintype.card α * m.val / (N : ℝ)^2 + 2 * ((m.val : ℝ)/N-w)^2) =
      8 * Fintype.card α / (N : ℝ)^2 * (N*w) + 2 * (w*(1-w)/N) := by
    rw [FiniteLaw.expectation_add]
    have hm : (fun m : Fin (N+1) => 8 * Fintype.card α * m.val / (N : ℝ)^2) =
        fun m => (8 * Fintype.card α / (N : ℝ)^2) * m.val := by funext m; ring
    rw [hm, FiniteLaw.expectation_const_mul, hmean,
      FiniteLaw.expectation_const_mul, normalized_count_variance N hN p w hvar]
  change p.expectation _ ≤ _
  rw [he]
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hn0 : (N : ℝ) ≠ 0 := ne_of_gt hn
  apply (le_div_iff₀ hn).mpr
  field_simp
  nlinarith [sq_nonneg w]

end CountAverage


/-- Physical retained experiments. This is ordinary experiment data plus its
original normalized Frobenius guarantee, not a new external theorem. The
family is constructed from the registered OW input below, before inputρ. -/
structure RetainedFamily (α : Type*) [Fintype α] [DecidableEq α] (N : ℕ) where
  Outcome : Finset (Fin N) → Type
  outcomeMeasurable : ∀ S, MeasurableSpace (Outcome S)
  retainedMeasurement : ∀ (S : Finset (Fin N)), @DominatedPOVM ({j : Fin N // j ∈ S} → α) (Outcome S)
    _ _ (outcomeMeasurable S)
  estimator : ∀ (S : Finset (Fin N)), @Estimator α (Outcome S) _ _ (outcomeMeasurable S)
  expected_error : ∀ (S : Finset (Fin N)), 0 < S.card → ∀ τ : Density α,
    (∫⁻ y, ENNReal.ofReal (frobeniusSq
      (((estimator S).estimate y).matrix - τ.matrix))
      ∂(retainedMeasurement S).outcomeMeasure (indexedDensity (J := {j : Fin N // j ∈ S}) τ)) ≤
        ENNReal.ofReal (4 * Fintype.card α / (S.card : ℝ))
attribute [instance] RetainedFamily.outcomeMeasurable

namespace RetainedFamily
variable {N : ℕ} {α β : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [Fintype β] [DecidableEq β]
local instance : MeasurableSpace (Finset (Fin N)) := ⊤
local instance : MeasurableSpace (Fin (N+1)) := ⊤
variable (D : RetainedFamily α N)

def output (z : Finset (Fin N) × (∀ S, D.Outcome S)) : Matrix α α ℂ :=
  ((((z.1.card : ℝ) / N : ℝ) : ℂ) • ((D.estimator z.1).estimate (z.2 z.1)).matrix)

lemma output_posSemidef (z : Finset (Fin N) × (∀ S, D.Outcome S)) :
    (D.output z).PosSemidef :=
  rescaled_posSemidef _ _ (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

lemma output_zero_count (z : Finset (Fin N) × (∀ S, D.Outcome S))
    (hz : z.1.card = 0) : D.output z = 0 := by simp [output, hz]

lemma measurable_output : Measurable D.output := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  apply measurable_from_prod_countable_right
  intro S
  change Measurable (fun y : ∀ S, D.Outcome S =>
    (((S.card : ℝ) / N : ℝ) : ℂ) * ((D.estimator S).estimate (y S)).matrix i j)
  exact (((measurable_pi_apply j).comp ((measurable_pi_apply i).comp
    (D.estimator S).measurable_matrix)).comp (measurable_pi_apply S)).const_mul _

/-- A genuine collective N-copy POVM, independent of the unknown input. -/
def measurement : DominatedPOVM (Fin N → (α ⊕ β))
    (Finset (Fin N) × (∀ S, D.Outcome S)) := jointMeasurement D.retainedMeasurement

lemma measurable_error (ρ : Density (α ⊕ β)) :
    Measurable (fun z => frobeniusSq (D.output z - headBlock ρ.matrix)) := by
  unfold frobeniusSq
  apply Finset.measurable_sum Finset.univ
  intro i _
  apply Finset.measurable_sum Finset.univ
  intro j _
  exact (((measurable_pi_apply j).comp ((measurable_pi_apply i).comp
    D.measurable_output)).sub_const _).norm.pow_const 2

/-- Actual full-copy risk, under the concrete physical continuous POVM. -/
theorem full_expected_error (hN : 0 < N) (ρ : Density (α ⊕ β)) (hw : 0 < headMass ρ) :
    (∫⁻ z, ENNReal.ofReal (frobeniusSq (D.output z - headBlock ρ.matrix))
      ∂(D.measurement (β := β)).outcomeMeasure (TensorCopies.density ρ N)) ≤
        ENNReal.ofReal (2 * (4 * Fintype.card α + 1) * headMass ρ / N) := by
  let τ := retainedState ρ hw
  have hm : headBlock ρ.matrix = (headMass ρ : ℂ) • τ.matrix := headBlock_eq_mass_smul ρ hw
  let g : ∀ S, D.Outcome S → ℝ≥0∞ := fun S y => ENNReal.ofReal (frobeniusSq
    (((((S.card : ℝ) / N : ℝ) : ℂ) • ((D.estimator S).estimate y).matrix) - headBlock ρ.matrix))
  have hg : ∀ S, Measurable (g S) := by
    intro S
    change Measurable (fun y => ENNReal.ofReal (frobeniusSq
      (((((S.card : ℝ) / N : ℝ) : ℂ) • ((D.estimator S).estimate y).matrix) - headBlock ρ.matrix)))
    rw [hm]
    exact (measurable_frobenius_error (D.estimator S).estimate
      (D.estimator S).measurable_estimate τ _ _).ennreal_ofReal
  change (∫⁻ z, g z.1 (z.2 z.1) ∂(jointMeasurement (β := β) D.retainedMeasurement).outcomeMeasure (TensorCopies.density ρ N)) ≤ _
  rw [joint_lintegral (β := β) D.retainedMeasurement ρ hw g hg]
  calc
    _ ≤ ∑ S : Finset (Fin N), ENNReal.ofReal
        (headMass ρ ^ S.card * (1-headMass ρ)^(N-S.card)) * ENNReal.ofReal
          (8 * Fintype.card α * S.card / (N : ℝ)^2 +
            2 * ((S.card : ℝ)/N-headMass ρ)^2) := by
      apply Finset.sum_le_sum
      intro S _
      apply mul_le_mul_left'
      dsimp [g]
      rw [hm]
      exact conditional_count_risk ((D.retainedMeasurement S).outcomeMeasure (indexedDensity τ))
        N hN S.card (D.estimator S).estimate (D.estimator S).measurable_estimate τ
        (headMass ρ) (fun hS => D.expected_error S hS τ)
    _ = ENNReal.ofReal ((binomialLaw N (headMass ρ) (headMass_nonneg ρ)
        (headMass_le_one ρ)).expectation (fun m =>
          8 * Fintype.card α * m.val / (N : ℝ)^2 + 2 * ((m.val : ℝ)/N-headMass ρ)^2)) :=
      by
        exact subset_count_lintegral (N := N) ρ
          (fun m : Fin (N+1) => 8 * Fintype.card α * m.val / (N : ℝ)^2 +
            2 * ((m.val : ℝ)/N-headMass ρ)^2) (by intro m; positivity)
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (averaged_count_risk (α := α) N hN _ (headMass_nonneg ρ) (headMass_le_one ρ))


/-- A positive retained sector has Born density0 on a zero-mass block.
This uses the actual tensor compression, with no normalization of R/0. -/
lemma born_zero_of_zero_mass (ρ : Density (α ⊕ β)) (hw : headMass ρ = 0)
    (z : Finset (Fin N) × (∀ S, D.Outcome S)) (hS : z.1.card ≠ 0) :
    (D.measurement (β := β)).born (TensorCopies.density ρ N) z = 0 := by
  have hR : headBlock ρ.matrix = 0 := psd_zero_mass _ (headBlock_posSemidef ρ) hw
  have hc : copies (J := {j : Fin N // j ∈ z.1}) (headBlock ρ.matrix) = 0 := by
    ext x y
    simp [copies, hR, Fintype.card_coe, hS]
  change (Matrix.trace (TensorCopies.matrix ρ.matrix N *
    subsetEffect z.1 ((probabilityVersion (D.retainedMeasurement z.1)).effect (z.2 z.1)))).re = 0
  rw [subset_trace, hc]
  simp

/-- Zero-mass blocks are learned exactly, including under the continuous
retained experiments. Positive retained sectors have actual Born mass0. -/
theorem zero_mass_expected_error (ρ : Density (α ⊕ β)) (hw : headMass ρ = 0) :
    (∫⁻ z, ENNReal.ofReal (frobeniusSq (D.output z - headBlock ρ.matrix))
      ∂(D.measurement (β := β)).outcomeMeasure (TensorCopies.density ρ N)) = 0 := by
  have hR : headBlock ρ.matrix = 0 := psd_zero_mass _ (headBlock_posSemidef ρ) hw
  rw [DominatedPOVM.outcomeMeasure,
    lintegral_withDensity_eq_lintegral_mul _
      ((D.measurement (β := β)).born_measurable _).ennreal_ofReal
      (D.measurable_error ρ).ennreal_ofReal]
  calc
    _ = ∫⁻ z, (0 : ℝ≥0∞) ∂(D.measurement (β := β)).reference := by
      apply lintegral_congr_ae
      apply ae_of_all
      intro z
      by_cases hS : z.1.card = 0
      · simp [D.output_zero_count z hS, hR, frobeniusSq]
      · simp [D.born_zero_of_zero_mass ρ hw z hS]
    _ = 0 := by simp

/-- One prechosen physical experiment has this risk for every density input,
including blocks of mass0 and input coherences across the filter. -/
theorem expected_error_all (hN : 0 < N) (ρ : Density (α ⊕ β)) :
    (∫⁻ z, ENNReal.ofReal (frobeniusSq (D.output z - headBlock ρ.matrix))
      ∂(D.measurement (β := β)).outcomeMeasure (TensorCopies.density ρ N)) ≤
        ENNReal.ofReal (2 * (4 * Fintype.card α + 1) * headMass ρ / N) := by
  by_cases hw : 0 < headMass ρ
  · exact D.full_expected_error hN ρ hw
  · have hz : headMass ρ = 0 := le_antisymm (le_of_not_gt hw) (headMass_nonneg ρ)
    rw [D.zero_mass_expected_error ρ hz]
    exact zero_le _

/-- Uniform3/4 one-batch bound from the actual expected error, counting all
N input copies including rejected ones. -/
theorem three_quarter_success (hN : 0 < N) (ρ : Density (α ⊕ β))
    (W η : ℝ) (hwW : headMass ρ ≤ W) (hη : 0 < η)
    (hcost : 8 * (4 * Fintype.card α + 1) * W ≤ η * N) :
    (3 : ℝ≥0∞)/4 ≤ (D.measurement (β := β)).outcomeMeasure (TensorCopies.density ρ N)
      {z | frobeniusSq (D.output z - headBlock ρ.matrix) ≤ η} := by
  let ν := (D.measurement (β := β)).outcomeMeasure (TensorCopies.density ρ N)
  let f := fun z => frobeniusSq (D.output z - headBlock ρ.matrix)
  have hmean : (∫⁻ z, ENNReal.ofReal (f z) ∂ν) ≤ ENNReal.ofReal (η/4) := by
    apply (D.expected_error_all hN ρ).trans
    apply ENNReal.ofReal_le_ofReal
    apply (div_le_iff₀ (Nat.cast_pos.mpr hN)).mpr
    have hc : 0 ≤ 4 * (Fintype.card α : ℝ) + 1 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hwW hc]
  have hm := meas_ge_le_lintegral_div (μ := ν)
    (D.measurable_error ρ).ennreal_ofReal.aemeasurable
    (ENNReal.ofReal_pos.mpr hη).ne' ENNReal.ofReal_ne_top
  have hbad : ν {z | η < f z} ≤ (1 : ℝ≥0∞)/4 := by
    calc
      _ ≤ ν {z | ENNReal.ofReal η ≤ ENNReal.ofReal (f z)} :=
        measure_mono (fun z hz => ENNReal.ofReal_le_ofReal hz.le)
      _ ≤ (∫⁻ z, ENNReal.ofReal (f z) ∂ν) / ENNReal.ofReal η := hm
      _ ≤ ENNReal.ofReal (η/4) / ENNReal.ofReal η := by gcongr
      _ = _ := by
        rw [← ENNReal.ofReal_div_of_pos hη]
        have he : η/4/η = (1/4 : ℝ) := by field_simp
        rw [he, ENNReal.ofReal_div_of_pos (by norm_num)]
        norm_num
  have hs : MeasurableSet {z | η < f z} := measurableSet_lt measurable_const (D.measurable_error ρ)
  have he : {z | f z ≤ η} = {z | η < f z}ᶜ := by ext z; simp
  change (3 : ℝ≥0∞)/4 ≤ ν {z | f z ≤ η}
  rw [he, measure_compl hs (measure_ne_top _ _), measure_univ]
  have ht := tsub_le_tsub_left hbad (1 : ℝ≥0∞)
  have hv : (1 : ℝ≥0∞)-1/4 = 3/4 :=
    ENNReal.sub_eq_of_eq_add' (by norm_num)
      (by rw [ENNReal.div_add_div_same]; norm_num [ENNReal.div_self])
  rwa [hv] at ht

end RetainedFamily


section OWConstruction
variable {α J : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [Fintype J] [DecidableEq J]

/-- Probability-one dummy measurement for the zero-retained-copy branch. -/
def unitMeasurement (κ : Type*) [Fintype κ] [DecidableEq κ] : DominatedPOVM κ Unit where
  reference := Measure.dirac ()
  reference_finite := inferInstance
  effect _ := 1
  entry_measurable _ _ := measurable_const
  positive_ae := ae_of_all _ fun _ => Matrix.PosSemidef.one
  entry_integrable _ _ := integrable_const _
  total _ _ := by simp

def uniformDensity (α : Type*) [Fintype α] [DecidableEq α] [Nonempty α] : Density α where
  matrix := (Fintype.card α : ℝ)⁻¹ • (1 : Matrix α α ℂ)
  positive := Matrix.PosSemidef.one.smul (inv_nonneg.mpr (Nat.cast_nonneg _))
  trace_one := by
    rw [Matrix.trace_smul, Matrix.trace_one]
    simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

variable {κ η Ω : Type*} [Fintype κ] [DecidableEq κ] [Fintype η] [DecidableEq η]
  [MeasurableSpace Ω]

def reindexMeasurement (e : κ ≃ η) (M : DominatedPOVM η Ω) : DominatedPOVM κ Ω where
  reference := M.reference
  reference_finite := M.reference_finite
  effect y := (M.effect y).submatrix e e
  entry_measurable i j := M.entry_measurable (e i) (e j)
  positive_ae := M.positive_ae.mono fun _ hy => hy.submatrix e
  entry_integrable i j := M.entry_integrable (e i) (e j)
  total i j := by simpa only [Matrix.one_apply, e.injective.eq_iff] using M.total (e i) (e j)

def siteBasisEquiv (e : J ≃ Fin (Fintype.card J)) : (J → α) ≃ (Fin (Fintype.card J) → α) :=
  Equiv.arrowCongr e (Equiv.refl α)

lemma reindex_born (e : J ≃ Fin (Fintype.card J))
    (M : DominatedPOVM (Fin (Fintype.card J) → α) Ω) (τ : Density α) (y : Ω) :
    (reindexMeasurement (siteBasisEquiv (α := α) e) M).born (indexedDensity (J := J) τ) y =
      M.born (TensorCopies.density τ (Fintype.card J)) y := by
  let E := siteBasisEquiv (α := α) e
  have hρ : (indexedDensity (J := J) τ).matrix =
      (TensorCopies.density τ (Fintype.card J)).matrix.submatrix E E := by
    ext x z
    change (∏ j : J, τ.matrix (x j) (z j)) =
      ∏ j : Fin (Fintype.card J), τ.matrix (x (e.symm j)) (z (e.symm j))
    exact (e.symm.prod_comp (fun j => τ.matrix (x j) (z j))).symm
  change (Matrix.trace ((indexedDensity (J := J) τ).matrix * (M.effect y).submatrix E E)).re = _
  rw [hρ, Matrix.submatrix_mul_equiv _ _ E E E]
  have ht : ∀ A : Matrix (Fin (Fintype.card J) → α) (Fin (Fintype.card J) → α) ℂ,
      Matrix.trace (A.submatrix E E) = Matrix.trace A := fun A => E.sum_comp (fun i => A i i)
  rw [ht]
  rfl

lemma reindex_outcomeMeasure (e : J ≃ Fin (Fintype.card J))
    (M : DominatedPOVM (Fin (Fintype.card J) → α) Ω) (τ : Density α) :
    (reindexMeasurement (siteBasisEquiv (α := α) e) M).outcomeMeasure (indexedDensity (J := J) τ) =
      M.outcomeMeasure (TensorCopies.density τ (Fintype.card J)) := by
  unfold DominatedPOVM.outcomeMeasure
  congr 1
  funext y
  rw [reindex_born]

/-- A retained-site experiment, using an arbitrary finite copy-site type. -/
structure RetainedExperiment (α J : Type*) [Fintype α] [DecidableEq α]
    [Fintype J] [DecidableEq J] where
  Outcome : Type
  outcomeMeasurable : MeasurableSpace Outcome
  measurement : @DominatedPOVM (J → α) Outcome _ _ outcomeMeasurable
  estimator : @Estimator α Outcome _ _ outcomeMeasurable
  expected_error : 0 < Fintype.card J → ∀ τ : Density α,
    (∫⁻ y, ENNReal.ofReal (frobeniusSq ((estimator.estimate y).matrix - τ.matrix))
      ∂measurement.outcomeMeasure (indexedDensity τ)) ≤
        ENNReal.ofReal (4 * Fintype.card α / (Fintype.card J : ℝ))
attribute [instance] RetainedExperiment.outcomeMeasurable

/-- Native coordinate transport of the single uniform original OW experiment.
The zero-copy branch is a state-independent unit experiment, with zero final
scaled output. The chosen experiment never depends on the unknown state. -/
def retainedExperiment (O : FrobeniusLearning.OWFrobeniusInput α) : RetainedExperiment α J := by
  classical
  by_cases hJ : 0 < Fintype.card J
  · let A := FrobeniusLearning.chooseExperiment O (Fintype.card J) hJ
    letI := A.outcomeMeasurable
    refine {
      Outcome := A.Outcome
      outcomeMeasurable := A.outcomeMeasurable
      measurement := reindexMeasurement (siteBasisEquiv (Fintype.equivFin J)) A.learner.measurement
      estimator := A.learner.estimator
      expected_error := ?_ }
    intro _ τ
    rw [reindex_outcomeMeasure]
    have h := A.expected_error τ
    have he : ∀ y, frobeniusSq ((A.learner.estimator.estimate y).matrix - τ.matrix) =
        SpectralLoss.frobeniusSq (τ.matrix - (A.learner.estimator.estimate y).matrix) := by
      intro y
      simp only [frobeniusSq, SpectralLoss.frobeniusSq, Complex.normSq_eq_norm_sq, Matrix.sub_apply, norm_sub_rev]
    simp_rw [he]
    apply h.trans
    apply ENNReal.ofReal_le_ofReal
    exact div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  · exact {
      Outcome := Unit
      outcomeMeasurable := inferInstance
      measurement := unitMeasurement (J → α)
      estimator := ⟨fun _ => uniformDensity α, measurable_const⟩
      expected_error := fun h => False.elim (hJ h) }

/-- The entire physical filtering family is fixed before inputρ. -/
def chooseFamily (O : FrobeniusLearning.OWFrobeniusInput α) (N : ℕ) : RetainedFamily α N where
  Outcome S := (retainedExperiment (J := {j : Fin N // j ∈ S}) O).Outcome
  outcomeMeasurable S := (retainedExperiment (J := {j : Fin N // j ∈ S}) O).outcomeMeasurable
  retainedMeasurement S := (retainedExperiment (J := {j : Fin N // j ∈ S}) O).measurement
  estimator S := (retainedExperiment (J := {j : Fin N // j ∈ S}) O).estimator
  expected_error S hS τ := by
    simpa only [Fintype.card_coe] using
      (retainedExperiment (J := {j : Fin N // j ∈ S}) O).expected_error
        (by simpa only [Fintype.card_coe] using hS) τ

end OWConstruction

local instance uniformLabelMeasurableSpace (N : ℕ) : MeasurableSpace (Finset (Fin N)) := ⊤

/-- A single actual physical POVM and measurable PSD matrix estimate, fixed
before every input state, satisfy the source submatrix one-batch guarantee.
The only external parameter is the original uniform normalized OW experiment. -/
theorem uniform_physical_routine {α β : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] [Fintype β] [DecidableEq β]
    (O : FrobeniusLearning.OWFrobeniusInput α) (N : ℕ) (hN : 0 < N)
    (W η : ℝ) (hη : 0 < η)
    (hcost : 8 * (4 * Fintype.card α + 1) * W ≤ η * N) :
    let D := chooseFamily O N
    (∀ z, (D.output z).PosSemidef) ∧ Measurable D.output ∧
    ∀ ρ : Density (α ⊕ β), headMass ρ ≤ W →
      (3 : ℝ≥0∞)/4 ≤ (D.measurement (β := β)).outcomeMeasure (TensorCopies.density ρ N)
        {z | frobeniusSq (D.output z - headBlock ρ.matrix) ≤ η} := by
  dsimp only
  exact ⟨RetainedFamily.output_posSemidef _, RetainedFamily.measurable_output _,
    fun ρ hρ => RetainedFamily.three_quarter_success _ hN ρ W η hρ hη hcost⟩

end Paper26.ContinuousSubmatrixLearning
