import Paper26.AdaptiveModel
import Paper26.CollectiveModel
import Paper26.TensorSLD
import Paper26.AlignedFisherBudget
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.CompProdEqIff

/-!
# Normalizing actual adaptive measurement kernels

This module constructs, rather than assumes, the trace-dominating probability
reference of each actual adaptive step. Its normalized effects have the same
Born transition laws, including zero-trace effects. Actual history-dependent
tensor effects then form a finite-reference collective POVM on the same full
transcript. Its outcome, output and success laws are proved equal to the
adaptive laws, with exactly the same copy count, seed and estimator. No
protocol-equivalence, Fisher or success bound is an input. The arbitrary-POVM-
family joint RN question remains separate from this dominated representation.
-/

noncomputable section

namespace Paper26.AdaptiveCollectiveEmbedding

open MeasureTheory ProbabilityTheory QuantumModel ContinuousPOVM AdaptiveModel
open scoped BigOperators ComplexOrder ENNReal Matrix

variable {ι H Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace H] [MeasurableSpace Ω]

/-- The actual maximally mixed state, used only for a parameter-free reference. -/
def uniformState (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] : Density ι where
  matrix := (Fintype.card ι : ℝ)⁻¹ • (1 : Matrix ι ι ℂ)
  positive := Matrix.PosSemidef.one.smul (inv_nonneg.mpr (Nat.cast_nonneg _))
  trace_one := by
    rw [Matrix.trace_smul, Matrix.trace_one]
    simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

omit [Nonempty ι] in
/-- Every entry of a PSD matrix is bounded by its real trace. -/
theorem psd_entry_norm_le_trace (E : Matrix ι ι ℂ) (hE : E.PosSemidef) (i j : ι) :
    ‖E i j‖ ≤ E.trace.re := by
  have hd := AlignedFisherBudget.psd_diagonal_nonneg E hE
  have ht : E.trace.re = ∑ k, (E k k).re := by simp [Matrix.trace]
  have hi : (E i i).re ≤ E.trace.re := by
    rw [ht]
    exact Finset.single_le_sum (fun k _ => hd k) (Finset.mem_univ i)
  have hj : (E j j).re ≤ E.trace.re := by
    rw [ht]
    exact Finset.single_le_sum (fun k _ => hd k) (Finset.mem_univ j)
  have hn : 0 ≤ E.trace.re := le_trans (hd i) hi
  have he := AlignedFisherBudget.psd_entry_normSq_le E hE i j
  rw [Complex.normSq_eq_norm_sq] at he
  have hm := mul_le_mul hi hj (hd j) hn
  nlinarith [norm_nonneg (E i j)]

end Paper26.AdaptiveCollectiveEmbedding

namespace Paper26.AdaptiveModel.OneCopyStep

open MeasureTheory ProbabilityTheory QuantumModel ContinuousPOVM AdaptiveCollectiveEmbedding
open scoped BigOperators ComplexOrder ENNReal Matrix
variable {ι H Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace H] [MeasurableSpace Ω]
variable (M : AdaptiveModel.OneCopyStep ι H Ω)

theorem uniform_born (h : H) (y : Ω) :
    M.born (uniformState ι) h y =
      (Fintype.card ι : ℝ)⁻¹ * (M.effect h y).trace.re := by
  simp [AdaptiveModel.OneCopyStep.born, AdaptiveModel.OneCopyStep.complexBorn,
    uniformState, Matrix.trace_smul, Complex.real_smul]

theorem trace_eq_dim_mul_uniform_born (h : H) (y : Ω) :
    (M.effect h y).trace.re = (Fintype.card ι : ℝ) * M.born (uniformState ι) h y := by
  rw [M.uniform_born]
  field_simp

/-- A trace-zero PSD effect is the zero matrix; no output branch is discarded. -/
theorem effect_eq_zero_of_uniform_born_zero (h : H) (y : Ω)
    (hE : (M.effect h y).PosSemidef) (hz : M.born (uniformState ι) h y = 0) :
    M.effect h y = 0 := by
  apply hE.trace_eq_zero_iff.mp
  apply Complex.ext
  · rw [M.trace_eq_dim_mul_uniform_born, hz, mul_zero]
    rfl
  · exact (RCLike.nonneg_iff.mp hE.trace_nonneg).2

/-- F=E / Born(uniform), totalized by inv0=0. -/
def normalizedEffect (h : H) (y : Ω) : Matrix ι ι ℂ :=
  (M.born (uniformState ι) h y)⁻¹ • M.effect h y

theorem normalizedEffect_entry_measurable (i j : ι) :
    Measurable (fun z : H × Ω => M.normalizedEffect z.1 z.2 i j) :=
  (M.born_joint_measurable (uniformState ι)).inv.smul (M.entry_measurable i j)

theorem normalizedEffect_posSemidef_ae (h : H) :
    ∀ᵐ y ∂M.reference h, (M.normalizedEffect h y).PosSemidef := by
  filter_upwards [M.positive_ae h, M.born_nonneg_ae (uniformState ι) h] with y hE hb
  exact hE.smul (inv_nonneg.mpr hb)

/-- Multiplying back by the scalar reference density recovers the actual
matrix effect, even at a zero-trace outcome. -/
theorem uniform_born_smul_normalizedEffect_ae (h : H) :
    ∀ᵐ y ∂M.reference h,
      M.born (uniformState ι) h y • M.normalizedEffect h y = M.effect h y := by
  filter_upwards [M.positive_ae h] with y hE
  by_cases hz : M.born (uniformState ι) h y = 0
  · rw [hz, zero_smul, M.effect_eq_zero_of_uniform_born_zero h y hE hz]
  · rw [normalizedEffect, smul_smul, mul_inv_cancel₀ hz, one_smul]

theorem normalizedEffect_entry_integrable (h : H) (i j : ι) :
    Integrable (fun y => M.normalizedEffect h y i j) (M.bornKernel (uniformState ι) h) := by
  rw [M.bornKernel_apply]
  apply (integrable_withDensity_iff_integrable_smul'
    (M.born_measurable (uniformState ι) h).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).2
  apply (M.entry_integrable h i j).congr
  filter_upwards [M.uniform_born_smul_normalizedEffect_ae h,
    M.born_nonneg_ae (uniformState ι) h] with y he hb
  rw [ENNReal.toReal_ofReal hb]
  exact (congrFun (congrFun he i) j).symm

theorem normalizedEffect_integral (h : H) (i j : ι) :
    ∫ y, M.normalizedEffect h y i j ∂M.bornKernel (uniformState ι) h =
      (1 : Matrix ι ι ℂ) i j := by
  rw [M.bornKernel_apply, integral_withDensity_eq_integral_toReal_smul
    (M.born_measurable (uniformState ι) h).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  calc
    _ = ∫ y, M.effect h y i j ∂M.reference h := by
      apply integral_congr_ae
      filter_upwards [M.uniform_born_smul_normalizedEffect_ae h,
        M.born_nonneg_ae (uniformState ι) h] with y he hb
      rw [ENNReal.toReal_ofReal hb]
      exact congrFun (congrFun he i) j
    _ = _ := M.total h i j

/-- Normalized effects always have real trace either0 or the dimension. -/
theorem normalizedEffect_trace_le (h : H) (y : Ω) :
    (M.normalizedEffect h y).trace.re ≤ Fintype.card ι := by
  change ((M.born (uniformState ι) h y)⁻¹ • M.effect h y).trace.re ≤ _
  rw [Matrix.trace_smul]
  simp only [Complex.smul_re, smul_eq_mul]
  change (M.born (uniformState ι) h y)⁻¹ * (M.effect h y).trace.re ≤ _
  rw [M.trace_eq_dim_mul_uniform_born]
  by_cases hz : M.born (uniformState ι) h y = 0
  · simp [hz]
  · have he : (M.born (uniformState ι) h y)⁻¹ *
        ((Fintype.card ι : ℝ) * M.born (uniformState ι) h y) = Fintype.card ι := by
      field_simp
    exact he.le

/-- The normalized adaptive step has a genuine probability reference kernel.
Probability and totalI are derived from the original actual POVM conditions. -/
def normalize : AdaptiveModel.OneCopyStep ι H Ω where
  reference := M.bornKernel (uniformState ι)
  reference_sfinite := inferInstance
  effect := M.normalizedEffect
  entry_measurable := M.normalizedEffect_entry_measurable
  positive_ae h := by
    apply (show M.bornKernel (uniformState ι) h ≪ M.reference h from by
      rw [M.bornKernel_apply]
      exact withDensity_absolutelyContinuous _ _).ae_le
    exact M.normalizedEffect_posSemidef_ae h
  entry_integrable := M.normalizedEffect_entry_integrable
  total := M.normalizedEffect_integral

instance normalized_reference_isMarkovKernel : IsMarkovKernel M.normalize.reference :=
  inferInstanceAs (IsMarkovKernel (M.bornKernel (uniformState ι)))

theorem normalizedEffect_entry_norm_le_ae (h : H) (i j : ι) :
    ∀ᵐ y ∂M.normalize.reference h, ‖M.normalize.effect h y i j‖ ≤ Fintype.card ι := by
  filter_upwards [M.normalize.positive_ae h] with y hy
  exact (psd_entry_norm_le_trace _ hy i j).trans (M.normalizedEffect_trace_le h y)

/-- Normalizing the reference and the effects preserves every actual Born
transition law. The zero-trace branch is handled by PSD trace0⇒effect0. -/
theorem normalize_bornKernel (ρ : Density ι) : M.normalize.bornKernel ρ = M.bornKernel ρ := by
  apply Kernel.ext
  intro h
  rw [M.normalize.bornKernel_apply, M.bornKernel_apply ρ h]
  change (M.bornKernel (uniformState ι) h).withDensity
    (fun y => ENNReal.ofReal (M.normalize.born ρ h y)) = _
  rw [M.bornKernel_apply]
  rw [← withDensity_mul _ (M.born_measurable (uniformState ι) h).ennreal_ofReal
    (M.normalize.born_measurable ρ h).ennreal_ofReal]
  apply withDensity_congr_ae
  filter_upwards [M.uniform_born_smul_normalizedEffect_ae h,
    M.born_nonneg_ae (uniformState ι) h] with y he hb
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul hb]
  congr 1
  have ht := congrArg (fun X : Matrix ι ι ℂ => (Matrix.trace (ρ.matrix * X)).re) he
  simpa only [Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re,
    AdaptiveModel.OneCopyStep.born, AdaptiveModel.OneCopyStep.complexBorn,
    normalize] using ht

end Paper26.AdaptiveModel.OneCopyStep

namespace Paper26.AdaptiveCollectiveEmbedding

open MeasureTheory ProbabilityTheory QuantumModel ContinuousPOVM AdaptiveModel
open scoped BigOperators ComplexOrder ENNReal Matrix

universe u
variable {ι : Type*} {Seed Ω : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace Seed] [MeasurableSpace Ω] {n : ℕ}

/-- The same actual adaptive experiment, with trace-probability reference at
all steps. Its estimator and parameter-independent seed are unchanged. -/
def normalizedLearner (A : AdaptiveModel.Learner ι Seed Ω n) :
    AdaptiveModel.Learner ι Seed Ω n where
  seed := A.seed
  seed_probability := A.seed_probability
  step k := (A.step k).normalize
  estimator := A.estimator

theorem normalizedLearner_prefixLaw (A : AdaptiveModel.Learner ι Seed Ω n)
    (ρ : Density ι) (k : ℕ) (hk : k ≤ n) :
    (normalizedLearner A).prefixLaw ρ k hk = A.prefixLaw ρ k hk := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change ((normalizedLearner A).prefixLaw ρ k
        (Nat.le_trans (Nat.le_succ k) hk)).compProd
          ((A.step ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩).normalize.bornKernel ρ) = _
      rw [ih _, AdaptiveModel.OneCopyStep.normalize_bornKernel]
      rfl

theorem normalizedLearner_transcriptLaw (A : AdaptiveModel.Learner ι Seed Ω n)
    (ρ : Density ι) :
    (normalizedLearner A).transcriptLaw ρ = A.transcriptLaw ρ :=
  normalizedLearner_prefixLaw A ρ n _

theorem normalizedLearner_outputLaw (A : AdaptiveModel.Learner ι Seed Ω n)
    (ρ : Density ι) :
    (normalizedLearner A).outputLaw ρ = A.outputLaw ρ := by
  change ((normalizedLearner A).transcriptLaw ρ).map A.estimator.estimate = _
  rw [normalizedLearner_transcriptLaw]
  rfl

theorem normalizedLearner_successProbability (A : AdaptiveModel.Learner ι Seed Ω n)
    (loss : Density ι → Density ι → ℝ≥0∞) (ρ : Density ι) (ε : ℝ≥0∞) :
    (normalizedLearner A).successProbability loss ρ ε = A.successProbability loss ρ ε := by
  change (normalizedLearner A).transcriptLaw ρ (A.successSet loss ρ ε) = _
  rw [normalizedLearner_transcriptLaw]
  rfl

local instance matrixMeasurableSpace (σ τ : Type*) : MeasurableSpace (Matrix σ τ ℂ) :=
  inferInstanceAs (MeasurableSpace (σ → τ → ℂ))
local instance matrixBorelSpace (σ τ : Type*) [Fintype σ] [Fintype τ] :
    BorelSpace (Matrix σ τ ℂ) := inferInstanceAs (BorelSpace (σ → τ → ℂ))

omit [DecidableEq ι] [Nonempty ι] in
/-- Positivity is a Borel condition on actual finite matrix entries. -/
theorem isClosed_setOf_posSemidef : IsClosed {E : Matrix ι ι ℂ | E.PosSemidef} := by
  change IsClosed {E : Matrix ι ι ℂ | Eᴴ = E ∧ ∀ v, 0 ≤ star v ⬝ᵥ E *ᵥ v}
  simp only [Set.setOf_and, Set.setOf_forall]
  apply IsClosed.inter
  · exact isClosed_eq (by fun_prop) continuous_id
  · apply isClosed_iInter
    intro v
    exact isClosed_le continuous_const (by fun_prop)

omit [DecidableEq ι] [Nonempty ι] in
theorem measurableSet_posSemidef_of_entries {X : Type*} [MeasurableSpace X]
    (E : X → Matrix ι ι ℂ) (hm : ∀ i j, Measurable (fun x => E x i j)) :
    MeasurableSet {x | (E x).PosSemidef} :=
  (isClosed_setOf_posSemidef (ι := ι)).measurableSet.preimage
    (measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => hm i j)

/-- The normalized one-copy matrix encountered at every site of a complete
prefix. The new last factor sees all of the old history. -/
def siteEffect (A : AdaptiveModel.Learner ι Seed Ω n) :
    (k : ℕ) → k ≤ n → History Seed Ω k → Fin k → Matrix ι ι ℂ
  | 0, _ => fun _ j => Fin.elim0 j
  | k + 1, hk => fun z => Fin.lastCases
      ((A.step ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩).normalizedEffect z.1 z.2)
      (siteEffect A k (Nat.le_trans (Nat.le_succ k) hk) z.1)

/-- The actual collective tensor effect associated with a prefix. -/
def effectProduct (A : AdaptiveModel.Learner ι Seed Ω n) (k : ℕ) (hk : k ≤ n)
    (z : History Seed Ω k) : Matrix (Fin k → ι) (Fin k → ι) ℂ :=
  TensorSLD.tensor (siteEffect A k hk z)

theorem siteEffect_entry_measurable (A : AdaptiveModel.Learner ι Seed Ω n)
    (k : ℕ) (hk : k ≤ n) (j : Fin k) (a b : ι) :
    Measurable (fun z => siteEffect A k hk z j a b) := by
  induction k with
  | zero => exact Fin.elim0 j
  | succ k ih =>
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa only [siteEffect, Fin.lastCases_last] using
          (A.step ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩).normalizedEffect_entry_measurable a b
      · simpa only [siteEffect, Fin.lastCases_castSucc] using
          (ih (Nat.le_trans (Nat.le_succ k) hk) j).comp measurable_fst

theorem effectProduct_entry_measurable (A : AdaptiveModel.Learner ι Seed Ω n)
    (k : ℕ) (hk : k ≤ n) (x y : Fin k → ι) :
    Measurable (fun z => effectProduct A k hk z x y) := by
  exact Finset.measurable_prod Finset.univ fun j _ =>
    siteEffect_entry_measurable A k hk j (x j) (y j)

theorem siteEffect_trace_le (A : AdaptiveModel.Learner ι Seed Ω n)
    (k : ℕ) (hk : k ≤ n) (z : History Seed Ω k) (j : Fin k) :
    (siteEffect A k hk z j).trace.re ≤ Fintype.card ι := by
  induction k with
  | zero => exact Fin.elim0 j
  | succ k ih =>
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa only [siteEffect, Fin.lastCases_last] using
          (A.step ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩).normalizedEffect_trace_le z.1 z.2
      · simpa only [siteEffect, Fin.lastCases_castSucc] using ih _ z.1 j

/-- Every encountered one-copy effect is PSD almost everywhere under the
parameter-free uniform-input transcript reference law. -/
theorem siteEffect_posSemidef_ae (A : AdaptiveModel.Learner ι Seed Ω n)
    (k : ℕ) (hk : k ≤ n) :
    ∀ᵐ z ∂A.prefixLaw (uniformState ι) k hk, ∀ j, (siteEffect A k hk z j).PosSemidef := by
  induction k with
  | zero => exact Filter.Eventually.of_forall fun _ j => Fin.elim0 j
  | succ k ih =>
      change ∀ᵐ z ∂(A.prefixLaw (uniformState ι) k
        (Nat.le_trans (Nat.le_succ k) hk)).compProd
          ((A.step ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩).bornKernel (uniformState ι)), ∀ j, (siteEffect A (k + 1) hk z j).PosSemidef
      apply Measure.ae_compProd_of_ae_ae
      · simp only [Set.setOf_forall]
        exact MeasurableSet.iInter fun j => measurableSet_posSemidef_of_entries _
          (siteEffect_entry_measurable A (k + 1) hk j)
      · filter_upwards [ih (Nat.le_trans (Nat.le_succ k) hk)] with z hz
        filter_upwards [(A.step ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩).normalize.positive_ae z] with y hy
        intro j
        refine Fin.lastCases ?_ (fun j => ?_) j
        · simpa only [siteEffect, Fin.lastCases_last] using hy
        · simpa only [siteEffect, Fin.lastCases_castSucc] using hz j

omit [Nonempty ι] in
/-- Finite tensor products of actual PSD matrices are PSD, by native Gram
factors and the proved finite-product multiplication identities. -/
theorem tensor_posSemidef {k : ℕ} (E : Fin k → Matrix ι ι ℂ)
    (hE : ∀ j, (E j).PosSemidef) : (TensorSLD.tensor E).PosSemidef := by
  choose R hR using fun j => TensorCopies.psd_exists_gram (E j) (hE j)
  have he : TensorSLD.tensor E = (TensorSLD.tensor R)ᴴ * TensorSLD.tensor R := by
    rw [← TensorSLD.tensor_conjTranspose, ← TensorSLD.tensor_mul]
    congr 1
    funext j
    exact (hR j).symm
  rw [he]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem effectProduct_posSemidef_ae (A : AdaptiveModel.Learner ι Seed Ω n)
    (k : ℕ) (hk : k ≤ n) :
    ∀ᵐ z ∂A.prefixLaw (uniformState ι) k hk, (effectProduct A k hk z).PosSemidef :=
  (siteEffect_posSemidef_ae A k hk).mono fun _ hz => tensor_posSemidef _ hz

theorem effectProduct_entry_bound_ae (A : AdaptiveModel.Learner ι Seed Ω n)
    (k : ℕ) (hk : k ≤ n) (x y : Fin k → ι) :
    ∀ᵐ z ∂A.prefixLaw (uniformState ι) k hk,
      ‖effectProduct A k hk z x y‖ ≤ (Fintype.card ι : ℝ) ^ k := by
  filter_upwards [siteEffect_posSemidef_ae A k hk] with z hz
  change ‖∏ j, siteEffect A k hk z j (x j) (y j)‖ ≤ _
  rw [norm_prod]
  calc
    (∏ j, ‖siteEffect A k hk z j (x j) (y j)‖) ≤ ∏ _j : Fin k, (Fintype.card ι : ℝ) := by
      apply Finset.prod_le_prod
      · intro j _
        exact norm_nonneg _
      · intro j _
        exact (psd_entry_norm_le_trace _ (hz j) _ _).trans (siteEffect_trace_le A k hk z j)
    _ = (Fintype.card ι : ℝ) ^ k := by simp

theorem effectProduct_entry_integrable (A : AdaptiveModel.Learner ι Seed Ω n)
    (k : ℕ) (hk : k ≤ n) (x y : Fin k → ι) :
    Integrable (fun z => effectProduct A k hk z x y)
      (A.prefixLaw (uniformState ι) k hk) :=
  (integrable_const ((Fintype.card ι : ℝ) ^ k)).mono'
    (effectProduct_entry_measurable A k hk x y).aestronglyMeasurable
    (effectProduct_entry_bound_ae A k hk x y)

/-- Last-coordinate expansion of the actual tensor effect. -/
theorem effectProduct_succ_apply (A : AdaptiveModel.Learner ι Seed Ω n)
    (k : ℕ) (hk : k + 1 ≤ n) (z : History Seed Ω k × Ω)
    (x y : Fin (k + 1) → ι) :
    effectProduct A (k + 1) hk z x y =
      effectProduct A k (Nat.le_trans (Nat.le_succ k) hk) z.1
        (fun j => x j.castSucc) (fun j => y j.castSucc) *
      (A.step ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩).normalizedEffect
        z.1 z.2 (x (Fin.last k)) (y (Fin.last k)) := by
  unfold effectProduct TensorSLD.tensor
  rw [Fin.prod_univ_castSucc]
  simp only [siteEffect, Fin.lastCases_last, Fin.lastCases_castSucc]

omit [Fintype ι] [Nonempty ι] in
/-- Identity deltas split into their old and last coordinates. -/
theorem identity_last_split (k : ℕ) (x y : Fin (k + 1) → ι) :
    (1 : Matrix (Fin k → ι) (Fin k → ι) ℂ)
        (fun j => x j.castSucc) (fun j => y j.castSucc) *
      (1 : Matrix ι ι ℂ) (x (Fin.last k)) (y (Fin.last k)) =
        (1 : Matrix (Fin (k + 1) → ι) (Fin (k + 1) → ι) ℂ) x y := by
  classical
  have he : x = y ↔
      ((fun j : Fin k => x j.castSucc) = (fun j : Fin k => y j.castSucc) ∧
        x (Fin.last k) = y (Fin.last k)) := by
    constructor
    · intro h
      subst y
      exact ⟨rfl, rfl⟩
    · intro h
      funext j
      refine Fin.lastCases h.2 (fun j => congrFun h.1 j) j
  simp only [Matrix.one_apply]
  by_cases ha : (fun j : Fin k => x j.castSucc) = (fun j : Fin k => y j.castSucc)
  · by_cases hb : x (Fin.last k) = y (Fin.last k)
    · simp [he.mpr ⟨ha, hb⟩]
    · have hxy : x ≠ y := fun h => hb (he.mp h).2
      simp [ha, hb, hxy]
  · have hxy : x ≠ y := fun h => ha (he.mp h).1
    simp [ha, hxy]

/-- Integrating the tensor effects gives the actual identity matrix. All
entries are already proved integrable by their dimension bound. -/
theorem effectProduct_integral (A : AdaptiveModel.Learner ι Seed Ω n)
    (k : ℕ) (hk : k ≤ n) (x y : Fin k → ι) :
    (∫ z, effectProduct A k hk z x y ∂A.prefixLaw (uniformState ι) k hk) =
      (1 : Matrix (Fin k → ι) (Fin k → ι) ℂ) x y := by
  induction k with
  | zero =>
      have hxy : x = y := Subsingleton.elim x y
      simp [effectProduct, TensorSLD.tensor, AdaptiveModel.Learner.prefixLaw, Matrix.one_apply, hxy]
  | succ k ih =>
      have hi := effectProduct_entry_integrable A (k + 1) hk x y
      change Integrable (fun z : History Seed Ω k × Ω => effectProduct A (k + 1) hk z x y)
        ((A.prefixLaw (uniformState ι) k (Nat.le_trans (Nat.le_succ k) hk)).compProd
          ((A.step ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩).bornKernel (uniformState ι))) at hi
      change (∫ z : History Seed Ω k × Ω, effectProduct A (k + 1) hk z x y
        ∂(A.prefixLaw (uniformState ι) k (Nat.le_trans (Nat.le_succ k) hk)).compProd
          ((A.step ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩).bornKernel (uniformState ι))) = _
      rw [Measure.integral_compProd hi]
      simp_rw [effectProduct_succ_apply, integral_const_mul,
        AdaptiveModel.OneCopyStep.normalizedEffect_integral]
      rw [integral_mul_const, ih _ _ _]
      exact identity_last_split k x y

/-- A genuine finite-reference collective POVM for every adaptive prefix. -/
def prefixMeasurement (A : AdaptiveModel.Learner ι Seed Ω n) (k : ℕ) (hk : k ≤ n) :
    DominatedPOVM (Fin k → ι) (History Seed Ω k) where
  reference := A.prefixLaw (uniformState ι) k hk
  reference_finite := inferInstance
  effect := effectProduct A k hk
  entry_measurable := effectProduct_entry_measurable A k hk
  positive_ae := effectProduct_posSemidef_ae A k hk
  entry_integrable := effectProduct_entry_integrable A k hk
  total := effectProduct_integral A k hk

/-- Actual collective measurement and estimator on the same full transcript.
The law-equivalence theorem below is a deduction, never a protocol field. -/
def collectiveLearner (A : AdaptiveModel.Learner ι Seed Ω n) :
    CollectiveModel.Learner ι (History Seed Ω n) n where
  measurement := prefixMeasurement A n (Nat.le_refl n)
  estimator := A.estimator

omit [DecidableEq ι] [Nonempty ι] in
/-- Trace factorization is the actual tensor product trace, with no model
factorization assumption. -/
theorem trace_tensor_mul (ρ : Density ι) {k : ℕ} (E : Fin k → Matrix ι ι ℂ) :
    Matrix.trace (TensorCopies.matrix ρ.matrix k * TensorSLD.tensor E) =
      ∏ j, Matrix.trace (ρ.matrix * E j) := by
  change Matrix.trace (TensorSLD.tensor (fun _ : Fin k => ρ.matrix) * TensorSLD.tensor E) = _
  rw [← TensorSLD.tensor_mul, TensorSLD.tensor_trace]

/-- Actual complex Born traces factor under the history-dependent tensor
construction. Positivity is unnecessary for this algebraic equality. -/
theorem prefix_complexBorn_succ (A : AdaptiveModel.Learner ι Seed Ω n)
    (ρ : Density ι) (k : ℕ) (hk : k + 1 ≤ n) (z : History Seed Ω k × Ω) :
    (prefixMeasurement A (k + 1) hk).complexBorn (TensorCopies.density ρ (k + 1)) z =
      (prefixMeasurement A k (Nat.le_trans (Nat.le_succ k) hk)).complexBorn
        (TensorCopies.density ρ k) z.1 *
      (A.step ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩).normalize.complexBorn
        ρ z.1 z.2 := by
  change Matrix.trace (TensorCopies.matrix ρ.matrix (k + 1) *
    TensorSLD.tensor (siteEffect A (k + 1) hk z)) =
      Matrix.trace (TensorCopies.matrix ρ.matrix k *
        TensorSLD.tensor (siteEffect A k (Nat.le_trans (Nat.le_succ k) hk) z.1)) * _
  rw [trace_tensor_mul, trace_tensor_mul, Fin.prod_univ_castSucc]
  simp only [siteEffect, Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

/-- The last normalized effect is PSD at almost every reference transcript,
so the complex trace factorization gives actual nonnegative Born factors. -/
theorem prefix_bornWeight_succ_ae (A : AdaptiveModel.Learner ι Seed Ω n)
    (ρ : Density ι) (k : ℕ) (hk : k + 1 ≤ n) :
    ∀ᵐ z ∂A.prefixLaw (uniformState ι) (k + 1) hk,
      ENNReal.ofReal ((prefixMeasurement A (k + 1) hk).born (TensorCopies.density ρ (k + 1)) z) =
        ENNReal.ofReal ((A.step ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩).normalize.born
          ρ z.1 z.2) *
        ENNReal.ofReal ((prefixMeasurement A k (Nat.le_trans (Nat.le_succ k) hk)).born
          (TensorCopies.density ρ k) z.1) := by
  filter_upwards [siteEffect_posSemidef_ae A (k + 1) hk] with z hz
  have hp : ((A.step ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩).normalize.effect z.1 z.2).PosSemidef := by
    simpa only [siteEffect, Fin.lastCases_last] using hz (Fin.last k)
  have him := EnergyReality.trace_hermitian_product_im ρ.matrix _ ρ.hermitian.eq hp.isHermitian.eq
  have hnon := QuantumModel.trace_mul_effect_nonneg ρ hp
  have he : (prefixMeasurement A (k + 1) hk).born (TensorCopies.density ρ (k + 1)) z =
      (prefixMeasurement A k (Nat.le_trans (Nat.le_succ k) hk)).born (TensorCopies.density ρ k) z.1 *
        (A.step ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩).normalize.born ρ z.1 z.2 := by
    change ((prefixMeasurement A (k + 1) hk).complexBorn (TensorCopies.density ρ (k + 1)) z).re = _
    rw [prefix_complexBorn_succ, Complex.mul_re]
    change _ - _ * (Matrix.trace (ρ.matrix *
      (A.step ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩).normalize.effect z.1 z.2)).im = _
    rw [him, mul_zero, sub_zero]
    rfl
  change 0 ≤ (A.step ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩).normalize.born ρ z.1 z.2 at hnon
  rw [he, mul_comm, ENNReal.ofReal_mul hnon]

/-- Moving a finite-valued density from the preceding history into a kernel
extension is an actual measure identity on arbitrary measurable spaces. -/
theorem compProd_withDensity_left {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ]
    (f : α → ℝ≥0∞) (hf : Measurable f) (hfin : ∀ a, f a ≠ ∞) :
    (μ.withDensity f).compProd κ =
      (μ.compProd κ).withDensity (fun z => f z.1) := by
  letI : IsSFiniteKernel (κ.withDensity (fun a _ => f a)) :=
    Kernel.IsSFiniteKernel.withDensity κ (fun a _ => hfin a)
  calc
    (μ.withDensity f).compProd κ = μ.compProd (κ.withDensity (fun a _ => f a)) := by
      ext S hS
      rw [Measure.compProd_apply hS,
        lintegral_withDensity_eq_lintegral_mul μ hf (Kernel.measurable_kernel_prodMk_left hS),
        Measure.compProd_apply hS]
      apply lintegral_congr
      intro a
      rw [Kernel.withDensity_apply' κ (f := fun a (_ : β) => f a) (hf.comp measurable_fst) a]
      simp
    _ = (μ.compProd κ).withDensity (fun z => f z.1) :=
      Measure.compProd_withDensity (hf.comp measurable_fst)

/-- The constructed collective prefix POVM has precisely the original
adaptive Born prefix law, for every actual input density. -/
theorem prefixMeasurement_outcomeMeasure (A : AdaptiveModel.Learner ι Seed Ω n)
    (ρ : Density ι) (k : ℕ) (hk : k ≤ n) :
    (prefixMeasurement A k hk).outcomeMeasure (TensorCopies.density ρ k) =
      A.prefixLaw ρ k hk := by
  induction k with
  | zero =>
      have hb : ∀ z, (prefixMeasurement A 0 hk).born (TensorCopies.density ρ 0) z = 1 := by
        intro z
        simp [DominatedPOVM.born, DominatedPOVM.complexBorn, prefixMeasurement,
          effectProduct, TensorSLD.tensor, TensorCopies.density, TensorCopies.matrix,
          Matrix.trace, Matrix.mul_apply]
      change (A.prefixLaw (uniformState ι) 0 hk).withDensity
        (fun z => ENNReal.ofReal ((prefixMeasurement A 0 hk).born (TensorCopies.density ρ 0) z)) = _
      simp_rw [hb, ENNReal.ofReal_one]
      change (A.prefixLaw (uniformState ι) 0 hk).withDensity (1 : History Seed Ω 0 → ℝ≥0∞) = _
      rw [withDensity_one]
      rfl
  | succ k ih =>
      let hp : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      let index : Fin n := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      let μ : Measure (History Seed Ω k) := A.prefixLaw (uniformState ι) k hp
      let β : Kernel (History Seed Ω k) Ω := (A.step index).bornKernel (uniformState ι)
      let f : History Seed Ω k → ℝ≥0∞ := fun h => ENNReal.ofReal
        ((prefixMeasurement A k hp).born (TensorCopies.density ρ k) h)
      let q : History Seed Ω k → Ω → ℝ≥0∞ := fun h y => ENNReal.ofReal
        ((A.step index).normalize.born ρ h y)
      have hf : Measurable f := ((prefixMeasurement A k hp).born_measurable _).ennreal_ofReal
      have hq : Measurable (Function.uncurry q) :=
        ((A.step index).normalize.born_joint_measurable ρ).ennreal_ofReal
      have hstep : β.withDensity q = (A.step index).bornKernel ρ :=
        (A.step index).normalize_bornKernel ρ
      letI : IsMarkovKernel (β.withDensity q) := by rw [hstep]; infer_instance
      have hprev := ih hp
      change μ.withDensity f = A.prefixLaw ρ k hp at hprev
      change (μ.compProd β).withDensity
        (fun z => ENNReal.ofReal ((prefixMeasurement A (k + 1) hk).born
          (TensorCopies.density ρ (k + 1)) z)) = _
      calc
        (μ.compProd β).withDensity
            (fun z => ENNReal.ofReal ((prefixMeasurement A (k + 1) hk).born
              (TensorCopies.density ρ (k + 1)) z)) =
            (μ.compProd β).withDensity (fun z => q z.1 z.2 * f z.1) :=
          withDensity_congr_ae (prefix_bornWeight_succ_ae A ρ k hk)
        _ = ((μ.compProd β).withDensity (Function.uncurry q)).withDensity (fun z => f z.1) :=
          by
            have he := withDensity_mul (μ.compProd β) (f := Function.uncurry q)
              (g := fun z => f z.1) hq (hf.comp measurable_fst)
            simpa only [Pi.mul_apply, Function.uncurry_apply_pair] using he
        _ = (μ.compProd (β.withDensity q)).withDensity (fun z => f z.1) := by
          rw [Measure.compProd_withDensity hq]
          rfl
        _ = (μ.withDensity f).compProd (β.withDensity q) :=
          (compProd_withDensity_left μ _ f hf (fun _ => ENNReal.ofReal_ne_top)).symm
        _ = (A.prefixLaw ρ k hp).compProd ((A.step index).bornKernel ρ) := by
          rw [hprev, hstep]
        _ = A.prefixLaw ρ (k + 1) hk := rfl

/-- Exact adaptive-to-collective law equivalence on the same full transcript. -/
theorem collectiveLearner_outcomeMeasure (A : AdaptiveModel.Learner ι Seed Ω n)
    (ρ : Density ι) : (collectiveLearner A).outcomeMeasure ρ = A.transcriptLaw ρ :=
  prefixMeasurement_outcomeMeasure A ρ n _

theorem collectiveLearner_outputMeasure (A : AdaptiveModel.Learner ι Seed Ω n)
    (ρ : Density ι) : (collectiveLearner A).outputMeasure ρ = A.outputLaw ρ := by
  change ((collectiveLearner A).outcomeMeasure ρ).map A.estimator.estimate = _
  rw [collectiveLearner_outcomeMeasure]
  rfl

/-- Every actual successful transcript event has exactly the same measure. -/
theorem collectiveLearner_successProbability (A : AdaptiveModel.Learner ι Seed Ω n)
    (loss : Density ι → Density ι → ℝ≥0∞) (ρ : Density ι) (ε : ℝ≥0∞) :
    (collectiveLearner A).successProbability loss ρ ε = A.successProbability loss ρ ε := by
  change (collectiveLearner A).outcomeMeasure ρ (A.successSet loss ρ ε) = _
  rw [collectiveLearner_outcomeMeasure]
  rfl

/-- The exact rank promise and confidence guarantee transfer with all copies
counted; no additional output rank or success premise is introduced. -/
theorem collectiveLearner_learnsRank_iff (A : AdaptiveModel.Learner ι Seed Ω n)
    (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε q : ℝ≥0∞) :
    (collectiveLearner A).LearnsRank loss r ε q ↔ A.LearnsRank loss r ε q := by
  unfold CollectiveModel.Learner.LearnsRank AdaptiveModel.Learner.LearnsRank
  simp_rw [collectiveLearner_successProbability]
  rfl

end Paper26.AdaptiveCollectiveEmbedding
