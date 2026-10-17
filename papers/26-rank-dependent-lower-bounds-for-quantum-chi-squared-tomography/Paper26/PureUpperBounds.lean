import Paper26.PureCovariant
import Paper26.JordanLossMeasurability

/-! Section 4's actual regularized covariant learners and their
constant-confidence pure-state copy bounds. The statistical tail mean is
proved in PureCovariant, not assumed as a probability input. -/
noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal
open MeasureTheory

namespace Paper26.PureUpperBounds
open QuantumModel HaarFrames PureCovariant CollectiveModel ContinuousPOVM
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance matrixMeasurableSpace (m n : Type*) : MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))

/-- The actual regularized output for each measured direction. -/
def output (m : ℕ) (hm : 0 < m) (hd : Fintype.card ι = m + 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (V : Frame ι (Fin 1)) : Density ι :=
  PureMinimax.projectorOutput V.projector (by simpa using V.projector_rank)
    m hm hd a ha ha1

theorem measurable_output (m : ℕ) (hm : 0 < m) (hd : Fintype.card ι = m + 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) : Measurable (output m hm hd a ha ha1) := by
  have hp (i j : ι) : Measurable (fun V : Frame ι (Fin 1) => V.projector.matrix i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp Frame.measurable_projector_matrix)
  have hmatrix : Measurable (fun V : Frame ι (Fin 1) =>
      ((output m hm hd a ha ha1 V).matrix : ι → ι → ℂ)) := by
    apply measurable_pi_iff.2
    intro i
    apply measurable_pi_iff.2
    intro j
    change Measurable (fun V : Frame ι (Fin 1) =>
      (((1 - a : ℝ) : ℂ)) * V.projector.matrix i j +
        (((a / m : ℝ) : ℂ)) * ((1 : Matrix ι ι ℂ) i j - V.projector.matrix i j))
    exact ((hp i j).const_mul _).add ((measurable_const.sub (hp i j)).const_mul _)
  intro S hS
  rcases hS with ⟨T, hT, rfl⟩
  exact hmatrix hT

/-- A genuine `n`-copy collective learner with unrestricted density output. -/
def learner [Nonempty ι] (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) {n : ℕ} (P : SymmetricSupport.SymmetricProjectorInput ι n)
    (m : ℕ) (hm : 0 < m) (hd : Fintype.card ι = m + 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) : Learner ι (Frame ι (Fin 1)) n where
  measurement := measurement μ H P
  estimator := ⟨output m hm hd a ha ha1, measurable_output m hm hd a ha ha1⟩

/-- A bounded nonnegative error with mean at most `z/3` succeeds with
probability at least `2/3`; no Markov conclusion is an input. -/
theorem two_thirds_of_mean {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (t : Ω → ℝ) (ht : Measurable t)
    (ht0 : ∀ x, 0 ≤ t x) (ht1 : ∀ x, t x ≤ 1) {z : ℝ} (hz : 0 < z)
    (hmean : (∫ x, t x ∂ν) ≤ z / 3) :
    (2 : ℝ≥0∞) / 3 ≤ ν {x | t x ≤ z} := by
  have hi : Integrable t ν := Integrable.of_bound ht.aestronglyMeasurable 1
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (ht0 x)]; exact ht1 x)
  have hdiv : Integrable (fun x => t x / z) ν := hi.div_const z
  have hm : ν {x | z < t x} ≤ ENNReal.ofReal (1 / 3 : ℝ) := by
    have h := hdiv.measure_le_integral (ae_of_all _ fun x => div_nonneg (ht0 x) hz.le)
      (s := {x | z < t x}) (by intro x hx; exact (le_div_iff₀ hz).2 (by simpa using le_of_lt hx))
    apply h.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [integral_div]
    exact (div_le_iff₀ hz).2 (by linarith)
  have hs : MeasurableSet {x | z < t x} := measurableSet_lt measurable_const ht
  have hcomp : {x | t x ≤ z} = {x | z < t x}ᶜ := by ext x; simp
  rw [hcomp, measure_compl hs (measure_ne_top ν _), measure_univ]
  have hthird : ENNReal.ofReal (1 / 3 : ℝ) = (1 : ℝ≥0∞) / 3 := by
    norm_num only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3),
      ENNReal.ofReal_ofNat, ENNReal.ofReal_one]
  rw [hthird] at hm
  have h := tsub_le_tsub_left hm (1 : ℝ≥0∞)
  have hval : (1 : ℝ≥0∞) - 1 / 3 = 2 / 3 :=
    ENNReal.sub_eq_of_eq_add' (by norm_num) (by rw [ENNReal.div_add_div_same]; norm_num [ENNReal.div_self])
  rwa [hval] at h

/-- Mean complementary overlap and native Markov yield the actual good
outcome event, retaining zero probability and singular-output semantics. -/
theorem tail_success [Nonempty ι] (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) {n : ℕ} (P : SymmetricSupport.SymmetricProjectorInput ι n)
    (Q : SymmetricSupport.SymmetricProjectorInput ι (n + 1))
    (m : ℕ) (hd : Fintype.card ι = m + 1) (U : Frame ι (Fin 1))
    {z : ℝ} (hz : 0 < z) (hmean : (m : ℝ) / ((n : ℝ) + m + 1) ≤ z / 3) :
    (2 : ℝ≥0∞) / 3 ≤
      (measurement μ H P).outcomeMeasure (TensorCopies.density U.density n)
        {V | 1 - overlap U V ≤ z} := by
  apply two_thirds_of_mean _ _ (measurable_const.sub (measurable_overlap U))
    (fun V => sub_nonneg.mpr (overlap_mem_unit U V).2)
    (fun V => by linarith [(overlap_mem_unit U V).1]) hz
  rw [expected_tail μ H P Q U, hd]
  push_cast
  convert hmean using 1
  ring

/-- Section 4's Bures learner: `48*m^(3/2)/ε` actual copies suffice
uniformly on the entire actual rank-at-most-one state family. -/
theorem bures_learns [Nonempty ι] (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) {n : ℕ} (P : SymmetricSupport.SymmetricProjectorInput ι n)
    (Q : SymmetricSupport.SymmetricProjectorInput ι (n + 1))
    (m : ℕ) (hm : 0 < m) (hd : Fintype.card ι = m + 1)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hcopies : 48 * (m : ℝ) * Real.sqrt (m : ℝ) / ε ≤ (n : ℝ)) :
    (learner μ H P m hm hd (ε / 16) (by positivity) (by linarith)).BuresSuccess 1
      (ENNReal.ofReal ε) := by
  let A := learner μ H P m hm hd (ε / 16) (by positivity) (by linarith)
  intro ρ hρ
  obtain ⟨U, rfl⟩ := (PureMinimax.rankAtMost_one_iff_frame ρ).1 hρ
  refine ⟨A.successSet_measurable chiB U.density
    (JordanLossMeasurability.measurable_chiB_comp (fun _ : Density ι => U.density) id
      measurable_const measurable_id) _, ?_⟩
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hmr
  have hden : (0 : ℝ) < (n : ℝ) + m + 1 := by positivity
  have hmean : (m : ℝ) / ((n : ℝ) + m + 1) ≤ ((ε / 16) / Real.sqrt (m : ℝ)) / 3 := by
    apply (div_le_iff₀ hden).2
    have hnc := (div_le_iff₀ hε).1 hcopies
    have heq : ε / 16 / Real.sqrt (m : ℝ) / 3 * ((n : ℝ) + m + 1) =
        ε * ((n : ℝ) + m + 1) / (Real.sqrt (m : ℝ) * 48) := by ring
    rw [heq]
    apply (le_div_iff₀ (by positivity : 0 < Real.sqrt (m : ℝ) * 48)).2
    nlinarith [mul_nonneg (by positivity : 0 ≤ ε) (by positivity : 0 ≤ (m : ℝ) + 1)]
  have htail := tail_success μ H P Q m hd U (by positivity) hmean
  apply htail.trans (measure_mono ?_)
  intro V hV
  have ht : PureMinimax.tailMass U.density V.projector ≤ (ε / 16) / Real.sqrt (m : ℝ) := by
    have he : V.projector.matrix = V.density.matrix := by
      simp only [Frame.density_matrix, Fintype.card_fin, Nat.cast_one, inv_one, one_smul,
        Frame.projector_matrix]
    simpa only [PureMinimax.tailMass, he, overlap] using hV
  exact (PureMinimax.bures_epsilon U.density (by simpa using U.density_rank) V.projector
    (by simpa using V.projector_rank) m hm hd ε hε hε1 ht).le

/-- Section 4's right-inverse learner: `24*m²/ε²` actual copies suffice. -/
theorem right_learns [Nonempty ι] (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) {n : ℕ} (P : SymmetricSupport.SymmetricProjectorInput ι n)
    (Q : SymmetricSupport.SymmetricProjectorInput ι (n + 1))
    (m : ℕ) (hm : 0 < m) (hd : Fintype.card ι = m + 1)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hcopies : 24 * (m : ℝ) ^ 2 / ε ^ 2 ≤ (n : ℝ)) :
    (learner μ H P m hm hd (ε / 4) (by positivity) (by linarith)).RightSuccess 1
      (ENNReal.ofReal ε) := by
  let A := learner μ H P m hm hd (ε / 4) (by positivity) (by linarith)
  intro ρ hρ
  obtain ⟨U, rfl⟩ := (PureMinimax.rankAtMost_one_iff_frame ρ).1 hρ
  refine ⟨A.successSet_measurable chiR U.density
    (LossMeasurability.measurable_chiR_comp (fun _ : Density ι => U.density) id
      measurable_const measurable_id) _, ?_⟩
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hden : (0 : ℝ) < (n : ℝ) + m + 1 := by positivity
  have hmean : (m : ℝ) / ((n : ℝ) + m + 1) ≤ (ε ^ 2 / (8 * (m : ℝ))) / 3 := by
    apply (div_le_iff₀ hden).2
    have hnc := (div_le_iff₀ (sq_pos_of_pos hε)).1 hcopies
    have heq : ε ^ 2 / (8 * (m : ℝ)) / 3 * ((n : ℝ) + m + 1) =
        ε ^ 2 * ((n : ℝ) + m + 1) / (24 * (m : ℝ)) := by ring
    rw [heq]
    apply (le_div_iff₀ (by positivity : 0 < 24 * (m : ℝ))).2
    nlinarith [mul_nonneg (sq_nonneg ε) (by positivity : 0 ≤ (m : ℝ) + 1)]
  have htail := tail_success μ H P Q m hd U (by positivity) hmean
  apply htail.trans (measure_mono ?_)
  intro V hV
  have ht : PureMinimax.tailMass U.density V.projector ≤ ε ^ 2 / (8 * (m : ℝ)) := by
    have he : V.projector.matrix = V.density.matrix := by
      simp only [Frame.density_matrix, Fintype.card_fin, Nat.cast_one, inv_one, one_smul,
        Frame.projector_matrix]
    simpa only [PureMinimax.tailMass, he, overlap] using hV
  exact PureMinimax.right_epsilon U.density (by simpa using U.density_rank) V.projector
    (by simpa using V.projector_rank) m hm hd ε hε hε1 ht

end Paper26.PureUpperBounds
