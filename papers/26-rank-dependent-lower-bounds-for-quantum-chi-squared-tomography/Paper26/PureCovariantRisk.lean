import Paper26.PureUpperBounds

/-! Exact achieved risk in Appendix A for the actual covariant experiment.
The arbitrary-measurement minimax lower bound is a separate posterior argument;
this module proves the attained value for every true pure input directly. -/
noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal
open MeasureTheory

namespace Paper26.PureCovariantRisk
open QuantumModel HaarFrames PureCovariant PureUpperBounds CollectiveModel
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def isotropicMass (n m : ℕ) : ℝ := (m : ℝ) / (Real.sqrt ((n : ℝ) + 1) + m)

theorem sqrt_copy_pos (n : ℕ) : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)

theorem isotropicMass_pos (n m : ℕ) (hm : 0 < m) : 0 < isotropicMass n m := by
  unfold isotropicMass
  exact div_pos (Nat.cast_pos.2 hm) (by positivity)

theorem isotropicMass_lt_one (n m : ℕ) : isotropicMass n m < 1 := by
  unfold isotropicMass
  rw [div_lt_one (by positivity : (0 : ℝ) < Real.sqrt ((n : ℝ) + 1) + m)]
  linarith [sqrt_copy_pos n]

/-- The real finite loss from the actual pure-state formula (39). -/
def scalarLoss (m : ℕ) (a t : ℝ) : ℝ := (1 - t) / (1 - a) + (m : ℝ) * t / a - 1

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
theorem scalarLoss_nonneg (m : ℕ) (hm : 0 < m) {a t : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (ht : 0 ≤ t) (ht1 : t ≤ 1) : 0 ≤ scalarLoss m a t := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h1 : 0 ≤ 1 / (1 - a) - 1 := by
    apply sub_nonneg.2
    rw [le_div_iff₀ (by linarith : 0 < 1 - a)]
    linarith
  have h2 : 0 ≤ (m : ℝ) / a - 1 := by
    apply sub_nonneg.2
    rw [le_div_iff₀ ha]
    linarith
  have he : scalarLoss m a t =
      (1 - t) * (1 / (1 - a) - 1) + t * ((m : ℝ) / a - 1) := by
    unfold scalarLoss
    ring
  rw [he]
  exact add_nonneg (mul_nonneg (by linarith) h1) (mul_nonneg ht h2)

/-- An affine expression of the overlap tail used for the actual expectation. -/
theorem scalarLoss_affine (m : ℕ) (a t : ℝ) :
    scalarLoss m a t = (1 / (1 - a) - 1) + ((m : ℝ) / a - 1 / (1 - a)) * t := by
  unfold scalarLoss
  ring

/-- Expected chi-squared risk is the extended-real expectation of the actual
support-aware loss, never an expectation of an unguarded totalized inverse. -/
def expectedRisk {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (A : Learner ι Ω n) (ρ : Density ι) : ℝ≥0∞ :=
  ∫⁻ y, chiR ρ (A.estimator.estimate y) ∂A.outcomeMeasure ρ

/-- For any interior regularization mass, the actual pure experiment's
expected loss is obtained by integrating the exact affine formula (39). -/
theorem expectedRisk_eq (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) {n : ℕ} (P : SymmetricSupport.SymmetricProjectorInput ι n)
    (Q : SymmetricSupport.SymmetricProjectorInput ι (n + 1))
    (m : ℕ) (hm : 0 < m) (hd : Fintype.card ι = m + 1)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (U : Frame ι (Fin 1)) :
    expectedRisk (learner μ H P m hm hd a ha.le ha1.le) U.density =
      ENNReal.ofReal ((1 / (1 - a) - 1) + ((m : ℝ) / a - 1 / (1 - a)) *
        ((m : ℝ) / ((n : ℝ) + m + 1))) := by
  let A := learner μ H P m hm hd a ha.le ha1.le
  let ν := A.outcomeMeasure U.density
  let t : Frame ι (Fin 1) → ℝ := fun V => 1 - overlap U V
  have ht0 (V : Frame ι (Fin 1)) : 0 ≤ t V := sub_nonneg.mpr (overlap_mem_unit U V).2
  have ht1 (V : Frame ι (Fin 1)) : t V ≤ 1 := by dsimp [t]; linarith [(overlap_mem_unit U V).1]
  have htm : Measurable t := measurable_const.sub (measurable_overlap U)
  have hti : Integrable t ν := Integrable.of_bound htm.aestronglyMeasurable 1
    (ae_of_all _ fun V => by rw [Real.norm_eq_abs, abs_of_nonneg (ht0 V)]; exact ht1 V)
  have hi : Integrable (fun V => scalarLoss m a (t V)) ν := by
    simp_rw [scalarLoss_affine]
    exact (integrable_const _).add (hti.const_mul _)
  have hf (V : Frame ι (Fin 1)) : chiR U.density (A.estimator.estimate V) =
      ENNReal.ofReal (scalarLoss m a (t V)) := by
    have he : V.projector.matrix = V.density.matrix := by
      simp only [Frame.density_matrix, Fintype.card_fin, Nat.cast_one, inv_one, one_smul,
        Frame.projector_matrix]
    have h := PureMinimax.equation_39 U.density (by simpa using U.density_rank)
      V.projector (by simpa using V.projector_rank) m hm hd a ha ha1
    simpa only [A, learner, output, scalarLoss, t, PureMinimax.tailMass, he, overlap] using h
  change (∫⁻ V, chiR U.density (A.estimator.estimate V) ∂ν) = _
  simp_rw [hf]
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ fun V => scalarLoss_nonneg m hm ha ha1 (ht0 V) (ht1 V))]
  congr 1
  simp_rw [scalarLoss_affine]
  rw [integral_add (integrable_const _) (hti.const_mul _), integral_const,
    measureReal_univ_eq_one, one_smul, integral_const_mul]
  have hmean : (∫ V, t V ∂ν) = (m : ℝ) / ((n : ℝ) + m + 1) := by
    change (∫ V, (1 - overlap U V) ∂(measurement μ H P).outcomeMeasure
      (TensorCopies.density U.density n)) = _
    rw [expected_tail μ H P Q U, hd]
    push_cast
    ring
  rw [hmean]

/-- The exact value in Equation (50) is achieved on each actual pure input,
including `n=0`; covariance or a Bayes-to-minimax interchange is unnecessary
for this pointwise risk calculation. -/
theorem achieved_risk (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) {n : ℕ} (P : SymmetricSupport.SymmetricProjectorInput ι n)
    (Q : SymmetricSupport.SymmetricProjectorInput ι (n + 1))
    (m : ℕ) (hm : 0 < m) (hd : Fintype.card ι = m + 1) (U : Frame ι (Fin 1)) :
    expectedRisk (learner μ H P m hm hd (isotropicMass n m)
      (isotropicMass_pos n m hm).le (isotropicMass_lt_one n m).le) U.density =
      ENNReal.ofReal (((Real.sqrt ((n : ℝ) + 1) + m) ^ 2 /
        ((n : ℝ) + Fintype.card ι)) - 1) := by
  rw [expectedRisk_eq μ H P Q m hm hd _ (isotropicMass_pos n m hm) (isotropicMass_lt_one n m) U]
  congr 1
  have hs : 0 < Real.sqrt ((n : ℝ) + 1) := sqrt_copy_pos n
  have hmR : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hroot := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)
  rw [hd]
  push_cast
  unfold isotropicMass
  have hsd : Real.sqrt ((n : ℝ) + 1) + m ≠ 0 := by positivity
  have hden : (n : ℝ) + m + 1 ≠ 0 := by positivity
  generalize hq : Real.sqrt ((n : ℝ) + 1) = q at *
  have hn : (n : ℝ) = q ^ 2 - 1 := by linarith
  rw [hn]
  ring_nf
  field_simp [hs.ne', hmR.ne', hsd, show q ^ 2 + (m : ℝ) ≠ 0 by positivity]
  ring

/-- Uniform risk on the entire rank-at-most-one density family follows
from the actual pure-state classification, rather than a chosen subfamily. -/
theorem achieved_risk_all_pure (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) {n : ℕ} (P : SymmetricSupport.SymmetricProjectorInput ι n)
    (Q : SymmetricSupport.SymmetricProjectorInput ι (n + 1))
    (m : ℕ) (hm : 0 < m) (hd : Fintype.card ι = m + 1)
    (ρ : Density ι) (hρ : ρ.matrix.rank ≤ 1) :
    expectedRisk (learner μ H P m hm hd (isotropicMass n m)
      (isotropicMass_pos n m hm).le (isotropicMass_lt_one n m).le) ρ =
      ENNReal.ofReal (((Real.sqrt ((n : ℝ) + 1) + m) ^ 2 /
        ((n : ℝ) + Fintype.card ι)) - 1) := by
  obtain ⟨U, rfl⟩ := (PureMinimax.rankAtMost_one_iff_frame ρ).1 hρ
  exact achieved_risk μ H P Q m hm hd U

end Paper26.PureCovariantRisk
