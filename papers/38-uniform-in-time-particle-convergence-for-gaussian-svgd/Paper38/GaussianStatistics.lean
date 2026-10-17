import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Gaussian initial sample statistics

The random sample below lives on the actual finite product of standard real
Gaussian measures. Each pair `(i,j)` denotes coordinate `j` of sample `i`.
Thus the sample vectors are independent standard d-dimensional Gaussians.
The expectation is the Bochner integral for this product probability measure.
-/
noncomputable section

namespace Paper38.GaussianStatistics

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

section GenericProduct

variable {I : Type*} [Fintype I]

lemma gaussianProduct_coordinate_measurePreserving (a : I) :
    MeasurePreserving (fun ω : I → ℝ => ω a)
      (Measure.pi (fun _ : I => gaussianReal 0 1)) (gaussianReal 0 1) :=
  measurePreserving_eval (fun _ => gaussianReal 0 1) a

lemma gaussianProduct_coordinate_memLp (a : I) :
    MemLp (fun ω : I → ℝ => ω a) 2
      (Measure.pi (fun _ : I => gaussianReal 0 1)) :=
  (memLp_id_gaussianReal 2).comp_measurePreserving
    (gaussianProduct_coordinate_measurePreserving a)

lemma gaussianProduct_coordinate_integral (a : I) :
    ∫ ω : I → ℝ, ω a ∂Measure.pi (fun _ : I => gaussianReal 0 1) = 0 := by
  calc
    _ = ∫ x : ℝ, x ∂(Measure.pi (fun _ : I => gaussianReal 0 1)).map (fun ω => ω a) :=
      (integral_map (φ := fun ω : I → ℝ => ω a) (f := fun x : ℝ => x)
        (measurable_pi_apply a).aemeasurable measurable_id.aestronglyMeasurable).symm
    _ = 0 := by rw [(gaussianProduct_coordinate_measurePreserving a).map_eq]; simp

lemma gaussianProduct_coordinate_variance (a : I) :
    variance (fun ω : I → ℝ => ω a)
      (Measure.pi (fun _ : I => gaussianReal 0 1)) = 1 := by
  rw [← variance_id_map (measurable_pi_apply a).aemeasurable,
    (gaussianProduct_coordinate_measurePreserving a).map_eq]
  simp

/-- The identity covariance of an actual standard product Gaussian measure. -/
lemma gaussianProduct_coordinate_mul_integral [DecidableEq I] (a b : I) :
    ∫ ω : I → ℝ, ω a * ω b ∂Measure.pi (fun _ : I => gaussianReal 0 1) =
      if a = b then 1 else 0 := by
  by_cases hab : a = b
  · subst b
    simp only [ite_true]
    have hv := gaussianProduct_coordinate_variance a
    rw [variance_eq_integral (gaussianProduct_coordinate_memLp a).aemeasurable,
      gaussianProduct_coordinate_integral] at hv
    simpa only [sub_zero, pow_two] using hv
  · rw [if_neg hab]
    have hi : iIndepFun (fun i : I => fun ω : I → ℝ => ω i)
        (Measure.pi (fun _ : I => gaussianReal 0 1)) :=
      iIndepFun_pi (X := fun _ => id) (fun _ => measurable_id.aemeasurable)
    calc
      _ = (∫ ω : I → ℝ, ω a ∂Measure.pi (fun _ : I => gaussianReal 0 1)) *
          (∫ ω : I → ℝ, ω b ∂Measure.pi (fun _ : I => gaussianReal 0 1)) :=
        (hi.indepFun hab).integral_mul_eq_mul_integral
          (measurable_pi_apply a).aestronglyMeasurable
          (measurable_pi_apply b).aestronglyMeasurable
      _ = 0 := by rw [gaussianProduct_coordinate_integral, zero_mul]

end GenericProduct

/-- The genuine standard product Gaussian has a Lebesgue density in every
finite dimension. The proof is by Fubini/product absolute continuity. -/
theorem gaussianProduct_absolutelyContinuous (d : ℕ) :
    Measure.pi (fun _ : Fin d => gaussianReal 0 1) ≪ (volume : Measure (Fin d → ℝ)) := by
  induction d with
  | zero =>
    rw [Measure.pi_of_empty (fun _ : Fin 0 => gaussianReal 0 1) (fun _ => 0),
      Measure.volume_pi_eq_dirac (fun _ : Fin 0 => (0 : ℝ))]
  | succ d ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
    have h := (gaussianReal_absolutelyContinuous 0 (v := 1) one_ne_zero).prod ih
    have hm := h.map e.symm.measurable
    have hg := measurePreserving_piFinSuccAbove
      (fun _ : Fin (d + 1) => gaussianReal 0 1) 0
    have hv := volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
    have hv' : MeasurePreserving e.symm
        ((volume : Measure ℝ).prod (volume : Measure (Fin d → ℝ)))
        (volume : Measure (Fin (d + 1) → ℝ)) := hv.symm
    rw [hg.symm.map_eq, hv'.map_eq] at hm
    exact hm

/-- Absolute continuity is preserved on the canonical Euclidean-space copy. -/
theorem gaussianEuclidean_absolutelyContinuous (d : ℕ) :
    (Measure.pi (fun _ : Fin d => gaussianReal 0 1)).map
      (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) ≪ volume := by
  have h := (gaussianProduct_absolutelyContinuous d).map
    (show Measurable (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) from
      (EuclideanSpace.measurableEquiv (Fin d)).symm.measurable)
  rwa [(PiLp.volume_preserving_toLp (Fin d)).map_eq] at h

/-- The canonical probability space for N independent standard Gaussians in R^d. -/
noncomputable def gaussianSampleLaw (N d : ℕ) : Measure (Fin N × Fin d → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance gaussianSampleLaw_probability (N d : ℕ) :
    IsProbabilityMeasure (gaussianSampleLaw N d) := by
  unfold gaussianSampleLaw
  infer_instance

/-- The j-th coordinate of the empirical mean (6.7). -/
def sampleMeanCoord {N d : ℕ} (j : Fin d) (ω : Fin N × Fin d → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i : Fin N, ω (i, j)

/-- The empirical mean as a vector with the Euclidean norm. -/
def sampleMean {N d : ℕ} (ω : Fin N × Fin d → ℝ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j => sampleMeanCoord j ω)

lemma coordinate_measurePreserving (N d : ℕ) (a : Fin N × Fin d) :
    MeasurePreserving (fun ω : Fin N × Fin d → ℝ => ω a)
      (gaussianSampleLaw N d) (gaussianReal 0 1) :=
  measurePreserving_eval (fun _ => gaussianReal 0 1) a

lemma coordinate_memLp (N d : ℕ) (a : Fin N × Fin d) :
    MemLp (fun ω : Fin N × Fin d → ℝ => ω a) 2 (gaussianSampleLaw N d) := by
  exact (memLp_id_gaussianReal 2).comp_measurePreserving (coordinate_measurePreserving N d a)

lemma coordinate_integral (N d : ℕ) (a : Fin N × Fin d) :
    ∫ ω, ω a ∂gaussianSampleLaw N d = 0 := by
  calc ∫ ω, ω a ∂gaussianSampleLaw N d
      = ∫ x : ℝ, x ∂(gaussianSampleLaw N d).map (fun ω => ω a) := by
        exact (integral_map (μ := gaussianSampleLaw N d)
          (φ := fun ω => ω a) (f := fun x : ℝ => x)
          (measurable_pi_apply a).aemeasurable measurable_id.aestronglyMeasurable).symm
    _ = 0 := by rw [(coordinate_measurePreserving N d a).map_eq]; simp

lemma coordinate_variance (N d : ℕ) (a : Fin N × Fin d) :
    variance (fun ω : Fin N × Fin d → ℝ => ω a) (gaussianSampleLaw N d) = 1 := by
  rw [← variance_id_map (measurable_pi_apply a).aemeasurable,
    (coordinate_measurePreserving N d a).map_eq]
  simp

lemma coordinates_iIndepFun (N d : ℕ) :
    iIndepFun (fun a : Fin N × Fin d => fun ω : Fin N × Fin d → ℝ => ω a)
      (gaussianSampleLaw N d) := by
  exact iIndepFun_pi (X := fun _ => id) (fun _ => measurable_id.aemeasurable)

lemma sampleMeanCoord_memLp {N d : ℕ} (j : Fin d) :
    MemLp (sampleMeanCoord (N := N) j) 2 (gaussianSampleLaw N d) := by
  unfold sampleMeanCoord
  exact (memLp_finset_sum _ (fun i _ => coordinate_memLp N d (i, j))).const_mul _

lemma sampleMeanCoord_integral {N d : ℕ} (j : Fin d) :
    ∫ ω, sampleMeanCoord (N := N) j ω ∂gaussianSampleLaw N d = 0 := by
  unfold sampleMeanCoord
  rw [integral_const_mul, integral_finset_sum]
  · simp [coordinate_integral]
  · exact fun i _ => (coordinate_memLp N d (i, j)).integrable (by norm_num)

lemma sampleMeanCoord_variance {N d : ℕ} (hN : N ≠ 0) (j : Fin d) :
    variance (sampleMeanCoord (N := N) j) (gaussianSampleLaw N d) = (N : ℝ)⁻¹ := by
  unfold sampleMeanCoord
  rw [variance_mul]
  have hvar : variance (fun ω : Fin N × Fin d → ℝ => ∑ i : Fin N, ω (i, j))
      (gaussianSampleLaw N d) = (N : ℝ) := by
    have hv := IndepFun.variance_sum (s := Finset.univ)
      (X := fun i : Fin N => fun ω : Fin N × Fin d → ℝ => ω (i, j))
      (fun i _ => coordinate_memLp N d (i, j))
      (fun i _ k _ hik => (coordinates_iIndepFun N d).indepFun (by
        intro h
        exact hik (Prod.mk.inj h).1))
    simpa only [Finset.sum_fn, coordinate_variance, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] using hv
  rw [hvar]
  field_simp

/-- Each coordinate of the standard Gaussian sample mean has second moment 1/N. -/
theorem sampleMeanCoord_secondMoment {N d : ℕ} (hN : N ≠ 0) (j : Fin d) :
    ∫ ω, sampleMeanCoord (N := N) j ω ^ 2 ∂gaussianSampleLaw N d = (N : ℝ)⁻¹ := by
  have hv := sampleMeanCoord_variance hN j
  rw [variance_eq_integral (sampleMeanCoord_memLp j).aemeasurable,
    sampleMeanCoord_integral] at hv
  simpa using hv

/-- The first exact Gaussian moment identity in equation (6.11): E|mean|²=d/N. -/
theorem sampleMean_secondMoment {N d : ℕ} (hN : N ≠ 0) :
    ∫ ω, ‖sampleMean (N := N) (d := d) ω‖ ^ 2 ∂gaussianSampleLaw N d =
      (d : ℝ) / N := by
  simp only [EuclideanSpace.norm_sq_eq, sampleMean, PiLp.toLp_apply,
    Real.norm_eq_abs, sq_abs]
  rw [integral_finset_sum]
  · simp only [sampleMeanCoord_secondMoment hN, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_eq_mul_inv]
  · intro j _
    exact (sampleMeanCoord_memLp j).integrable_sq

/-- The standard normal has the exact centered sub-Gaussian MGF. -/
lemma standardGaussian_subGaussian :
    HasSubgaussianMGF (fun x : ℝ => x) 1 (gaussianReal 0 1) where
  integrable_exp_mul := integrable_exp_mul_gaussianReal
  mgf_le t := by simp [mgf_fun_id_gaussianReal]

lemma coordinate_subGaussian (N d : ℕ) (a : Fin N × Fin d) :
    HasSubgaussianMGF (fun ω : Fin N × Fin d → ℝ => ω a) 1
      (gaussianSampleLaw N d) := by
  change HasSubgaussianMGF ((fun x : ℝ => x) ∘ (fun ω => ω a)) 1 (gaussianSampleLaw N d)
  apply HasSubgaussianMGF.of_map (measurable_pi_apply a).aemeasurable
  rw [(coordinate_measurePreserving N d a).map_eq]
  exact standardGaussian_subGaussian

lemma coordinate_sum_subGaussian {N d : ℕ} (j : Fin d) :
    HasSubgaussianMGF (fun ω : Fin N × Fin d → ℝ => ∑ i : Fin N, ω (i, j))
      (N : ℝ≥0) (gaussianSampleLaw N d) := by
  have hi := (coordinates_iIndepFun N d).precomp
    (g := fun i : Fin N => (i, j)) (fun i k h => (Prod.mk.inj h).1)
  have hs := HasSubgaussianMGF.sum_of_iIndepFun (s := Finset.univ)
    (c := fun _ => (1 : ℝ≥0)) hi (fun i _ => coordinate_subGaussian N d (i, j))
  simpa using hs

/-- The mean part of the exponential good-event estimate (Lemma 7.1),
for any coordinate and any nonnegative threshold. -/
theorem sampleMeanCoord_abs_tail {N d : ℕ} (hN : 0 < N) (j : Fin d)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (gaussianSampleLaw N d).real {ω | ε ≤ |sampleMeanCoord (N := N) j ω|} ≤
      2 * Real.exp (-(N : ℝ) * ε ^ 2 / 2) := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hNzero : (N : ℝ) ≠ 0 := ne_of_gt hNreal
  have hthreshold : 0 ≤ (N : ℝ) * ε := mul_nonneg hNreal.le hε
  have hp := (coordinate_sum_subGaussian (N := N) j).measure_ge_le hthreshold
  have hm := (coordinate_sum_subGaussian (N := N) j).neg.measure_ge_le hthreshold
  have hexp : -((N : ℝ) * ε) ^ 2 / (2 * (N : ℝ)) = -(N : ℝ) * ε ^ 2 / 2 := by
    field_simp
  simp only [NNReal.coe_natCast, hexp] at hp hm
  have hsubset : {ω | ε ≤ |sampleMeanCoord (N := N) j ω|} ⊆
      {ω : Fin N × Fin d → ℝ | (N : ℝ) * ε ≤ ∑ i, ω (i, j)} ∪
      {ω : Fin N × Fin d → ℝ | (N : ℝ) * ε ≤ -(∑ i, ω (i, j))} := by
    intro ω hω
    change ε ≤ |sampleMeanCoord (N := N) j ω| at hω
    rcases le_abs.mp hω with h | h
    · left
      have hh := mul_le_mul_of_nonneg_left h hNreal.le
      simpa [sampleMeanCoord, ← mul_assoc, hNzero] using hh
    · right
      have hh := mul_le_mul_of_nonneg_left h hNreal.le
      simpa [sampleMeanCoord, ← mul_assoc, hNzero] using hh
  calc
    _ ≤ (gaussianSampleLaw N d).real
        ({ω : Fin N × Fin d → ℝ | (N : ℝ) * ε ≤ ∑ i, ω (i, j)} ∪
          {ω : Fin N × Fin d → ℝ | (N : ℝ) * ε ≤ -(∑ i, ω (i, j))}) :=
      measureReal_mono hsubset
    _ ≤ _ := (measureReal_union_le _ _).trans (by
      simpa only [Pi.neg_apply, two_mul] using add_le_add hp hm)

end Paper38.GaussianStatistics
