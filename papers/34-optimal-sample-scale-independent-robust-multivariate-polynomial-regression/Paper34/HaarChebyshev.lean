import Paper34.AngularMeasure
import Paper34.CosineFourierLift
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The Haar-to-Chebyshev measure bridge

The normalized circle Haar law pushed through cosine is the positive-angular
Chebyshev law. The proof splits a symmetric fundamental interval into two
halves and uses the measure-preserving reflection. Finite-product measure
identities then give the exact source `L¹` norm for every actual cosine lift.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace Paper34.HaarChebyshev

open Kernel TensorNorming

noncomputable section

/-- Cosine on the exact `Kernel.Torus` type (the angle synonym has no measure instance). -/
def circleCos (u : Torus) : ℝ := Real.Angle.cos u

lemma continuous_circleCos : Continuous circleCos := Real.Angle.continuous_cos

@[simp] lemma circleCos_coe (t : ℝ) : circleCos (t : Torus) = Real.cos t := rfl

abbrev positiveAngularLaw : Measure ℝ :=
  (ENNReal.ofReal Real.pi)⁻¹ • volume.restrict (Icc 0 Real.pi)

instance positiveAngular_isProbabilityMeasure : IsProbabilityMeasure positiveAngularLaw where
  measure_univ := by
    simp only [positiveAngularLaw, Measure.smul_apply, Measure.restrict_apply_univ,
      Real.volume_Icc, sub_zero, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by positivity) (by simp)

lemma reflect_positive_interval :
    Measure.map (fun t : ℝ => -t) (volume.restrict (Icc 0 Real.pi)) =
      volume.restrict (Icc (-Real.pi) 0) := by
  have hpre : (fun t : ℝ => -t) ⁻¹' Icc (-Real.pi) 0 = Icc 0 Real.pi := by
    ext t
    simp only [mem_preimage, mem_Icc]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [← hpre, ← measurableEmbedding_neg.restrict_map,
    Measure.map_neg_eq_self]

lemma map_cos_negative_interval :
    Measure.map Real.cos (volume.restrict (Icc (-Real.pi) 0)) =
      Measure.map Real.cos (volume.restrict (Icc 0 Real.pi)) := by
  rw [← reflect_positive_interval,
    Measure.map_map Real.continuous_cos.measurable measurable_neg]
  congr 1
  funext t
  exact Real.cos_neg t

lemma symmetric_interval_split :
    volume.restrict (Icc (-Real.pi) Real.pi) =
      volume.restrict (Icc (-Real.pi) 0) + volume.restrict (Icc 0 Real.pi) := by
  have hd : Disjoint (Ioc (-Real.pi) (0 : ℝ)) (Ioc 0 Real.pi) := by
    apply Set.disjoint_left.mpr
    intro t ht hu
    exact (not_lt_of_ge ht.2) hu.1
  have h := Measure.restrict_union (μ := (volume : Measure ℝ)) hd measurableSet_Ioc
  rw [Ioc_union_Ioc_eq_Ioc (by linarith [Real.pi_pos] : -Real.pi ≤ 0) Real.pi_pos.le] at h
  simpa only [restrict_Ioc_eq_restrict_Icc] using h

lemma map_cos_symmetric_interval :
    Measure.map Real.cos (volume.restrict (Icc (-Real.pi) Real.pi)) =
      ENNReal.ofReal (2 : ℝ) • Measure.map Real.cos (volume.restrict (Icc 0 Real.pi)) := by
  rw [symmetric_interval_split, Measure.map_add _ _ Real.continuous_cos.measurable,
    map_cos_negative_interval]
  norm_num [two_smul]

/-- Actual normalized Haar cosine pushforward in one dimension. -/
theorem map_angleCos_haar :
    Measure.map circleCos haar = Measure.map Real.cos positiveAngularLaw := by
  have hquot := (AddCircle.measurePreserving_mk (2 * Real.pi) (-Real.pi)).map_eq
  have hend : -Real.pi + 2 * Real.pi = Real.pi := by ring
  rw [hend, restrict_Ioc_eq_restrict_Icc, AddCircle.volume_eq_smul_haarAddCircle] at hquot
  have h := congrArg (Measure.map circleCos) hquot
  rw [Measure.map_map continuous_circleCos.measurable AddCircle.measurable_mk',
    Measure.map_smul] at h
  change Measure.map Real.cos (volume.restrict (Icc (-Real.pi) Real.pi)) =
    ENNReal.ofReal (2 * Real.pi) • Measure.map circleCos haar at h
  have hnorm := congrArg (fun mu : Measure ℝ => (ENNReal.ofReal (2 * Real.pi))⁻¹ • mu) h
  dsimp only at hnorm
  rw [smul_smul, ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top, one_smul] at hnorm
  have hscalar : (ENNReal.ofReal (2 * Real.pi))⁻¹ * ENNReal.ofReal (2 : ℝ) =
      (ENNReal.ofReal Real.pi)⁻¹ := by
    rw [← ENNReal.ofReal_inv_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (2 * Real.pi)⁻¹),
      ← ENNReal.ofReal_inv_of_pos Real.pi_pos]
    congr 1
    field_simp
  calc
    Measure.map circleCos haar =
        (ENNReal.ofReal (2 * Real.pi))⁻¹ •
          Measure.map Real.cos (volume.restrict (Icc (-Real.pi) Real.pi)) := hnorm.symm
    _ = (ENNReal.ofReal Real.pi)⁻¹ •
          Measure.map Real.cos (volume.restrict (Icc 0 Real.pi)) := by
      rw [map_cos_symmetric_interval, smul_smul, hscalar]
    _ = Measure.map Real.cos positiveAngularLaw := by
      rw [positiveAngularLaw, Measure.map_smul]

/-- The actual source angular law is the finite product of positive-angular laws. -/
theorem angularLaw_eq_pi (n : ℕ) :
    angularLaw n = Measure.pi (fun _ : Fin n => positiveAngularLaw) := by
  apply Eq.symm
  apply Measure.pi_eq
  intro s hs
  have hbox : Icc (fun _ : Fin n => (0 : ℝ)) (fun _ => Real.pi) =
      Set.pi Set.univ (fun _ : Fin n => Icc (0 : ℝ) Real.pi) :=
    (Set.pi_univ_Icc _ _).symm
  rw [angularLaw, Measure.smul_apply,
    Measure.restrict_apply (MeasurableSet.univ_pi hs), hbox,
    ← Set.pi_inter_distrib, volume_pi_pi]
  simp only [positiveAngularLaw, Measure.smul_apply,
    Measure.restrict_apply (hs _), smul_eq_mul]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow Real.pi_pos.le, ENNReal.inv_pow]

/-- The actual continuous product cosine map on the product torus. -/
def torusCos (n : ℕ) (u : TorusN n) : Point n := fun k => circleCos (u k)

lemma continuous_torusCos (n : ℕ) : Continuous (torusCos n) :=
  continuous_pi (fun k => continuous_circleCos.comp (continuous_apply k))

/-- The finite product of probability Haar measures pushes exactly to the
source product-Chebyshev law. -/
theorem map_torusCos_haarN (n : ℕ) :
    Measure.map (torusCos n) (haarN n) = chebyshevLaw n := by
  calc
    Measure.map (torusCos n) (haarN n) =
        Measure.pi (fun _ : Fin n => Measure.map circleCos haar) := by
      exact Measure.pi_map_pi (fun _ => continuous_circleCos.measurable.aemeasurable)
    _ = Measure.pi (fun _ : Fin n => Measure.map Real.cos positiveAngularLaw) := by
      simp_rw [map_angleCos_haar]
    _ = Measure.map (fun theta : Point n => fun k => Real.cos (theta k))
        (Measure.pi (fun _ : Fin n => positiveAngularLaw)) := by
      exact (Measure.pi_map_pi (fun _ => Real.continuous_cos.measurable.aemeasurable)).symm
    _ = chebyshevLaw n := by rw [← angularLaw_eq_pi]; rfl

/-- The Haar/Chebyshev integral bridge for every measurable scalar function. -/
theorem integral_torusCos_eq_chebyshev {n : ℕ} (f : Point n → ℝ) (hf : Measurable f) :
    (∫ u, f (torusCos n u) ∂haarN n) = ∫ x, f x ∂chebyshevLaw n := by
  rw [← map_torusCos_haarN]
  exact (integral_map_of_stronglyMeasurable (continuous_torusCos n).measurable
    hf.stronglyMeasurable).symm

lemma angularPoint_surjective (n : ℕ) : Function.Surjective (@angularPoint n) := by
  intro u
  have h : ∀ k : Fin n, ∃ t : ℝ, (t : Torus) = u k := fun k => Quotient.exists_rep (u k)
  choose theta htheta using h
  exact ⟨theta, funext htheta⟩

/-- Exact (3.2) for any actual finite Fourier polynomial representing the source
polynomial in angular coordinates. The representation identity is the only
connection required here; no norming estimate is assumed. -/
theorem haar_l1_eq_l1Norm {n d : ℕ} (q : PolynomialSpace n d) (H : TrigPolynomial n d)
    (hH : ∀ theta : Point n, H.eval (angularPoint theta) = (angularEval q theta : ℂ)) :
    (∫ u, ‖H.eval u‖ ∂haarN n) = l1Norm q := by
  have hp : ∀ u : TorusN n, ‖H.eval u‖ = |polyEval q (torusCos n u)| := by
    intro u
    obtain ⟨theta, rfl⟩ := angularPoint_surjective n u
    rw [hH]
    change ‖(angularEval q theta : ℂ)‖ = |angularEval q theta|
    simp only [Complex.norm_real, Real.norm_eq_abs]
  simp_rw [hp]
  exact integral_torusCos_eq_chebyshev _ (continuous_polyEval q).abs.measurable

/-- Exact Haar norm identity for the constructed source cosine/Fourier lift. -/
theorem toTrigPolynomial_haar_l1 {n d : ℕ} (q : PolynomialSpace n d) :
    (∫ u, ‖(CosineFourierLift.toTrigPolynomial q).eval u‖ ∂haarN n) = l1Norm q :=
  haar_l1_eq_l1Norm q _ (CosineFourierLift.toTrigPolynomial_angular q)

end

end Paper34.HaarChebyshev
