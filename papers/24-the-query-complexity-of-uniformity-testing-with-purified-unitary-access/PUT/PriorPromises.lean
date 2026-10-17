import PUT.FourierModel
import PUT.DirichletLemma
import PUT.ParameterLowerBound

/-!
# The actual Dirichlet hard-event probability at the testing scale

The radial Lemma 2 event is lifted to the full radial-phase probability
space.  Its threshold is exactly `2ε` at the selected scale, so correctness
on the source's strict alternative promise applies on that event.
-/
noncomputable section
namespace PUT.PriorPromises
open MeasureTheory FourierModel
open scoped ENNReal

/-- The parameter substitution in Section 4 gives an exact TV threshold. -/
theorem threshold_at_scale {ε : ℝ} (hε : 0 < ε) :
    lemma2Threshold (dirichletScale ε) = 2 * ε := by
  have hs : Real.sqrt (dirichletScale ε) = 1 / (48 * ε) := by
    unfold dirichletScale
    rw [zpow_neg, zpow_ofNat, Real.sqrt_inv, Real.sqrt_sq (by positivity)]
    simp only [one_div]
  unfold lemma2Threshold
  rw [hs]
  field_simp
  ring

/-- Taking the product with the normalized phase prior preserves every
measurable radial-event probability. -/
theorem radial_event_probability {d M : ℕ} {a : ℝ}
    (s : Set (Fin d → ℝ)) :
    (alternativeMeasure d M a).real {x | x.1 ∈ s} = (dirichletMeasure d a).real s := by
  have he : {x : (Fin d → ℝ) × Torus d M | x.1 ∈ s} = s ×ˢ Set.univ := by
    ext x
    simp
  rw [he]
  unfold alternativeMeasure Measure.real
  rw [Measure.prod_prod]
  simp

/-- Actual mass `q₀` of the TV-good event on the full continuous prior. -/
theorem good_event_mass (hMom : External.DirichletJointMomentLaw)
    {d M : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ 1 / 48) :
    q0 ≤ (alternativeMeasure d M (dirichletScale ε)).real
      {x | 2 * ε ≤ tvDist x.1 (uniform d)} := by
  have he := radial_event_probability (d := d) (M := M) (a := dirichletScale ε)
    {p : Fin d → ℝ | 2 * ε ≤ tvDist p (uniform d)}
  change (alternativeMeasure d M (dirichletScale ε)).real
    {x | 2 * ε ≤ tvDist x.1 (uniform d)} = _ at he
  rw [he]
  have h := lemma2_from_joint_moments hMom d (dirichletScale ε) hd
    (ParameterLowerBound.dirichletScale_ge_one hε hsmall)
  rw [threshold_at_scale hε] at h
  exact h

end PUT.PriorPromises
