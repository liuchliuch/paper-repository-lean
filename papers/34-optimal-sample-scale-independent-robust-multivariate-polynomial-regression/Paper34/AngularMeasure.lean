import Paper34.CellMass
import Paper34.CellOscillation

/-! The exact normalized angular pushforward identities in (3.2). -/

noncomputable section
open Set MeasureTheory

namespace Paper34

lemma continuous_cosPoint (n : ℕ) :
    Continuous (fun theta : Point n => fun k => Real.cos (theta k)) :=
  continuous_pi (fun k => Real.continuous_cos.comp (continuous_apply k))

/-- The exact angular pushforward identity for every measurable scalar
function. Integrability is not needed for this Bochner-integral identity. -/
theorem chebyshev_integral_eq_normalized_angular {n : ℕ} (f : Point n → ℝ)
    (hf : Measurable f) :
    (∫ x, f x ∂chebyshevLaw n) =
      (Real.pi ^ n)⁻¹ * ∫ theta in Icc (fun _ : Fin n => (0 : ℝ))
        (fun _ => Real.pi), f (fun k => Real.cos (theta k)) := by
  rw [chebyshevLaw, integral_map_of_stronglyMeasurable (continuous_cosPoint n).measurable
    hf.stronglyMeasurable, angularLaw, integral_smul_measure]
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal (pow_pos Real.pi_pos n).le, smul_eq_mul]

/-- The second equality in (3.2), with its exact `π⁻ⁿ` normalization. -/
theorem l1Norm_eq_normalized_angular {n d : ℕ} (q : PolynomialSpace n d) :
    l1Norm q = (Real.pi ^ n)⁻¹ * ∫ theta in Icc (fun _ : Fin n => (0 : ℝ))
      (fun _ => Real.pi), |angularEval q theta| :=
  chebyshev_integral_eq_normalized_angular _ (continuous_polyEval q).abs.measurable

end Paper34
