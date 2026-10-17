import Paper10.Theorems
import Paper10.ProposalLaw

noncomputable section
open Matrix MeasureTheory
open scoped MatrixOrder
namespace Paper10
variable {q m : ℕ}

/-- Constant rescaling cancels in the normalized covariance. -/
theorem auxiliaryCovariance_rescale {s d : ℝ} (hs : 0 < s) (hd : 0 < d)
    (E : Matrix (Fin m) (Fin m) ℝ) (hE : E.PosSemidef) :
    auxiliaryCovariance (d * s) (d • E) = auxiliaryCovariance s E := by
  have hp : (s • (1 : Matrix (Fin m) (Fin m) ℝ) + E).PosDef :=
    (Matrix.PosDef.smul (Matrix.PosDef.one) hs).add_posSemidef hE
  letI : Invertible d := invertibleOfNonzero hd.ne'
  have hi := Matrix.inv_smul (A := s • (1 : Matrix (Fin m) (Fin m) ℝ) + E) d
    ((Matrix.isUnit_iff_isUnit_det _).mp hp.isUnit)
  unfold auxiliaryCovariance
  rw [show (d * s) • (1 : Matrix (Fin m) (Fin m) ℝ) + d • E =
      d • (s • (1 : Matrix (Fin m) (Fin m) ℝ) + E) by rw [smul_add, smul_smul], hi]
  simp only [invOf_eq_inv, smul_smul]
  congr 1
  field_simp

/-- The normalized time transforms with the square root of the constant scale. -/
theorem tOf_rescale {s d : ℝ} (hs : 0 < s) (hd : 0 < d) (r : ℝ) :
    tOf (q := q) r (d * s) = tOf (q := q) (r / Real.sqrt d) s := by
  unfold tOf
  rw [show (n q : ℝ) * (d * s) = d * ((n q : ℝ) * s) by ring,
    Real.sqrt_mul hd.le, div_div]

/-- Equality of the actual Gaussian proposals under the change r↦r/√d, E↦E/d. -/
theorem proposalStep_rescale (F : Fin m → Matrix (Fin q) (Fin q) ℝ)
    (R : Matrix (Fin q) (Fin q) ℝ) {s d : ℝ} (hs : 0 < s) (hd : 0 < d)
    (r : ℝ) (E : Matrix (Fin m) (Fin m) ℝ) (hE : E.PosSemidef)
    (hds : 0 < d * s) (hdE : (d • E).PosSemidef) :
    proposalStep F R (d * s) r (d • E) hds hdE =
      proposalStep F R s (r / Real.sqrt d) E hs hE := by
  have he := auxiliaryCovariance_rescale hs hd E hE
  have hev : auxiliaryEigenvalues (d * s) (d • E) hds hdE = auxiliaryEigenvalues s E hs hE := by
    unfold auxiliaryEigenvalues
    congr 1
  have hrot : auxiliaryRotation (d * s) (d • E) hds hdE = auxiliaryRotation s E hs hE := by
    unfold auxiliaryRotation
    congr 1
  funext ω
  simp only [proposalStep, tOf_rescale hs hd, hev, hrot]

/-- The SASC event transforms exactly with the squared radius. -/
theorem sascEvent_rescale {d s : ℝ} (hd : 0 < d) (X Z H : Matrix (Fin q) (Fin q) ℝ)
    (ε r : ℝ) :
    sascEvent (d * s) X Z H ε r ↔ sascEvent s X Z H ε (r / Real.sqrt d) := by
  have hd0 := hd.ne'
  have hsq := Real.sq_sqrt hd.le
  have he : (r / Real.sqrt d) ^ 2 = r ^ 2 / d := by rw [div_pow, hsq]
  unfold sascEvent localNormSq g
  rw [he]
  have hm : d * s * G Z H H - d * s * G X H H = d * (s * G Z H H - s * G X H H) := by ring
  rw [hm]
  constructor
  · rintro ⟨hz, hh⟩
    refine ⟨hz, ?_⟩
    apply (mul_le_mul_left hd).mp
    convert hh using 1 <;> field_simp <;> ring
  · rintro ⟨hz, hh⟩
    refine ⟨hz, ?_⟩
    have ht := (mul_le_mul_left hd).mpr hh
    convert ht using 1 <;> field_simp <;> ring

/-- Section 4: a constant rescaling preserves SASC, with radius multiplied by √d. -/
theorem sasc_rescale {s d : ℝ} (hsasc : SASC q s) (hd : 0 < d) : SASC q (d * s) := by
  obtain ⟨hs, hh⟩ := hsasc
  refine ⟨mul_pos hd hs, ?_⟩
  intro ε hε hε1
  obtain ⟨ρ, hρ, hbound⟩ := hh ε hε hε1
  refine ⟨Real.sqrt d * ρ, mul_pos (Real.sqrt_pos.mpr hd) hρ, ?_⟩
  intro X hX E hE r hr hr1
  have hdi : 0 ≤ d⁻¹ := inv_nonneg.mpr hd.le
  have hE' : (d⁻¹ • E).PosSemidef := hE.smul hdi
  have hu : 0 < r / Real.sqrt d := div_pos hr (Real.sqrt_pos.mpr hd)
  have hu1 : r / Real.sqrt d ≤ ρ := (div_le_iff₀ (Real.sqrt_pos.mpr hd)).mpr (by nlinarith)
  have hb := hbound X hX (d⁻¹ • E) hE' (r / Real.sqrt d) hu hu1
  have hEs : d • (d⁻¹ • E) = E := by rw [smul_smul, mul_inv_cancel₀ hd.ne', one_smul]
  have hp := proposalStep_rescale (canonicalF q) (CFC.sqrt X) hs hd r (d⁻¹ • E) hE'
    (mul_pos hd hs) (by simpa only [hEs] using hE)
  have hp' : proposalStep (canonicalF q) (CFC.sqrt X) (d * s) r E (mul_pos hd hs) hE =
      proposalStep (canonicalF q) (CFC.sqrt X) s (r / Real.sqrt d) (d⁻¹ • E) hs hE' := by
    convert hp using 2 <;> exact hEs.symm
  simpa only [hp', sascEvent_rescale hd] using hb

/-- At a fixed matrix order, every positive scale is SASC. The radius may depend on q,s. -/
theorem sasc_all_positive (hq : 0 < q) {s : ℝ} (hs : 0 < s) : SASC q s := by
  have hh := sasc_rescale (Main.thm_1_3_sasc q hq (s := c q) le_rfl)
    (div_pos hs (c_pos q))
  simpa only [div_mul_cancel₀ s (c_pos q).ne'] using hh

/-- Definition 1.2 for a fixed positive rescaling of the theorem's entire metric family. -/
def UniformScaledSASC (d : ℝ) (hd : 0 < d) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ ρ : ℝ, 0 < ρ ∧
    ∀ (q : ℕ) (hq : 0 < q) (s : ℝ) (hs : c q ≤ s)
      (X : Matrix (Fin q) (Fin q) ℝ), X.PosDef →
    ∀ (E : Matrix (Fin (n q)) (Fin (n q)) ℝ) (hE : E.PosSemidef)
      (r : ℝ), 0 < r → r ≤ ρ →
      let H := proposalStep (canonicalF q) (CFC.sqrt X) (d * s) r E
        (mul_pos hd (lt_of_lt_of_le (c_pos q) hs)) hE
      1 - ε ≤ (stdGaussianMeasure (n q)).real {ω | sascEvent (d * s) X (X + H ω) (H ω) ε r}

/-- The uniform radius of a constantly rescaled family is multiplied by √d. -/
theorem uniform_sasc_rescale {d : ℝ} (hd : 0 < d) (hh : UniformSASC) : UniformScaledSASC d hd := by
  intro ε hε hε1
  obtain ⟨ρ, hρ, hbound⟩ := hh ε hε hε1
  refine ⟨Real.sqrt d * ρ, mul_pos (Real.sqrt_pos.mpr hd) hρ, ?_⟩
  intro q hq s hs X hX E hE r hr hr1
  have hs0 := lt_of_lt_of_le (c_pos q) hs
  have hE' : (d⁻¹ • E).PosSemidef := hE.smul (inv_nonneg.mpr hd.le)
  have hu := div_pos hr (Real.sqrt_pos.mpr hd)
  have hu1 : r / Real.sqrt d ≤ ρ := (div_le_iff₀ (Real.sqrt_pos.mpr hd)).mpr (by nlinarith)
  have hb := hbound q hq s hs X hX (d⁻¹ • E) hE' (r / Real.sqrt d) hu hu1
  have hEs : d • (d⁻¹ • E) = E := by rw [smul_smul, mul_inv_cancel₀ hd.ne', one_smul]
  have hp := proposalStep_rescale (canonicalF q) (CFC.sqrt X) hs0 hd r (d⁻¹ • E) hE'
    (mul_pos hd hs0) (by simpa only [hEs] using hE)
  have hp' : proposalStep (canonicalF q) (CFC.sqrt X) (d * s) r E (mul_pos hd hs0) hE =
      proposalStep (canonicalF q) (CFC.sqrt X) s (r / Real.sqrt d) (d⁻¹ • E) hs0 hE' := by
    convert hp using 2 <;> exact hEs.symm
  simpa only [hp', sascEvent_rescale hd] using hb

end Paper10
