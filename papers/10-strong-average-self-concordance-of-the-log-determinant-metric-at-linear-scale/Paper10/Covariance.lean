import Paper10.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.NoncommRing

noncomputable section
open Matrix
open scoped MatrixOrder
namespace Paper10
variable {d : ℕ}

/-- Order reversal for inverses of real positive definite matrices, by a sum of PSD congruences. -/
theorem inverse_mono {A B : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (hAB : (B - A).PosSemidef) :
    (A⁻¹ - B⁻¹).PosSemidef := by
  have ha := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hb := (Matrix.isUnit_iff_isUnit_det B).mp hB.isUnit
  have ha1 := Matrix.nonsing_inv_mul A ha
  have ha2 := Matrix.mul_nonsing_inv A ha
  have hb1 := Matrix.nonsing_inv_mul B hb
  have he : A⁻¹ - B⁻¹ = (A⁻¹ - B⁻¹) * A * (A⁻¹ - B⁻¹) +
      B⁻¹ * (B - A) * B⁻¹ := by
    noncomm_ring [ha1, ha2, hb1]
  have hsA : (A⁻¹)ᴴ = A⁻¹ := hA.inv.isHermitian.eq
  have hsB : (B⁻¹)ᴴ = B⁻¹ := hB.inv.isHermitian.eq
  have h1 := hA.posSemidef.conjTranspose_mul_mul_same (A⁻¹ - B⁻¹)
  have h2 := hAB.conjTranspose_mul_mul_same B⁻¹
  rw [Matrix.conjTranspose_sub, hsA, hsB] at h1
  rw [hsB] at h2
  rw [he]
  exact h1.add h2

/-- Exact cancellation at zero auxiliary precision. -/
theorem normalized_inverse_identity (T : Matrix (Fin d) (Fin d) ℝ)
    (hT : IsUnit T) {s : ℝ} (hs : 0 < s) :
    s • (T * (s • (Tᴴ * T))⁻¹ * Tᴴ) = 1 := by
  have ht := (Matrix.isUnit_iff_isUnit_det T).mp hT
  have hts : IsUnit Tᴴ := hT.star
  have htd := (Matrix.isUnit_iff_isUnit_det Tᴴ).mp hts
  have h1 := Matrix.nonsing_inv_mul T ht
  have h2 := Matrix.mul_nonsing_inv T ht
  have h3 := Matrix.nonsing_inv_mul Tᴴ htd
  have h4 := Matrix.mul_nonsing_inv Tᴴ htd
  have hi : (s • (Tᴴ * T))⁻¹ = s⁻¹ • (T⁻¹ * (Tᴴ)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [mul_inv_cancel₀ hs.ne']
    simp only [one_smul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Tᴴ)⁻¹ Tᴴ T, h3, Matrix.one_mul, h1]
  rw [hi]
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  rw [mul_inv_cancel₀ hs.ne', one_smul]
  simp only [← Matrix.mul_assoc]
  rw [h2, Matrix.one_mul, h3]

/-- Lemma 2.1 covariance contraction in arbitrary invertible Frobenius coordinates.
`T` is the congruence coordinate matrix and `D` is the arbitrary auxiliary PSD precision. -/
theorem lemma_2_1_contraction (T D : Matrix (Fin d) (Fin d) ℝ)
    (hT : IsUnit T) (hD : D.PosSemidef) {s : ℝ} (hs : 0 < s) :
    let Q := s • (T * (s • (Tᴴ * T) + D)⁻¹ * Tᴴ)
    Q.PosSemidef ∧ ((1 : Matrix (Fin d) (Fin d) ℝ) - Q).PosSemidef := by
  let C := s • (Tᴴ * T)
  let P := C + D
  have hC : C.PosDef := (Matrix.PosDef.conjTranspose_mul_self T
    (Matrix.mulVec_injective_of_isUnit hT)).smul hs
  have hP : P.PosDef := hC.add_posSemidef hD
  have hPC : (P - C).PosSemidef := by simpa only [P, add_sub_cancel_left] using hD
  have hi := inverse_mono hC hP hPC
  have hpos := hP.inv.posSemidef.conjTranspose_mul_mul_same Tᴴ
  have hupper := hi.conjTranspose_mul_mul_same Tᴴ
  simp only [Matrix.conjTranspose_conjTranspose] at hpos hupper
  constructor
  · exact hpos.smul hs.le
  · have he : (1 : Matrix (Fin d) (Fin d) ℝ) - s • (T * P⁻¹ * Tᴴ) =
        s • (T * (C⁻¹ - P⁻¹) * Tᴴ) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, smul_sub,
        normalized_inverse_identity T hT hs]
    rw [he]
    exact hupper.smul hs.le

end Paper10
