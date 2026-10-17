import Paper12.Universality

noncomputable section
namespace Paper12
open Matrix Classical

def complementaryMap {d k : Type*} (S G : Matrix d k ℂ) (t r : ℝ) : Matrix d k ℂ :=
  (r : ℂ)⁻¹ • (S - (t : ℂ) • G)

theorem complementary_bundle {d k : Type*} [Fintype d] [Fintype k]
    [DecidableEq d] [DecidableEq k] (S G : Matrix d k ℂ) (t r : ℝ)
    (hS : IsIsometry S) (hG : IsIsometry G) (hcross : Gᴴ * S = (t : ℂ) • 1)
    (hsq : t ^ 2 + r ^ 2 = 1) (hr : r ≠ 0) :
    IsIsometry (complementaryMap S G t r) ∧ Gᴴ * complementaryMap S G t r = 0 ∧
      S = (t : ℂ) • G + (r : ℂ) • complementaryMap S G t r := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hsquare : (t : ℂ) ^ 2 + (r : ℂ) ^ 2 = 1 := by exact_mod_cast hsq
  have hSG : Sᴴ * G = (t : ℂ) • 1 := by
    have hh := congrArg Matrix.conjTranspose hcross
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_one, star_ofReal] using hh
  have hGF : Gᴴ * complementaryMap S G t r = 0 := by
    rw [complementaryMap, Matrix.mul_smul, Matrix.mul_sub, hcross,
      Matrix.mul_smul, hG, sub_self, smul_zero]
  have hSF : Sᴴ * complementaryMap S G t r = (r : ℂ) • 1 := by
    rw [complementaryMap, Matrix.mul_smul, Matrix.mul_sub, hS,
      Matrix.mul_smul, hSG]
    have hm : (1 : Matrix k k ℂ) - (t : ℂ) • ((t : ℂ) • 1) = (r : ℂ) ^ 2 • 1 := by
      have hc : 1 - (t : ℂ) ^ 2 = (r : ℂ) ^ 2 := by linear_combination -hsquare
      rw [← hc]
      module
    rw [hm, smul_smul, sq, inv_mul_cancel_left₀ hrC]
  have hFS : (complementaryMap S G t r)ᴴ * S = (r : ℂ) • 1 := by
    have hh := congrArg Matrix.conjTranspose hSF
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_one, star_ofReal] using hh
  have hFG : (complementaryMap S G t r)ᴴ * G = 0 := by
    have hh := congrArg Matrix.conjTranspose hGF
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] using hh
  refine ⟨?_, hGF, ?_⟩
  · change (complementaryMap S G t r)ᴴ * ((r : ℂ)⁻¹ • (S - (t : ℂ) • G)) = 1
    rw [Matrix.mul_smul, Matrix.mul_sub, hFS, Matrix.mul_smul, hFG,
      smul_zero, sub_zero, smul_smul, inv_mul_cancel₀ hrC, one_smul]
  · simp only [complementaryMap, smul_smul, mul_inv_cancel₀ hrC, one_smul]
    abel

variable {X W : Type*} [Fintype X] [Fintype W]

/-- Equation (17): a fixed complementary isometry, independent of the input,
with identically zero workspace-zero block. -/
theorem block_failure_decomposition (A : Circuit (X ⊕ W)) (U : Op X) (p : ℝ)
    (hU : Uᴴ * U = 1) (hp : 0 ≤ p) (hp1 : p < 1) (hb : BlockEncodes A.unitary p U) :
    ∃ F : Matrix (Basis (X ⊕ W)) (Basis X) ℂ,
      IsIsometry F ∧ (zeroEmbed (X := X) (W := W))ᴴ * F = 0 ∧
      A.unitary * zeroEmbed = (Real.sqrt p : ℂ) • (zeroEmbed * U) +
        (Real.sqrt (1 - p) : ℂ) • F := by
  let E := zeroEmbed (X := X) (W := W)
  let S := A.unitary * E
  let G := E * U
  have hE : Eᴴ * E = 1 := zeroEmbed_isometry
  have hS : IsIsometry S := isometry_comp A.unitary E (Circuit.unitary_isUnitary A) hE
  have hG : IsIsometry G := isometry_comp E U hE hU
  have hES : Eᴴ * S = (Real.sqrt p : ℂ) • U := by
    simpa only [S, E, ← Matrix.mul_assoc, zeroEmbed_block] using hb
  have hcross : Gᴴ * S = (Real.sqrt p : ℂ) • 1 := by
    simp only [G, Matrix.conjTranspose_mul, Matrix.mul_assoc, hES,
      Matrix.mul_smul, hU]
  obtain ⟨hF, _, hdec⟩ := complementary_bundle S G (Real.sqrt p) (Real.sqrt (1-p))
    hS hG hcross (by rw [Real.sq_sqrt hp, Real.sq_sqrt (by linarith)]; ring)
    (ne_of_gt (Real.sqrt_pos.mpr (by linarith)))
  refine ⟨complementaryMap S G (Real.sqrt p) (Real.sqrt (1-p)), hF, ?_, hdec⟩
  rw [complementaryMap, Matrix.mul_smul, Matrix.mul_sub, hES, Matrix.mul_smul]
  have hEG : Eᴴ * G = U := by
    change Eᴴ * (E * U) = U
    rw [← Matrix.mul_assoc, hE, Matrix.one_mul]
  rw [hEG, sub_self, smul_zero]
end Paper12
