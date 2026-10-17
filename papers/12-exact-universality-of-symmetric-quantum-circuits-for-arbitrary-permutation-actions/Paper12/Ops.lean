import Paper12.Qubit

/-!
# Isometries, orthogonal projectors, and reflections

Operator-level facts used by the two-reflection identity and by oblivious
amplitude amplification.  Isometries `S, G : ℂ^k → ℂ^d` are rectangular
`d × k` matrices with `Sᴴ S = 1`.
-/

noncomputable section

namespace Paper12

open Matrix Complex

/-- `S : Fin k → Fin d` is an isometry when `Sᴴ S = I`. -/
def IsIsometry {d k : Type*} [Fintype d] [Fintype k] [DecidableEq d] [DecidableEq k] (S : Matrix d k ℂ) : Prop := Sᴴ * S = 1

/-- `Π` is an orthogonal projector. -/
def IsOrthoProj {d : Type*} [Fintype d] [DecidableEq d] (P : Matrix d d ℂ) : Prop :=
  P * P = P ∧ Pᴴ = P

/-- Reflection `I - 2 Π` through the kernel of an orthogonal projector. -/
def reflect {d : Type*} [Fintype d] [DecidableEq d] (P : Matrix d d ℂ) : Matrix d d ℂ :=
  1 - (2 : ℂ) • P

/-- Reflection through the range of an isometry: `I - 2 S Sᴴ`. -/
def reflectRange {d k : Type*} [Fintype d] [Fintype k] [DecidableEq d] [DecidableEq k] (S : Matrix d k ℂ) : Matrix d d ℂ :=
  1 - (2 : ℂ) • (S * Sᴴ)

theorem isometry_gram {d k : Type*} [Fintype d] [Fintype k] [DecidableEq d] [DecidableEq k] {S : Matrix d k ℂ} (h : IsIsometry S) :
    Sᴴ * S = 1 := h

theorem orthoProj_selfAdjoint {d : Type*} [Fintype d] [DecidableEq d] {P : Matrix d d ℂ}
    (h : IsOrthoProj P) : Pᴴ = P := h.2

theorem orthoProj_idem {d : Type*} [Fintype d] [DecidableEq d] {P : Matrix d d ℂ}
    (h : IsOrthoProj P) : P * P = P := h.1

/-- If `Π S = c • G` with `c ≠ 0` and both `S,G` isometries, then `Π G = G`. -/
theorem proj_fixes_of_smul {d k : Type*} [Fintype d] [Fintype k] [DecidableEq d] [DecidableEq k] {P : Matrix d d ℂ}
    {S G : Matrix d k ℂ} {c : ℂ}
    (hP : IsOrthoProj P) (hS : IsIsometry S) (hG : IsIsometry G)
    (h : P * S = c • G) (hc : c ≠ 0) : P * G = G := by
  have hPS : P * (P * S) = P * S := by
    rw [← Matrix.mul_assoc, hP.1]
  have hPS' : P * (c • G) = c • G := by rwa [h] at hPS
  have hsmul : (c : ℂ) • (P * G) = c • G := by
    rw [← Matrix.mul_smul P c G]
    exact hPS'
  exact (smul_right_inj hc).mp hsmul

/-- From `Π S = c • G` with isometries and `c ≠ 0`, one has `Gᴴ S = c • 1`. -/
theorem adj_cross {d k : Type*} [Fintype d] [Fintype k] [DecidableEq d] [DecidableEq k] {P : Matrix d d ℂ}
    {S G : Matrix d k ℂ} {c : ℂ}
    (hP : IsOrthoProj P) (hS : IsIsometry S) (hG : IsIsometry G)
    (h : P * S = c • G) (hc : c ≠ 0) : Gᴴ * S = c • 1 := by
  have hPG : P * G = G := proj_fixes_of_smul hP hS hG h hc
  have hGP : Gᴴ * P = Gᴴ := by
    have h2 : (P * G)ᴴ = Gᴴ := by rw [hPG]
    rw [Matrix.conjTranspose_mul, hP.2] at h2
    exact h2
  calc Gᴴ * S = (Gᴴ * P) * S := by rw [hGP]
    _ = Gᴴ * (P * S) := by rw [Matrix.mul_assoc]
    _ = Gᴴ * (c • G) := by rw [h]
    _ = c • (Gᴴ * G) := Matrix.mul_smul Gᴴ c G
    _ = c • 1 := by rw [hG]

end Paper12
