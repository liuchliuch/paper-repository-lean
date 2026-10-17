import Paper12.Qubit
import Paper12.Ops

/-!
# Two-reflection identity (Lemma 2.4)

Let `Π` be an orthogonal projector on a finite-dimensional Hilbert space and
let `S, G` be isometries into that space from the same domain.  If
`Π S = sin θ • G` with `0 < θ < π/2`, then
`B = (S - sin θ • G) / cos θ` is an isometry orthogonal to `G` with `Π B = 0`,
and for every `j ≥ 0`,
`(R_S R_G)^j S = (-1)^j (sin((2j+1)θ) G + cos((2j+1)θ) B)`.
-/

noncomputable section

namespace Paper12

open Matrix Complex

variable {d k : Type*} [Fintype d] [Fintype k] [DecidableEq d] [DecidableEq k]

/-- Decomposition data of Lemma 2.4. -/
structure TwoReflectionData (θ : ℝ) (P : Matrix d d ℂ)
    (S G : Matrix d k ℂ) : Prop where
  proj : IsOrthoProj P
  isoS : IsIsometry S
  isoG : IsIsometry G
  angle : 0 < θ ∧ θ < Real.pi / 2
  key : P * S = (Real.sin θ : ℂ) • G

/-- The complementary isometry `B = (S - sinθ G) / cosθ`. -/
def twoReflB (θ : ℝ) (S G : Matrix d k ℂ) : Matrix d k ℂ :=
  ((Real.cos θ : ℂ)⁻¹) • (S - (Real.sin θ : ℂ) • G)

/-- `R_G = I - 2Π`. -/
def RG (P : Matrix d d ℂ) : Matrix d d ℂ := reflect P

/-- `R_S = I - 2 S S†`. -/
def RS (S : Matrix d k ℂ) : Matrix d d ℂ := reflectRange S

theorem cos_ne_zero_of_mem {θ : ℝ} (h : 0 < θ ∧ θ < Real.pi / 2) :
    Real.cos θ ≠ 0 :=
  ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩)

theorem sin_ne_zero_of_mem {θ : ℝ} (h : 0 < θ ∧ θ < Real.pi / 2) :
    Real.sin θ ≠ 0 :=
  ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h.1 (by linarith))

theorem sin_c_ne_zero {θ : ℝ} (h : 0 < θ ∧ θ < Real.pi / 2) :
    (Real.sin θ : ℂ) ≠ 0 := by
  rw [Ne, ofReal_eq_zero]; exact sin_ne_zero_of_mem h

theorem cos_c_ne_zero {θ : ℝ} (h : 0 < θ ∧ θ < Real.pi / 2) :
    (Real.cos θ : ℂ) ≠ 0 := by
  rw [Ne, ofReal_eq_zero]; exact cos_ne_zero_of_mem h

theorem star_ofReal (r : ℝ) : star ((r : ℂ)) = (r : ℂ) :=
  Complex.conj_ofReal r

theorem sin_sq_c (θ : ℝ) :
    (Real.sin θ : ℂ) * (Real.sin θ : ℂ) = (((Real.sin θ : ℝ) ^ 2 : ℝ) : ℂ) := by
  rw [← ofReal_mul]; congr 1; ring

theorem cos_sq_c (θ : ℝ) :
    (Real.cos θ : ℂ) * (Real.cos θ : ℂ) = (((Real.cos θ : ℝ) ^ 2 : ℝ) : ℂ) := by
  rw [← ofReal_mul]; congr 1; ring

theorem one_sub_two_sin_sq (θ : ℝ) :
    (1 : ℂ) - (2 : ℂ) * ((Real.sin θ : ℂ) * (Real.sin θ : ℂ)) = (Real.cos (2 * θ) : ℂ) := by
  have h : (1 : ℝ) - 2 * (Real.sin θ * Real.sin θ) = Real.cos (2 * θ) := by
    nlinarith [Real.sin_sq_add_cos_sq θ, Real.cos_two_mul θ]
  have := congrArg ((↑) : ℝ → ℂ) h
  push_cast at this
  simpa using this

theorem one_sub_two_cos_sq (θ : ℝ) :
    (1 : ℂ) - (2 : ℂ) * ((Real.cos θ : ℂ) * (Real.cos θ : ℂ)) = - (Real.cos (2 * θ) : ℂ) := by
  have h : (1 : ℝ) - 2 * (Real.cos θ * Real.cos θ) = - Real.cos (2 * θ) := by
    nlinarith [Real.sin_sq_add_cos_sq θ, Real.cos_two_mul θ]
  have := congrArg ((↑) : ℝ → ℂ) h
  push_cast at this
  simpa using this

theorem two_sin_cos (θ : ℝ) :
    (2 : ℂ) * ((Real.sin θ : ℂ) * (Real.cos θ : ℂ)) = (Real.sin (2 * θ) : ℂ) := by
  have h : (2 : ℝ) * (Real.sin θ * Real.cos θ) = Real.sin (2 * θ) := by
    conv_rhs => rw [Real.sin_two_mul]
    ring
  have := congrArg ((↑) : ℝ → ℂ) h
  push_cast at this
  simpa using this

theorem sin_add_c (x y : ℝ) :
    (Real.sin x : ℂ) * (Real.cos y : ℂ) + (Real.cos x : ℂ) * (Real.sin y : ℂ) =
      (Real.sin (x + y) : ℂ) := by
  have := congrArg ((↑) : ℝ → ℂ) (Real.sin_add x y)
  push_cast at this
  simpa using this.symm

theorem cos_add_c (x y : ℝ) :
    (Real.cos x : ℂ) * (Real.cos y : ℂ) - (Real.sin x : ℂ) * (Real.sin y : ℂ) =
      (Real.cos (x + y) : ℂ) := by
  have := congrArg ((↑) : ℝ → ℂ) (Real.cos_add x y)
  push_cast at this
  simpa using this.symm

theorem twoRefl_proj_G {θ : ℝ} {P : Matrix d d ℂ}
    {S G : Matrix d k ℂ} (D : TwoReflectionData θ P S G) :
    P * G = G :=
  proj_fixes_of_smul D.proj D.isoS D.isoG D.key (sin_c_ne_zero D.angle)

theorem twoRefl_cross {θ : ℝ} {P : Matrix d d ℂ}
    {S G : Matrix d k ℂ} (D : TwoReflectionData θ P S G) :
    Gᴴ * S = (Real.sin θ : ℂ) • 1 :=
  adj_cross D.proj D.isoS D.isoG D.key (sin_c_ne_zero D.angle)

theorem twoRefl_SG {θ : ℝ} {P : Matrix d d ℂ}
    {S G : Matrix d k ℂ} (D : TwoReflectionData θ P S G) :
    Sᴴ * G = (Real.sin θ : ℂ) • 1 := by
  have h := twoRefl_cross D
  have h2 := congrArg (fun (M : Matrix k k ℂ) => Mᴴ) h
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_one, Matrix.conjTranspose_smul, star_ofReal] at h2
  exact h2

theorem twoRefl_proj_B {θ : ℝ} {P : Matrix d d ℂ}
    {S G : Matrix d k ℂ} (D : TwoReflectionData θ P S G) :
    P * twoReflB θ S G = 0 := by
  unfold twoReflB
  rw [Matrix.mul_smul, Matrix.mul_sub, D.key, Matrix.mul_smul, twoRefl_proj_G D]
  rw [smul_sub, smul_smul]
  exact sub_self _

theorem twoRefl_orth {θ : ℝ} {P : Matrix d d ℂ}
    {S G : Matrix d k ℂ} (D : TwoReflectionData θ P S G) :
    Gᴴ * twoReflB θ S G = 0 := by
  unfold twoReflB
  rw [Matrix.mul_smul, Matrix.mul_sub, twoRefl_cross D, Matrix.mul_smul, D.isoG]
  rw [smul_sub, smul_smul]
  exact sub_self _



theorem twoRefl_SB {θ : ℝ} {P : Matrix d d ℂ}
    {S G : Matrix d k ℂ} (D : TwoReflectionData θ P S G) :
    Sᴴ * twoReflB θ S G = (Real.cos θ : ℂ) • 1 := by
  have hsum : (Real.sin θ : ℂ) ^ 2 + (Real.cos θ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq θ
  have hscalar : (Real.cos θ : ℂ)⁻¹ * (1 - (Real.sin θ : ℂ) ^ 2)
      = (Real.cos θ : ℂ) := by
    have h : 1 - (Real.sin θ : ℂ) ^ 2 = (Real.cos θ : ℂ) ^ 2 := by
      linear_combination -hsum
    rw [h, sq, inv_mul_cancel_left₀ (cos_c_ne_zero D.angle)]
  unfold twoReflB
  rw [Matrix.mul_smul, Matrix.mul_sub, D.isoS, Matrix.mul_smul, twoRefl_SG D]
  have hm : (1 : Matrix k k ℂ) -
      (Real.sin θ : ℂ) • ((Real.sin θ : ℂ) • 1) =
      (1 - (Real.sin θ : ℂ) ^ 2) • 1 := by module
  rw [hm, smul_smul, hscalar]

theorem twoRefl_BS {θ : ℝ} {P : Matrix d d ℂ}
    {S G : Matrix d k ℂ} (D : TwoReflectionData θ P S G) :
    (twoReflB θ S G)ᴴ * S = (Real.cos θ : ℂ) • 1 := by
  have h := congrArg Matrix.conjTranspose (twoRefl_SB D)
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one, star_ofReal] using h

theorem twoRefl_BG {θ : ℝ} {P : Matrix d d ℂ}
    {S G : Matrix d k ℂ} (D : TwoReflectionData θ P S G) :
    (twoReflB θ S G)ᴴ * G = 0 := by
  have h := congrArg Matrix.conjTranspose (twoRefl_orth D)
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_zero] using h

theorem twoRefl_B_iso {θ : ℝ} {P : Matrix d d ℂ}
    {S G : Matrix d k ℂ} (D : TwoReflectionData θ P S G) :
    IsIsometry (twoReflB θ S G) := by
  change (twoReflB θ S G)ᴴ *
    ((Real.cos θ : ℂ)⁻¹ • (S - (Real.sin θ : ℂ) • G)) = 1
  rw [Matrix.mul_smul, Matrix.mul_sub, twoRefl_BS D,
    Matrix.mul_smul, twoRefl_BG D, smul_zero, sub_zero, smul_smul,
    inv_mul_cancel₀ (cos_c_ne_zero D.angle), one_smul]

theorem twoRefl_decompose {θ : ℝ} {P : Matrix d d ℂ}
    {S G : Matrix d k ℂ} (D : TwoReflectionData θ P S G) :
    S = (Real.sin θ : ℂ) • G + (Real.cos θ : ℂ) • twoReflB θ S G := by
  simp only [twoReflB, smul_smul, mul_inv_cancel₀ (cos_c_ne_zero D.angle), one_smul]
  abel

theorem twoRefl_step_G {θ : ℝ} {P : Matrix d d ℂ}
    {S G : Matrix d k ℂ} (D : TwoReflectionData θ P S G) :
    (RS S * RG P) * G =
      -(Real.cos (2 * θ) : ℂ) • G + (Real.sin (2 * θ) : ℂ) • twoReflB θ S G := by
  have hRG : RG P * G = -G := by
    simp only [RG, reflect, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul,
      twoRefl_proj_G D]
    module
  have hRS : RS S * G = G - (2 : ℂ) • ((Real.sin θ : ℂ) • S) := by
    simp only [RS, reflectRange, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul,
      Matrix.mul_assoc, twoRefl_SG D, Matrix.mul_smul, Matrix.mul_one]
  have hdec := congrArg (fun T : Matrix d k ℂ =>
    G - (2 : ℂ) • ((Real.sin θ : ℂ) • T)) (twoRefl_decompose D)
  have hRS2 := hRS.trans hdec
  rw [Matrix.mul_assoc, hRG, Matrix.mul_neg, hRS2]
  rw [← one_sub_two_sin_sq θ, ← two_sin_cos θ]
  module

theorem twoRefl_step_B {θ : ℝ} {P : Matrix d d ℂ}
    {S G : Matrix d k ℂ} (D : TwoReflectionData θ P S G) :
    (RS S * RG P) * twoReflB θ S G =
      -(Real.sin (2 * θ) : ℂ) • G - (Real.cos (2 * θ) : ℂ) • twoReflB θ S G := by
  have hRG : RG P * twoReflB θ S G = twoReflB θ S G := by
    simp [RG, reflect, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul,
      twoRefl_proj_B D]
  have hRS : RS S * twoReflB θ S G = twoReflB θ S G -
      (2 : ℂ) • ((Real.cos θ : ℂ) • S) := by
    simp only [RS, reflectRange, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul,
      Matrix.mul_assoc, twoRefl_SB D, Matrix.mul_smul, Matrix.mul_one]
  have hdec := congrArg (fun T : Matrix d k ℂ =>
    twoReflB θ S G - (2 : ℂ) • ((Real.cos θ : ℂ) • T)) (twoRefl_decompose D)
  have hRS2 := hRS.trans hdec
  rw [Matrix.mul_assoc, hRG, hRS2]
  have hs := congrArg (fun z : ℂ => z • twoReflB θ S G) (one_sub_two_cos_sq θ)
  rw [← two_sin_cos θ]
  linear_combination (norm := module) hs

theorem two_reflection_identity {θ : ℝ} {P : Matrix d d ℂ}
    {S G : Matrix d k ℂ} (D : TwoReflectionData θ P S G) (j : ℕ) :
    (RS S * RG P) ^ j * S = (-1 : ℂ) ^ j •
      ((Real.sin ((2 * j + 1) * θ) : ℂ) • G +
        (Real.cos ((2 * j + 1) * θ) : ℂ) • twoReflB θ S G) := by
  induction j with
  | zero => simpa using twoRefl_decompose D
  | succ j ih =>
    rw [pow_succ', Matrix.mul_assoc, ih, Matrix.mul_smul, Matrix.mul_add,
      Matrix.mul_smul, Matrix.mul_smul, twoRefl_step_G D, twoRefl_step_B D]
    have hangle : (2 * (↑(j + 1) : ℝ) + 1) * θ = (2 * j + 1) * θ + 2 * θ := by
      push_cast; ring
    rw [hangle, pow_succ]
    have hsin := sin_add_c ((2 * j + 1) * θ) (2 * θ)
    have hcos := cos_add_c ((2 * j + 1) * θ) (2 * θ)
    rw [← hsin, ← hcos]
    module

theorem two_reflection_bundle {θ : ℝ} {P : Matrix d d ℂ}
    {S G : Matrix d k ℂ} (D : TwoReflectionData θ P S G) :
    IsIsometry (twoReflB θ S G) ∧ Gᴴ * twoReflB θ S G = 0 ∧
      P * twoReflB θ S G = 0 ∧
      ∀ j : ℕ, (RS S * RG P) ^ j * S = (-1 : ℂ) ^ j •
        ((Real.sin ((2 * j + 1) * θ) : ℂ) • G +
          (Real.cos ((2 * j + 1) * θ) : ℂ) • twoReflB θ S G) :=
  ⟨twoRefl_B_iso D, twoRefl_orth D, twoRefl_proj_B D, two_reflection_identity D⟩

end Paper12
