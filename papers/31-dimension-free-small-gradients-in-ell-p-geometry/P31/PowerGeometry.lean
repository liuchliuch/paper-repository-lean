import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Data.Sign.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Finite-dimensional real power geometry

The objects here are the actual coordinate formulas for the finite-dimensional ℓₚ
norm and the paper's duality map.  The connection with mathlib's `PiLp` norm is
proved explicitly.  No Clarkson inequality is postulated in this file.
-/

noncomputable section
open scoped BigOperators

namespace P31

variable {ι : Type*} [Fintype ι]

/-- The sum of the real `p`-powers of absolute coordinate values. -/
def lpPower (p : ℝ) (v : ι → ℝ) : ℝ := ∑ i, |v i| ^ p

/-- The finite-dimensional ℓₚ norm, written in coordinates. -/
def lpNorm (p : ℝ) (v : ι → ℝ) : ℝ := lpPower p v ^ (1 / p)

/-- The Hölder conjugate of a finite real exponent greater than one. -/
def dualExponent (p : ℝ) : ℝ := p / (p - 1)

/-- A coordinate of the paper's duality map, with sign zero equal to zero. -/
def dualityCoordinate (p t : ℝ) : ℝ := (SignType.sign t : ℝ) * |t| ^ (p - 1)

/-- Equation (2.3), as an actual finite vector. -/
def dualityMap (p : ℝ) (v : ι → ℝ) : ι → ℝ := fun i ↦ dualityCoordinate p (v i)

/-- The normalization in equation (2.4). -/
def atomScale (p : ℝ) : ℝ := (2 : ℝ) ^ (p - 2)

/-- The shifted-power atom in equation (2.4). -/
def powerAtom (p : ℝ) (c x : ι → ℝ) : ℝ := atomScale p / p * lpPower p (x - c)

lemma lpPower_nonneg (p : ℝ) (v : ι → ℝ) : 0 ≤ lpPower p v :=
  Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _

lemma lpNorm_nonneg (p : ℝ) (v : ι → ℝ) : 0 ≤ lpNorm p v :=
  Real.rpow_nonneg (lpPower_nonneg p v) _

/-- The coordinate norm is precisely mathlib's finite `PiLp` norm. -/
theorem lpNorm_eq_piLp_norm (p : ℝ) (hp : 0 < p) (v : ι → ℝ) :
    lpNorm p v = ‖(WithLp.toLp (ENNReal.ofReal p) v : PiLp (ENNReal.ofReal p) (fun _ : ι ↦ ℝ))‖ := by
  rw [PiLp.norm_eq_sum (by simpa [ENNReal.toReal_ofReal hp.le] using hp)]
  simp [lpNorm, lpPower, ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs]

lemma lpNorm_rpow (p : ℝ) (hp : 0 < p) (v : ι → ℝ) :
    lpNorm p v ^ p = lpPower p v := by
  rw [lpNorm, ← Real.rpow_mul (lpPower_nonneg p v)]
  rw [one_div_mul_cancel hp.ne', Real.rpow_one]

lemma dualExponent_pos {p : ℝ} (hp : 1 < p) : 0 < dualExponent p :=
  div_pos (by linarith) (by linarith)

lemma sub_one_mul_dualExponent {p : ℝ} (hp : 1 < p) :
    (p - 1) * dualExponent p = p := by
  unfold dualExponent
  field_simp [sub_ne_zero.mpr (ne_of_gt hp)]

lemma abs_dualityCoordinate {p : ℝ} (hp : 1 < p) (t : ℝ) :
    |dualityCoordinate p t| = |t| ^ (p - 1) := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · simp [dualityCoordinate, ht, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg t) _)]
  · simp [dualityCoordinate, Real.zero_rpow (by linarith : p - 1 ≠ 0)]
  · simp [dualityCoordinate, ht, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg t) _)]

/-- The coordinate form also equals the smooth norm-power derivative formula,
including at zero. -/
lemma dualityCoordinate_eq {p : ℝ} (hp : 1 < p) (t : ℝ) :
    dualityCoordinate p t = |t| ^ (p - 2) * t := by
  have he : p - 1 = (p - 2) + 1 := by ring
  rw [dualityCoordinate, he, Real.rpow_add_one' (abs_nonneg t) (by linarith)]
  calc
    (SignType.sign t : ℝ) * (|t| ^ (p - 2) * |t|) =
        |t| ^ (p - 2) * ((SignType.sign t : ℝ) * |t|) := by ring
    _ = |t| ^ (p - 2) * t := by rw [sign_mul_abs]

omit [Fintype ι] in
@[simp] theorem dualityMap_two (v : ι → ℝ) : dualityMap 2 v = v := by
  ext i
  norm_num [dualityMap, dualityCoordinate]

/-- The equality of sums in the proof of (2.5), with all exponents real. -/
theorem lpPower_dualityMap {p : ℝ} (hp : 1 < p) (v : ι → ℝ) :
    lpPower (dualExponent p) (dualityMap p v) = lpPower p v := by
  unfold lpPower
  apply Finset.sum_congr rfl
  intro i _
  rw [dualityMap, abs_dualityCoordinate hp, ← Real.rpow_mul (abs_nonneg (v i)),
    sub_one_mul_dualExponent hp]

/-- Equation (2.5): the genuine dual ℓ_q norm of the duality vector. -/
theorem dualityMap_norm {p : ℝ} (hp : 1 < p) (v : ι → ℝ) :
    lpNorm (dualExponent p) (dualityMap p v) = lpNorm p v ^ (p - 1) := by
  rw [lpNorm, lpPower_dualityMap hp, lpNorm, ← Real.rpow_mul (lpPower_nonneg p v)]
  congr 1
  unfold dualExponent
  field_simp

/-- The scalar derivative of the power atom before its normalization. -/
theorem hasDerivAt_abs_rpow_duality {p : ℝ} (hp : 1 < p) (t : ℝ) :
    HasDerivAt (fun z : ℝ ↦ |z| ^ p) (p * dualityCoordinate p t) t := by
  convert hasDerivAt_abs_rpow t hp using 1
  rw [dualityCoordinate_eq hp]
  ring

/-- The linear functional represented by a coordinate vector under the usual
pairing; the ambient function-space norm is irrelevant to the derivative. -/
def coordinateFunctional (v : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, (v i) • ContinuousLinearMap.proj i

lemma coordinateFunctional_apply (v h : ι → ℝ) :
    coordinateFunctional v h = ∑ i, v i * h i := by
  simp [coordinateFunctional]

/-- The actual Fréchet derivative of the shifted atom, represented by the
paper's vector `a_p J_p(x-c)`. -/
theorem powerAtom_hasFDerivAt {p : ℝ} (hp : 1 < p) (c x : ι → ℝ) :
    HasFDerivAt (powerAtom p c)
      (coordinateFunctional (fun i ↦ atomScale p * dualityMap p (x - c) i)) x := by
  have hcoord (i : ι) : HasFDerivAt (𝕜 := ℝ) (fun y : ι → ℝ ↦ |y i - c i| ^ p)
      ((p * dualityCoordinate p (x i - c i)) • ContinuousLinearMap.proj i) x := by
    convert (hasDerivAt_abs_rpow_duality hp (x i - c i)).comp_hasFDerivAt x
      ((hasFDerivAt_apply (𝕜 := ℝ) i x).sub_const (c i)) using 1
  have hsum := (HasFDerivAt.fun_sum fun i (_ : i ∈ (Finset.univ : Finset ι)) ↦ hcoord i)
  have hscaled := hsum.const_mul (atomScale p / p)
  have heq : coordinateFunctional (fun i ↦ atomScale p * dualityMap p (x - c) i) =
      (atomScale p / p) •
        (∑ i, (p * dualityCoordinate p (x i - c i)) •
          (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) := by
    ext h
    simp only [coordinateFunctional, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, ContinuousLinearMap.proj_apply,
      dualityMap, Pi.sub_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    field_simp [ne_of_gt (lt_trans zero_lt_one hp)]
  rw [heq]
  exact hscaled

/-- Evaluation of the derivative displays the gradient formula in (2.5). -/
theorem powerAtom_fderiv_apply {p : ℝ} (hp : 1 < p) (c x h : ι → ℝ) :
    fderiv ℝ (powerAtom p c) x h =
      ∑ i, (atomScale p * dualityMap p (x - c) i) * h i := by
  rw [(powerAtom_hasFDerivAt hp c x).fderiv, coordinateFunctional_apply]

lemma atomScale_pos (p : ℝ) : 0 < atomScale p :=
  Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _

lemma powerAtom_nonneg {p : ℝ} (hp : 0 < p) (c x : ι → ℝ) :
    0 ≤ powerAtom p c x :=
  mul_nonneg (div_nonneg (atomScale_pos p).le hp.le) (lpPower_nonneg p _)

@[simp] lemma powerAtom_self {p : ℝ} (hp : 0 < p) (c : ι → ℝ) :
    powerAtom p c c = 0 := by
  simp [powerAtom, lpPower, Real.zero_rpow hp.ne']

lemma powerAtom_eq_lpNorm {p : ℝ} (hp : 0 < p) (c x : ι → ℝ) :
    powerAtom p c x = atomScale p / p * lpNorm p (x - c) ^ p := by
  rw [lpNorm_rpow p hp]
  rfl

/-- Shifted atom sublevels are precisely norm-distance sublevels; this is the
radial monotonicity required by the minimizer transport proof. -/
theorem powerAtom_sublevel_iff {p : ℝ} (hp : 0 < p) (c x y : ι → ℝ) :
    powerAtom p c x ≤ powerAtom p c y ↔ lpNorm p (x - c) ≤ lpNorm p (y - c) := by
  rw [powerAtom_eq_lpNorm hp, powerAtom_eq_lpNorm hp]
  exact (mul_le_mul_left (div_pos (atomScale_pos p) hp)).trans
    (Real.rpow_le_rpow_iff (lpNorm_nonneg p _) (lpNorm_nonneg p _) hp)

/-- The Jensen convention (2.1) for the actual finite ℓₚ coordinate formula. -/
def LpPowerJensen (p μ : ℝ) (f : (ι → ℝ) → ℝ) : Prop :=
  ∀ x y (θ : ℝ), 0 ≤ θ → θ ≤ 1 →
    f (fun i ↦ (1 - θ) * x i + θ * y i) ≤
      (1 - θ) * f x + θ * f y - μ / p * θ * (1 - θ) * lpPower p (x - y)

/-- The scalar input (2.9), kept as an explicit proposition.  This definition
is not an assertion that the input has been proved. -/
def ScalarWeightedClarkson (p : ℝ) : Prop :=
  ∀ u v (θ : ℝ), 0 ≤ θ → θ ≤ 1 →
    |(1 - θ) * u + θ * v| ^ p ≤
      (1 - θ) * |u| ^ p + θ * |v| ^ p -
        (2 : ℝ) ^ (2 - p) * θ * (1 - θ) * |u - v| ^ p

/-- The coordinate summation and exact normalization step of Lemma 2.1.
`hClarkson` is an explicit missing scalar input, not a theorem proved here. -/
theorem powerAtom_jensen_of_scalar_clarkson {p : ℝ} (hp : 0 < p)
    (hClarkson : ScalarWeightedClarkson p) (c : ι → ℝ) :
    LpPowerJensen p 1 (powerAtom p c) := by
  intro x y θ hθ₀ hθ₁
  have hs : lpPower p ((fun i ↦ (1 - θ) * x i + θ * y i) - c) ≤
      (1 - θ) * lpPower p (x - c) + θ * lpPower p (y - c) -
        (2 : ℝ) ^ (2 - p) * θ * (1 - θ) * lpPower p (x - y) := by
    simp only [lpPower, Pi.sub_apply, Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hm : (1 - θ) * x i + θ * y i - c i =
        (1 - θ) * (x i - c i) + θ * (y i - c i) := by ring
    have hd : x i - y i = (x i - c i) - (y i - c i) := by ring
    rw [hm, hd]
    exact hClarkson (x i - c i) (y i - c i) θ hθ₀ hθ₁
  have hcancel : atomScale p * (2 : ℝ) ^ (2 - p) = 1 := by
    rw [atomScale, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    simp
  have hcancel' : atomScale p / p * (2 : ℝ) ^ (2 - p) = 1 / p := by
    calc
      atomScale p / p * (2 : ℝ) ^ (2 - p) =
        (atomScale p * (2 : ℝ) ^ (2 - p)) / p := by ring
      _ = 1 / p := by rw [hcancel]
  have hmul := mul_le_mul_of_nonneg_left hs (div_nonneg (atomScale_pos p).le hp.le)
  change atomScale p / p * lpPower p ((fun i ↦ (1 - θ) * x i + θ * y i) - c) ≤
    (1 - θ) * (atomScale p / p * lpPower p (x - c)) +
      θ * (atomScale p / p * lpPower p (y - c)) -
      1 / p * θ * (1 - θ) * lpPower p (x - y)
  apply hmul.trans_eq
  calc
    atomScale p / p * ((1 - θ) * lpPower p (x - c) + θ * lpPower p (y - c) -
      (2 : ℝ) ^ (2 - p) * θ * (1 - θ) * lpPower p (x - y)) =
      (1 - θ) * (atomScale p / p * lpPower p (x - c)) +
      θ * (atomScale p / p * lpPower p (y - c)) -
      (atomScale p / p * (2 : ℝ) ^ (2 - p)) * θ * (1 - θ) * lpPower p (x - y) := by ring
    _ = _ := by rw [hcancel']

/-- Jensen moduli add under nonnegative finite weighted sums. This is the
last implication of Lemma 2.1, with each atom's Jensen property explicit. -/
theorem lpPowerJensen_weighted_sum {κ : Type*} (s : Finset κ)
    (p : ℝ) (μ b : κ → ℝ) (f : κ → (ι → ℝ) → ℝ)
    (hb : ∀ j ∈ s, 0 ≤ b j) (hf : ∀ j ∈ s, LpPowerJensen p (μ j) (f j)) :
    LpPowerJensen p (∑ j ∈ s, b j * μ j) (fun x ↦ ∑ j ∈ s, b j * f j x) := by
  intro x y θ hθ₀ hθ₁
  have hs := Finset.sum_le_sum (fun j hj ↦
    mul_le_mul_of_nonneg_left (hf j hj x y θ hθ₀ hθ₁) (hb j hj))
  apply hs.trans_eq
  simp only [Finset.mul_sum, Finset.sum_div, Finset.sum_mul]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- At the Hilbert endpoint the coordinate Jensen formula is an equality. -/
theorem lpPower_two_jensen_identity (x y : ι → ℝ) (θ : ℝ) :
    lpPower 2 (fun i ↦ (1 - θ) * x i + θ * y i) =
      (1 - θ) * lpPower 2 x + θ * lpPower 2 y - θ * (1 - θ) * lpPower 2 (x - y) := by
  simp only [lpPower, Real.rpow_two, sq_abs, Pi.sub_apply, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A complete proof of the unit Jensen modulus for the endpoint `p = 2`.
The assertion for all real `p ≥ 2` additionally needs the scalar Clarkson
inequality from the paper. -/
theorem powerAtom_two_jensen (c : ι → ℝ) : LpPowerJensen 2 1 (powerAtom 2 c) := by
  intro x y θ _ _
  have hmix : (fun i ↦ (1 - θ) * x i + θ * y i - c i) =
      (fun i ↦ (1 - θ) * (x i - c i) + θ * (y i - c i)) := by
    ext i
    ring
  have hsub : (x - c) - (y - c) = x - y := by abel
  simp only [powerAtom, atomScale, sub_self, Real.rpow_zero]
  change 1 / 2 * lpPower 2 (fun i ↦ (1 - θ) * x i + θ * y i - c i) ≤ _
  rw [hmix, lpPower_two_jensen_identity]
  change 1 / 2 * ((1 - θ) * lpPower 2 (x - c) + θ * lpPower 2 (y - c) -
    θ * (1 - θ) * lpPower 2 ((x - c) - (y - c))) ≤ _
  rw [hsub]
  ring_nf
  exact le_rfl

/-- The unscaled fourth-power atom fails unit modulus, exactly at the
one-dimensional example used after the proof of Lemma 2.1. -/
theorem unscaled_fourth_power_not_unit_jensen :
    ¬ LpPowerJensen 4 1 (fun x : Fin 1 → ℝ ↦ lpPower 4 x / 4) := by
  intro h
  have hbad := h (fun _ ↦ 1) (fun _ ↦ -1) (1 / 2) (by norm_num) (by norm_num)
  norm_num [lpPower, Real.rpow_natCast] at hbad

end P31
