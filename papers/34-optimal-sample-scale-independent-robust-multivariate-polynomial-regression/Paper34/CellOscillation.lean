import Paper34.GridGeometry
import Paper34.ConstantCase
import Paper34.TrigBernsteinContract
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Complex.RealDeriv

/-!
# The angular path part of the cell-oscillation argument

The angular lift and all polynomial evaluations here use the source objects
from `Model`.  We prove differentiability, the actual arccosine-cell geometry,
the one-coordinate mean-value bound, and the finite-coordinate telescoping
argument.

The standard external input is exactly the general classical trigonometric
Bernstein theorem, `TrigBernstein.ClassicalTrigBernstein`, whose full statement
and source are in `TrigBernsteinContract`. We prove internally that each
angular slice belongs to the correct finite-degree Fourier span, using the
actual monomial support and the source coordinate-degree hypothesis. We then
derive `AngularDerivativeBound` and Lemma 5.1. No cell-oscillation conclusion
or bound on a particular source polynomial is an external assumption.
-/

namespace Paper34

noncomputable section

open Set
open scoped BigOperators

/-- The genuine angular lift `Q(θ) = q(cos θ₁, …, cos θₙ)`. -/
def angularEval {n d : ℕ} (q : PolynomialSpace n d) (theta : Point n) : ℝ :=
  polyEval q (fun k => Real.cos (theta k))

theorem angularEval_le_supNorm {n d : ℕ} (q : PolynomialSpace n d) (theta : Point n) :
    |angularEval q theta| ≤ supNorm q := by
  apply eval_le_supNorm q
  exact ⟨fun k => Real.neg_one_le_cos _, fun k => Real.cos_le_one _⟩

theorem angularEval_arccos {n d : ℕ} (q : PolynomialSpace n d)
    (x : Point n) (hx : x ∈ cube n) :
    angularEval q (fun k => Real.arccos (x k)) = polyEval q x := by
  unfold angularEval
  congr 1
  funext k
  exact Real.cos_arccos (hx.1 k) (hx.2 k)

/-- Every actual polynomial lift is differentiable on each angular line.
This is proved from polynomial induction and the derivative of cosine. -/
theorem differentiable_angularSlice {n d : ℕ} (q : PolynomialSpace n d)
    (theta : Point n) (k : Fin n) :
    Differentiable ℝ (fun t => angularEval q (Function.update theta k t)) := by
  have hpoly : ∀ p : MvPolynomial (Fin n) ℝ,
      Differentiable ℝ (fun t =>
        MvPolynomial.eval (fun i => Real.cos (Function.update theta k t i)) p) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
        simpa only [MvPolynomial.eval_C] using (differentiable_const a :
          Differentiable ℝ (fun _ : ℝ => a))
    | add p r hp hr =>
        simpa only [MvPolynomial.eval_add] using hp.add hr
    | mul_X p i hp =>
        simp only [MvPolynomial.eval_mul, MvPolynomial.eval_X]
        apply hp.mul
        by_cases hik : i = k
        · subst i
          simpa only [Function.update_self] using Real.differentiable_cos
        · simpa only [Function.update_of_ne hik] using
            (differentiable_const (Real.cos (theta i)) :
              Differentiable ℝ (fun _ : ℝ => Real.cos (theta i)))
  exact hpoly q.1

/-- The remaining sharp Bernstein input. It is a proposition, not an axiom
or a theorem asserted on the strength of the polynomial degree bound. -/
def AngularDerivativeBound {n d : ℕ} (q : PolynomialSpace n d) : Prop :=
  ∀ (theta : Point n) (k : Fin n) (t : ℝ),
    ‖deriv (fun s => angularEval q (Function.update theta k s)) t‖ ≤
      (d : ℝ) * supNorm q

/-- The actual one-variable mean-value step along an angular coordinate. -/
theorem angular_coordinate_change_bound {n d : ℕ} (q : PolynomialSpace n d)
    (hderiv : AngularDerivativeBound q) (theta : Point n) (k : Fin n) (s t : ℝ) :
    |angularEval q (Function.update theta k t) -
      angularEval q (Function.update theta k s)| ≤
      ((d : ℝ) * supNorm q) * |t - s| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun u (_ : u ∈ (univ : Set ℝ)) => differentiable_angularSlice q theta k u)
    (fun u (_ : u ∈ (univ : Set ℝ)) => hderiv theta k u)
    (convex_univ : Convex ℝ (univ : Set ℝ)) (mem_univ s) (mem_univ t)
  simpa only [Real.norm_eq_abs] using h

/-- Replace a finite collection of angular coordinates. -/
def replaceCoordinates {n : ℕ} (S : Finset (Fin n)) (theta phi : Point n) : Point n :=
  fun k => if k ∈ S then phi k else theta k

lemma replaceCoordinates_insert {n : ℕ} (S : Finset (Fin n)) (theta phi : Point n)
    (k : Fin n) :
    replaceCoordinates (insert k S) theta phi =
      Function.update (replaceCoordinates S theta phi) k (phi k) := by
  funext i
  by_cases hik : i = k
  · subst i
    simp [replaceCoordinates]
  · simp [replaceCoordinates, hik]

lemma replaceCoordinates_update_original {n : ℕ} (S : Finset (Fin n))
    (theta phi : Point n) (k : Fin n) (hk : k ∉ S) :
    Function.update (replaceCoordinates S theta phi) k (theta k) =
      replaceCoordinates S theta phi := by
  funext i
  by_cases hik : i = k
  · subst i
    simp [replaceCoordinates, hk]
  · simp only [Function.update_of_ne hik]

/-- The finite telescoping proof: no derivative bound is inferred here from
coordinate degree; it remains the explicitly named input `hderiv`. -/
theorem angular_finite_path_bound {n d : ℕ} (q : PolynomialSpace n d)
    (hderiv : AngularDerivativeBound q) (theta phi : Point n)
    (S : Finset (Fin n)) :
    |angularEval q (replaceCoordinates S theta phi) - angularEval q theta| ≤
      ((d : ℝ) * supNorm q) * ∑ k ∈ S, |phi k - theta k| := by
  induction S using Finset.induction_on with
  | empty =>
      have he : replaceCoordinates ∅ theta phi = theta := by
        funext i
        simp only [replaceCoordinates, Finset.notMem_empty, if_false]
      rw [he]
      simp
  | @insert k S hk ih =>
      have hstep := angular_coordinate_change_bound q hderiv
        (replaceCoordinates S theta phi) k (theta k) (phi k)
      rw [replaceCoordinates_update_original S theta phi k hk,
        ← replaceCoordinates_insert S theta phi k] at hstep
      calc
        _ ≤ |angularEval q (replaceCoordinates (insert k S) theta phi) -
              angularEval q (replaceCoordinates S theta phi)| +
            |angularEval q (replaceCoordinates S theta phi) - angularEval q theta| :=
          abs_sub_le _ _ _
        _ ≤ ((d : ℝ) * supNorm q) * |phi k - theta k| +
            ((d : ℝ) * supNorm q) * ∑ i ∈ S, |phi i - theta i| :=
          add_le_add hstep ih
        _ = _ := by rw [Finset.sum_insert hk, mul_add]

theorem angular_path_bound {n d : ℕ} (q : PolynomialSpace n d)
    (hderiv : AngularDerivativeBound q) (theta phi : Point n) :
    |angularEval q theta - angularEval q phi| ≤
      ((d : ℝ) * supNorm q) * ∑ k : Fin n, |theta k - phi k| := by
  have hu : replaceCoordinates Finset.univ phi theta = theta := by
    funext i
    simp only [replaceCoordinates, Finset.mem_univ, if_true]
  have h := angular_finite_path_bound q hderiv phi theta Finset.univ
  rw [hu] at h
  exact h

/-- Arccosine sends a point of an actual closed Chebyshev cell back to its
prescribed angular cell, including both endpoints. -/
theorem arccos_mem_angularCell {n m : ℕ} (hm : 0 < m) (j : CellIndex n m)
    (x : Point n) (hx : x ∈ closedCell j) (k : Fin n) :
    Real.arccos (x k) ∈ Icc ((j k : ℕ) * Real.pi / m)
      (((j k : ℕ) + (1 : ℝ)) * Real.pi / m) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hj : (j k : ℝ) + 1 ≤ m := by
    exact_mod_cast (Nat.succ_le_iff.mpr (j k).isLt)
  have hl0 : (0 : ℝ) ≤ (j k : ℕ) * Real.pi / m := by positivity
  have hu0 : (0 : ℝ) ≤ ((j k : ℕ) + (1 : ℝ)) * Real.pi / m := by positivity
  have huPi : ((j k : ℕ) + (1 : ℝ)) * Real.pi / m ≤ Real.pi := by
    apply (div_le_iff₀ hm').2
    nlinarith [mul_le_mul_of_nonneg_right hj Real.pi_pos.le]
  have hlPi : (j k : ℕ) * Real.pi / m ≤ Real.pi := by
    apply (div_le_iff₀ hm').2
    nlinarith [mul_le_mul_of_nonneg_right hj Real.pi_pos.le]
  constructor
  · have h := Real.arccos_le_arccos (hx.2 k)
    simpa only [cellUpper, Real.arccos_cos hl0 hlPi] using h
  · have h := Real.arccos_le_arccos (hx.1 k)
    simpa only [cellLower, Real.arccos_cos hu0 huPi] using h

theorem arccos_cell_coordinate_distance {n m : ℕ} (hm : 0 < m)
    (j : CellIndex n m) (x z : Point n) (hx : x ∈ closedCell j)
    (hz : z ∈ closedCell j) (k : Fin n) :
    |Real.arccos (x k) - Real.arccos (z k)| ≤ Real.pi / m := by
  have hxa := arccos_mem_angularCell hm j x hx k
  have hza := arccos_mem_angularCell hm j z hz k
  have hwidth : (((j k : ℕ) + (1 : ℝ)) * Real.pi / m) -
      ((j k : ℕ) * Real.pi / m) = Real.pi / m := by ring
  exact abs_le.mpr ⟨by linarith [hxa.1, hza.2], by linarith [hxa.2, hza.1]⟩

/-- The pointwise conclusion of Lemma 5.1, conditional on the still-missing
sharp Bernstein derivative theorem. -/
theorem cell_difference_of_angularDerivativeBound {n d m : ℕ}
    (q : PolynomialSpace n d) (hm : 0 < m) (hderiv : AngularDerivativeBound q)
    (j : CellIndex n m) (x z : Point n) (hx : x ∈ closedCell j)
    (hz : z ∈ closedCell j) :
    |polyEval q x - polyEval q z| ≤
      (Real.pi * n * d / m) * supNorm q := by
  have hpath := angular_path_bound q hderiv
    (fun k => Real.arccos (x k)) (fun k => Real.arccos (z k))
  rw [angularEval_arccos q x (closedCell_subset_cube j hx),
    angularEval_arccos q z (closedCell_subset_cube j hz)] at hpath
  have hsum : (∑ k : Fin n, |Real.arccos (x k) - Real.arccos (z k)|) ≤
      (n : ℝ) * (Real.pi / m) := by
    calc
      _ ≤ ∑ _k : Fin n, Real.pi / m :=
        Finset.sum_le_sum (fun k _ => arccos_cell_coordinate_distance hm j x z hx hz k)
      _ = _ := by simp [nsmul_eq_mul]
  calc
    _ ≤ ((d : ℝ) * supNorm q) * ∑ k : Fin n,
          |Real.arccos (x k) - Real.arccos (z k)| := hpath
    _ ≤ ((d : ℝ) * supNorm q) * ((n : ℝ) * (Real.pi / m)) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg (Nat.cast_nonneg _) (supNorm_nonneg q))
    _ = _ := by ring

/-- The actual supremum of differences over two points of the actual cell. -/
def cellOscillation {n d m : ℕ} (q : PolynomialSpace n d) (j : CellIndex n m) : ℝ :=
  sSup ((fun xz : Point n × Point n => |polyEval q xz.1 - polyEval q xz.2|) ''
    (closedCell j ×ˢ closedCell j))

/-- The supremum formulation, retaining the explicit unresolved Bernstein input. -/
theorem cellOscillation_of_angularDerivativeBound {n d m : ℕ}
    (q : PolynomialSpace n d) (hm : 0 < m) (hderiv : AngularDerivativeBound q)
    (j : CellIndex n m) :
    cellOscillation q j ≤ (Real.pi * n * d / m) * supNorm q := by
  unfold cellOscillation
  apply csSup_le
  · exact ((closedCell_nonempty hm j).prod (closedCell_nonempty hm j)).image _
  · rintro _ ⟨⟨x, z⟩, ⟨hx, hz⟩, rfl⟩
    exact cell_difference_of_angularDerivativeBound q hm hderiv j x z hx hz

/-- A monomial on an angular coordinate line is a scalar multiple of a
single cosine power; the other coordinates contribute only to the scalar. -/
theorem angular_monomial_factor {n : ℕ} (theta : Point n) (k : Fin n)
    (s : Fin n →₀ ℕ) (a : ℝ) :
    (fun t : ℝ => ((a * ∏ i : Fin n,
      Real.cos (Function.update theta k t i) ^ s i : ℝ) : ℂ)) =
    ((a : ℂ) * ∏ i ∈ (Finset.univ : Finset (Fin n)).erase k,
      (Real.cos (theta i) : ℂ) ^ s i) •
        (fun t : ℝ => (Real.cos t : ℂ) ^ s k) := by
  funext t
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  rw [← Finset.prod_erase_mul (Finset.univ : Finset (Fin n))
    (fun i => Complex.cos (Function.update theta k t i : ℂ) ^ s i) (Finset.mem_univ k)]
  rw [Function.update_self]
  have hp : (∏ i ∈ (Finset.univ : Finset (Fin n)).erase k,
      Complex.cos (Function.update theta k t i : ℂ) ^ s i) =
      ∏ i ∈ (Finset.univ : Finset (Fin n)).erase k,
        Complex.cos (theta i : ℂ) ^ s i := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]
  rw [hp]
  ring

/-- The paper's own degree bridge: every genuine bounded-coordinate-degree
multivariate polynomial has a degree-at-most-`d` trigonometric lift in each
angular coordinate. This proof uses no Bernstein input. -/
theorem angularSlice_mem_trigPolynomialSpace {n d : ℕ} (q : PolynomialSpace n d)
    (theta : Point n) (k : Fin n) :
    (fun t : ℝ => (angularEval q (Function.update theta k t) : ℂ)) ∈
      TrigBernstein.trigPolynomialSpace d := by
  have heval : (fun t : ℝ => (angularEval q (Function.update theta k t) : ℂ)) =
      ∑ s ∈ q.1.support, (fun t : ℝ =>
        ((q.1.coeff s * ∏ i : Fin n,
          Real.cos (Function.update theta k t i) ^ s i : ℝ) : ℂ)) := by
    funext t
    simp only [Finset.sum_apply, angularEval, polyEval, MvPolynomial.eval_eq']
    push_cast
    rfl
  rw [heval]
  apply Submodule.sum_mem
  intro s hs
  rw [angular_monomial_factor]
  apply Submodule.smul_mem
  exact TrigBernstein.trigPolynomialSpace_mono
    ((MvPolynomial.mem_restrictDegree (Fin n) q.1 d).mp q.2 s hs k)
    (TrigBernstein.cos_pow_mem (s k))

/-- The classical external theorem is used here, after the source polynomial
has been shown to satisfy its genuine Fourier-degree hypothesis. Degree zero
is proved internally from the source polynomial's constant representation. -/
theorem angularDerivativeBound_of_classicalTrigBernstein
    (hBernstein : TrigBernstein.ClassicalTrigBernstein)
    {n d : ℕ} (q : PolynomialSpace n d) : AngularDerivativeBound q := by
  by_cases hd : d = 0
  · subst d
    intro theta k t
    have hc : (fun s => angularEval q (Function.update theta k s)) =
        (fun _ : ℝ => q.1.coeff 0) := by
      funext s
      exact degree_zero_eval_constant q _
    rw [hc]
    simp
  · intro theta k t
    let T : ℝ → ℂ := fun s => (angularEval q (Function.update theta k s) : ℂ)
    have hT := angularSlice_mem_trigPolynomialSpace q theta k
    have hnorm : ∀ s : ℝ, ‖T s‖ ≤ supNorm q := by
      intro s
      simpa only [T, Complex.norm_real, Real.norm_eq_abs] using
        angularEval_le_supNorm q (Function.update theta k s)
    have hb := hBernstein d (Nat.one_le_iff_ne_zero.mpr hd) T hT
      (supNorm q) (supNorm_nonneg q) hnorm t
    have hderiv : deriv T t =
        Complex.ofReal (deriv (fun s : ℝ => angularEval q (Function.update theta k s)) t) :=
      ((differentiable_angularSlice q theta k t).hasDerivAt.ofReal_comp).deriv
    rw [hderiv] at hb
    simpa only [Complex.norm_real] using hb

/-- Lemma 5.1, pointwise form. The only external mathematical input is the
fully general published classical trigonometric Bernstein theorem. -/
theorem lemma_5_1_pointwise
    (hBernstein : TrigBernstein.ClassicalTrigBernstein)
    {n d m : ℕ} (q : PolynomialSpace n d) (hm : 0 < m)
    (j : CellIndex n m) (x z : Point n) (hx : x ∈ closedCell j)
    (hz : z ∈ closedCell j) :
    |polyEval q x - polyEval q z| ≤
      (Real.pi * n * d / m) * supNorm q :=
  cell_difference_of_angularDerivativeBound q hm
    (angularDerivativeBound_of_classicalTrigBernstein hBernstein q) j x z hx hz

/-- Lemma 5.1, exactly the supremum-over-two-cell-points formulation (5.1). -/
theorem lemma_5_1
    (hBernstein : TrigBernstein.ClassicalTrigBernstein)
    {n d m : ℕ} (q : PolynomialSpace n d) (hm : 0 < m) (j : CellIndex n m) :
    cellOscillation q j ≤ (Real.pi * n * d / m) * supNorm q :=
  cellOscillation_of_angularDerivativeBound q hm
    (angularDerivativeBound_of_classicalTrigBernstein hBernstein q) j

end

end Paper34
