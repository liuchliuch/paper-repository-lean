import Paper25.CircuitRecipe
import Paper25.PhaseEstCore
import Paper25.BlockEncoding
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Basic

/-!
# Explicit elementary-function inputs and the paper's rotation arithmetic

The external inputs below are specializations of Emil Jeřábek, *Elementary
analytic functions in VTC^0*, arXiv:2206.12164v3 (13 March 2023):
https://arxiv.org/pdf/2206.12164v3 .

* Lemma 3.46(ii), p. 31: a **multiplicative** rational approximation to sqrt on
  positive rational arguments. It is not asserted to be additive on an
  unbounded domain.
* Proposition 5.8, p. 45, with Definition 5.4 and Table 1: additive approximation
  to the real principal arccos on rational arguments in [-1,1].
* Proposition 5.11 and Table 2, pp. 46-47: additive sin/cos approximation. The
  real-input specialization has Im z = 0, so the unary bound parameter is 0.
* The approximation convention on pp. 9-10 is error <= 2^(-n), with unary n;
  rational numerators/denominators are binary (p. 6). The introduction states
  that TC^0 means DLOGTIME-uniform TC^0 and is contained in logarithmic space.

We expose those published classical results as **explicit inputs**, not Lean
axioms or existence theorems. Their finite-transducer conclusions use the
project's `LogspaceComputes`, raw binary fraction encodings, and unary bit
precision. Restriction to the real part of a complex rational output cannot
increase additive error. Encoding/recoding and FL closure belong to the
external classical transport, not to a hidden quantum workspace.

No external field states a label-filter rotation family, quantum compilation,
or the P25 simulator. The rational quotient, clipping, analytic error
propagation and rotation semantics below are proved here.
-/

noncomputable section
set_option maxHeartbeats 400000

namespace Paper25.OperationalModel

/-- A bit precision n means additive tolerance 2^(-n). -/
def bitError (n : ℕ) : ℝ := 1 / (2 : ℝ) ^ n

lemma bitError_pos (n : ℕ) : 0 < bitError n := by unfold bitError; positivity

/-- A mathematical reference query. Its canonical `ℚ` argument is only used
for the mathematical helper `eval` below; no machine output is asserted for
this canonical representation. Actual numerical interfaces use raw fractions. -/
structure RationalQuery (D : ℚ → Prop) where
  argument : ℚ
  precision : ℕ
  admissible : D argument

/-- The actual published numerical query: an unreduced signed numerator and
positive denominator, with a unary bit precision. -/
structure RepresentedQuery (D : ℚ → Prop) where
  argument : RationalRep
  precision : ℕ
  admissible : D argument.value

def RepresentedQuery.encode {D : ℚ → Prop} (q : RepresentedQuery D) : Input :=
  q.argument.encode ++ encodeNat q.precision

/-- Selecting a representation is a mathematical convenience, not a claim
that normalization or canonical encoding is computable in TC^0 or FL. -/
def RationalQuery.represented {D : ℚ → Prop} (q : RationalQuery D) : RepresentedQuery D :=
  ⟨RationalRep.ofRat q.argument, q.precision, by simpa only [RationalRep.ofRat_value] using q.admissible⟩

/-- A published additive approximation with raw query and raw output semantics.
The output may depend on the fraction representation; no representation-
independence or canonical-normalization assertion is hidden in this input. -/
structure RationalAdditiveApproximation (D : ℚ → Prop) (f : ℝ → ℝ) where
  representedValue : RepresentedQuery D → RationalRep
  computes : LogspaceComputes RepresentedQuery.encode (fun q => (representedValue q).encode)
  represented_error : ∀ q, |((representedValue q).value : ℝ) - f q.argument.value| ≤ bitError q.precision

def RationalAdditiveApproximation.value {D : ℚ → Prop} {f : ℝ → ℝ}
    (A : RationalAdditiveApproximation D f) (q : RationalQuery D) : ℚ :=
  (A.representedValue q.represented).value

lemma RationalAdditiveApproximation.error {D : ℚ → Prop} {f : ℝ → ℝ}
    (A : RationalAdditiveApproximation D f) (q : RationalQuery D) :
    |(A.value q : ℝ) - f q.argument| ≤ bitError q.precision := by
  simpa only [RationalAdditiveApproximation.value, RationalQuery.represented,
    RationalRep.ofRat_value] using A.represented_error q.represented

def RationalAdditiveApproximation.eval {D : ℚ → Prop} {f : ℝ → ℝ}
    (A : RationalAdditiveApproximation D f) (q : ℚ) (n : ℕ) (hq : D q) : ℚ :=
  A.value ⟨q, n, hq⟩

lemma RationalAdditiveApproximation.eval_error {D : ℚ → Prop} {f : ℝ → ℝ}
    (A : RationalAdditiveApproximation D f) (q : ℚ) (n : ℕ) (hq : D q) :
    |(A.eval q n hq : ℝ) - f q| ≤ bitError n := A.error _

/-- The positive-rational square-root input retains the source's relative
error. Both input and output are unreduced rational representations. -/
structure RationalSqrtApproximation where
  representedValue : RepresentedQuery (fun q => 0 < q) → RationalRep
  computes : LogspaceComputes RepresentedQuery.encode (fun q => (representedValue q).encode)
  represented_error : ∀ q, |((representedValue q).value : ℝ) - Real.sqrt q.argument.value| ≤
    bitError q.precision * Real.sqrt q.argument.value

def RationalSqrtApproximation.value (A : RationalSqrtApproximation)
    (q : RationalQuery (fun q => 0 < q)) : ℚ := (A.representedValue q.represented).value

lemma RationalSqrtApproximation.error (A : RationalSqrtApproximation)
    (q : RationalQuery (fun q => 0 < q)) :
    |(A.value q : ℝ) - Real.sqrt q.argument| ≤ bitError q.precision * Real.sqrt q.argument := by
  simpa only [RationalSqrtApproximation.value, RationalQuery.represented,
    RationalRep.ofRat_value] using A.represented_error q.represented

/-- Exactly the elementary numerical external inputs used here. This structure
asserts no existence theorem by itself. All machine claims concern raw fraction
queries and raw fraction outputs; canonical `ℚ` helpers are mathematical only. -/
structure ElementaryAnalyticInputs where
  sqrt : RationalSqrtApproximation
  arccos : RationalAdditiveApproximation (fun q => |q| ≤ 1) Real.arccos
  sin : RationalAdditiveApproximation (fun _ => True) Real.sin
  cos : RationalAdditiveApproximation (fun _ => True) Real.cos

/-- On arguments at most one the published relative sqrt guarantee implies the
additive guarantee needed for rotation matrix entries. -/
lemma RationalSqrtApproximation.additive_error (A : RationalSqrtApproximation)
    (q : RationalQuery (fun q => 0 < q)) (hq : q.argument ≤ 1) :
    |(A.value q : ℝ) - Real.sqrt q.argument| ≤ bitError q.precision := by
  have hle : Real.sqrt (q.argument : ℝ) ≤ 1 := by
    apply Real.sqrt_le_one.mpr
    exact_mod_cast hq
  exact (A.error q).trans (by nlinarith [bitError_pos q.precision])

/-- The exact rational filter quotient; its denominator is nonzero for δ>0. -/
def rationalFilter (δ t : ℚ) : ℚ := δ * t / (t ^ 2 + δ ^ 2)

lemma rationalFilter_cast (δ t : ℚ) :
    (rationalFilter δ t : ℝ) = Paper25.filterFn δ t := by
  simp only [rationalFilter, Paper25.filterFn, Rat.cast_div, Rat.cast_mul,
    Rat.cast_add, Rat.cast_pow]

/-- Clip an approximate amplitude to the interval used by the paper. -/
def rationalClipHalf (q : ℚ) : ℚ := max (-(1 / 2)) (min (1 / 2) q)

lemma rationalClipHalf_mem (q : ℚ) : |rationalClipHalf q| ≤ 1 / 2 := by
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

lemma rationalClipHalf_cast (q : ℚ) :
    (rationalClipHalf q : ℝ) = max (-(1 / 2)) (min (1 / 2) (q : ℝ)) := by
  simp [rationalClipHalf, Rat.cast_max, Rat.cast_min]

/-- Clipping cannot increase error relative to a true amplitude in [-1/2,1/2]. -/
lemma rationalClipHalf_error (q : ℚ) (a : ℝ) (ha : |a| ≤ 1 / 2) :
    |(rationalClipHalf q : ℝ) - a| ≤ |(q : ℝ) - a| := by
  have ha' := abs_le.mp ha
  have hfix : max (-(1 / 2) : ℝ) (min (1 / 2) a) = a := by
    rw [min_eq_right ha'.2, max_eq_right ha'.1]
  rw [rationalClipHalf_cast]
  have hmax := abs_max_sub_max_le_max (-(1 / 2) : ℝ) (min (1 / 2) (q : ℝ))
    (-(1 / 2)) (min (1 / 2) a)
  have hmin := abs_min_sub_min_le_max (1 / 2 : ℝ) (q : ℝ) (1 / 2) a
  have hmax' : |max (-(1 / 2)) (min (1 / 2) (q : ℝ)) - max (-(1 / 2)) (min (1 / 2) a)|
      ≤ |min (1 / 2) (q : ℝ) - min (1 / 2) a| := by
    simpa only [sub_self, abs_zero,
      max_eq_right (abs_nonneg (min (1 / 2) (q : ℝ) - min (1 / 2) a))] using hmax
  have hmin' : |min (1 / 2) (q : ℝ) - min (1 / 2) a| ≤ |(q : ℝ) - a| := by
    simpa only [sub_self, abs_zero, max_eq_right (abs_nonneg ((q : ℝ) - a))] using hmin
  calc
    _ = |max (-(1 / 2)) (min (1 / 2) (q : ℝ)) - max (-(1 / 2)) (min (1 / 2) a)| := by rw [hfix]
    _ ≤ |min (1 / 2) (q : ℝ) - min (1 / 2) a| := hmax'
    _ ≤ |(q : ℝ) - a| := hmin'

end Paper25.OperationalModel

namespace Paper25

/-- Actual derivative of the scalar rational filter. -/
lemma hasDerivAt_filterFn (δ t : ℝ) (hδ : δ ≠ 0) :
    HasDerivAt (filterFn δ) (δ * (δ ^ 2 - t ^ 2) / (t ^ 2 + δ ^ 2) ^ 2) t := by
  have hnum : HasDerivAt (fun x : ℝ => δ * x) δ t := by
    simpa using (hasDerivAt_id t).const_mul δ
  have hden : HasDerivAt (fun x : ℝ => x ^ 2 + δ ^ 2) (2 * t) t := by
    simpa [pow_two, two_mul] using ((hasDerivAt_id t).pow 2).add_const (δ ^ 2)
  have hne : t ^ 2 + δ ^ 2 ≠ 0 := by nlinarith [sq_pos_of_ne_zero hδ, sq_nonneg t]
  have h := hnum.div hden hne
  have heq : δ * (t ^ 2 + δ ^ 2) - δ * t * (2 * t) = δ * (δ ^ 2 - t ^ 2) := by ring
  rw [heq] at h
  exact h

/-- The quotient amplification from Appendix A.3, on the entire real line. -/
lemma filterFn_abs_sub_le (δ t u : ℝ) (hδ : 0 < δ) :
    |filterFn δ t - filterFn δ u| ≤ |t - u| / δ := by
  have hdiff : ∀ x : ℝ, DifferentiableAt ℝ (filterFn δ) x :=
    fun x => (hasDerivAt_filterFn δ x hδ.ne').differentiableAt
  have hbound : ∀ x : ℝ, ‖deriv (filterFn δ) x‖ ≤ 1 / δ := by
    intro x
    rw [(hasDerivAt_filterFn δ x hδ.ne').deriv, Real.norm_eq_abs]
    exact filter_deriv_bound δ x hδ
  have h := @Convex.norm_image_sub_le_of_norm_deriv_le ℝ ℝ _ _ _
    (filterFn δ) Set.univ t u (1 / δ) (fun x _ => hdiff x) (fun x _ => hbound x)
    convex_univ (by trivial) (by trivial)
  simpa [Real.norm_eq_abs, abs_sub_comm, div_eq_mul_inv, mul_comm] using h

/-- Elementary real sine stability. -/
lemma sin_abs_sub_le (x y : ℝ) : |Real.sin x - Real.sin y| ≤ |x - y| := by
  have h := @Convex.norm_image_sub_le_of_norm_deriv_le ℝ ℝ _ _ _
    Real.sin Set.univ x y 1 (fun t _ => Real.differentiable_sin.differentiableAt)
    (fun t _ => by rw [Real.deriv_sin, Real.norm_eq_abs]; exact Real.abs_cos_le_one t)
    convex_univ (by trivial) (by trivial)
  simpa [Real.norm_eq_abs, abs_sub_comm] using h

/-- Elementary real cosine stability. -/
lemma cos_abs_sub_le (x y : ℝ) : |Real.cos x - Real.cos y| ≤ |x - y| := by
  have h := @Convex.norm_image_sub_le_of_norm_deriv_le ℝ ℝ _ _ _
    Real.cos Set.univ x y 1 (fun t _ => Real.differentiable_cos.differentiableAt)
    (fun t _ => by rw [Real.deriv_cos, Real.norm_eq_abs, abs_neg]; exact Real.abs_sin_le_one t)
    convex_univ (by trivial) (by trivial)
  simpa [Real.norm_eq_abs, abs_sub_comm] using h

/-- The precise inverse-cosine Lipschitz constant on the clipped interval. -/
lemma arccos_abs_sub_le_half (x y : ℝ) (hx : |x| ≤ 1 / 2) (hy : |y| ≤ 1 / 2) :
    |Real.arccos x - Real.arccos y| ≤ (2 / Real.sqrt 3) * |x - y| := by
  have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hdiff : ∀ t ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2), DifferentiableAt ℝ Real.arccos t := by
    intro t ht
    exact (Real.hasDerivAt_arccos (by linarith [ht.1]) (by linarith [ht.2])).differentiableAt
  have hbound : ∀ t ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2),
      ‖deriv Real.arccos t‖ ≤ 2 / Real.sqrt 3 := by
    intro t ht
    have hden : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
    have hs : Real.sqrt 3 / 2 ≤ Real.sqrt (1 - t ^ 2) := by
      have hsq := Real.sq_sqrt hden.le
      nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg (1 - t ^ 2), ht.1, ht.2]
    rw [(Real.hasDerivAt_arccos (by linarith [ht.1]) (by linarith [ht.2])).deriv,
      Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity : 0 < 1 / Real.sqrt (1 - t ^ 2))]
    calc
      _ ≤ 1 / (Real.sqrt 3 / 2) := one_div_le_one_div_of_le (by positivity) hs
      _ = 2 / Real.sqrt 3 := by field_simp
  have h := @Convex.norm_image_sub_le_of_norm_deriv_le ℝ ℝ _ _ _
    Real.arccos (Set.Icc (-(1 / 2) : ℝ) (1 / 2)) x y (2 / Real.sqrt 3) hdiff hbound
    (convex_Icc _ _) (abs_le.mp hx) (abs_le.mp hy)
  simpa [Real.norm_eq_abs, abs_sub_comm] using h

/-- The amplitude rotation is exactly R_y(2 arccos a), including the positive
square-root off-diagonal entries and all scalar phases. -/
lemma amplitudeRotation_eq_arccos (a : ℝ) (ha : |a| ≤ 1) :
    amplitudeRotation a = realRotation (Real.cos (Real.arccos a)) (Real.sin (Real.arccos a)) := by
  rw [Real.cos_arccos (abs_le.mp ha).1 (abs_le.mp ha).2, Real.sin_arccos]
  rfl

section RotationError

open scoped Matrix.Norms.L2Operator

/-- A real Ry angle, so the entries use the half angle. -/
def angleRotation (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  realRotation (Real.cos (θ / 2)) (Real.sin (θ / 2))

lemma angleRotation_apply (θ : ℝ) (i j : Fin 2) :
    angleRotation θ i j = if i = j then (Real.cos (θ / 2) : ℂ)
      else if i = 0 then -(Real.sin (θ / 2) : ℂ) else (Real.sin (θ / 2) : ℂ) := by
  fin_cases i <;> fin_cases j <;> norm_num [angleRotation, realRotation, Matrix.of_apply]

lemma realRotation_sub_decomposition (a b c d : ℝ) :
    realRotation a b - realRotation c d =
      ((a - c : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      ((b - d : ℝ) : ℂ) • realRotation 0 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [realRotation, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply, Matrix.of_apply] <;> push_cast <;> ring

lemma realRotation_sub_norm_le (a b c d : ℝ) :
    ‖realRotation a b - realRotation c d‖ ≤ |a - c| + |b - d| := by
  have hJ : ‖realRotation 0 1‖ = 1 :=
    CStarRing.norm_of_mem_unitary (realRotation_unitary 0 1 (by norm_num))
  rw [realRotation_sub_decomposition]
  apply (norm_add_le _ _).trans
  simp only [norm_smul, hJ, norm_one, mul_one, Complex.norm_real, Real.norm_eq_abs]
  exact le_rfl

/-- A uniform operator-norm perturbation bound for the actual one-qubit Ry
matrix. This bound retains the global phase of the real rotation. -/
lemma angleRotation_norm_sub_le (θ φ : ℝ) :
    ‖angleRotation θ - angleRotation φ‖ ≤ |θ - φ| := by
  calc
    _ ≤ |Real.cos (θ / 2) - Real.cos (φ / 2)| +
        |Real.sin (θ / 2) - Real.sin (φ / 2)| :=
      realRotation_sub_norm_le _ _ _ _
    _ ≤ |θ / 2 - φ / 2| + |θ / 2 - φ / 2| :=
      add_le_add (cos_abs_sub_le _ _) (sin_abs_sub_le _ _)
    _ = |θ - φ| := by
      rw [show θ / 2 - φ / 2 = (θ - φ) / 2 by ring, abs_div]
      norm_num

lemma angleRotation_arccos (a : ℝ) (ha : |a| ≤ 1) :
    angleRotation (2 * Real.arccos a) = amplitudeRotation a := by
  rw [amplitudeRotation_eq_arccos a ha]
  unfold angleRotation
  congr 1 <;> congr 1 <;> ring

lemma angleRotation_amplitude_error (θ a : ℝ) (ha : |a| ≤ 1) :
    ‖angleRotation θ - amplitudeRotation a‖ ≤ |θ - 2 * Real.arccos a| := by
  rw [← angleRotation_arccos a ha]
  exact angleRotation_norm_sub_le _ _

end RotationError

end Paper25

namespace Paper25.OperationalModel

/-- A rational approximation to pi from a single elementary arccos query. -/
def rationalPi (E : ElementaryAnalyticInputs) (n : ℕ) : ℚ :=
  2 * E.arccos.eval 0 n (by norm_num)

lemma rationalPi_error (E : ElementaryAnalyticInputs) (n : ℕ) :
    |(rationalPi E n : ℝ) - Real.pi| ≤ 2 * bitError n := by
  have h := E.arccos.eval_error 0 n (by norm_num)
  simp only [Rat.cast_zero, Real.arccos_zero] at h
  have heq : |(rationalPi E n : ℝ) - Real.pi| =
      2 * |(E.arccos.eval 0 n (by norm_num) : ℝ) - Real.pi / 2| := by
    unfold rationalPi
    push_cast
    rw [show 2 * (E.arccos.eval 0 n (by norm_num) : ℝ) - Real.pi =
      2 * ((E.arccos.eval 0 n (by norm_num) : ℝ) - Real.pi / 2) by ring,
      abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [heq]
  exact mul_le_mul_of_nonneg_left h (by norm_num)

/-- The actual rational phase query for label j/M. -/
def rationalLabelPhase (E : ElementaryAnalyticInputs) (M j : ℚ) (n : ℕ) : ℚ :=
  2 * rationalPi E n * j / M

lemma rationalLabelPhase_error (E : ElementaryAnalyticInputs) (M j : ℚ) (n : ℕ)
    (hM : 0 < M) (hj : 0 ≤ j) (hjM : j ≤ M) :
    |(rationalLabelPhase E M j n : ℝ) - 2 * Real.pi * (j : ℝ) / (M : ℝ)|
      ≤ 4 * bitError n := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hjR : (0 : ℝ) ≤ j := by exact_mod_cast hj
  have hratio : (j : ℝ) / (M : ℝ) ≤ 1 := by
    rw [div_le_one hMR]
    exact_mod_cast hjM
  have hrat0 : 0 ≤ (j : ℝ) / (M : ℝ) := by positivity
  have heq : |(rationalLabelPhase E M j n : ℝ) - 2 * Real.pi * (j : ℝ) / (M : ℝ)|
      = (2 * |(rationalPi E n : ℝ) - Real.pi|) * ((j : ℝ) / (M : ℝ)) := by
    unfold rationalLabelPhase
    push_cast
    rw [show 2 * (rationalPi E n : ℝ) * j / M - 2 * Real.pi * j / M =
      2 * ((rationalPi E n : ℝ) - Real.pi) * ((j : ℝ) / M) by ring,
      abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg hrat0]
  rw [heq]
  calc
    _ ≤ (2 * (2 * bitError n)) * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left (rationalPi_error E n) (by norm_num))
        hratio hrat0 (by linarith [bitError_pos n])
    _ = 4 * bitError n := by ring

/-- A mathematical reference amplitude computed from an approximate cosine.
The elementary external input supplies only that cosine, not this quotient. -/
def approximatedFilterAmplitude (E : ElementaryAnalyticInputs)
    (δ θ : ℚ) (n : ℕ) : ℚ :=
  rationalClipHalf (rationalFilter δ (E.cos.eval θ n trivial))

lemma approximatedFilterAmplitude_mem (E : ElementaryAnalyticInputs)
    (δ θ : ℚ) (n : ℕ) : |approximatedFilterAmplitude E δ θ n| ≤ 1 / 2 :=
  rationalClipHalf_mem _

/-- A mathematical reference angle; actual raw numerical outputs are compiled in `RepresentedAnalytic`. -/
def approximatedFilterAngle (E : ElementaryAnalyticInputs)
    (δ θ : ℚ) (n k : ℕ) : ℚ :=
  2 * E.arccos.eval (approximatedFilterAmplitude E δ θ n) k
    (by have h := approximatedFilterAmplitude_mem E δ θ n; linarith)

/-- The cosine input may itself approximate an irrational ideal phase, e.g. a
Fourier phase involving pi. Both error contributions remain explicit. -/
lemma approximatedFilterAmplitude_error (E : ElementaryAnalyticInputs)
    (δ θ : ℚ) (n : ℕ) (φ η : ℝ) (hδ : 0 < δ)
    (hθ : |(θ : ℝ) - φ| ≤ η) :
    |(approximatedFilterAmplitude E δ θ n : ℝ) - Paper25.filterG δ φ|
      ≤ (bitError n + η) / (δ : ℝ) := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hcos := E.cos.eval_error θ n trivial
  have hinput := (abs_sub_le (E.cos.eval θ n trivial : ℝ) (Real.cos θ) (Real.cos φ)).trans
    (add_le_add hcos ((Paper25.cos_abs_sub_le θ φ).trans hθ))
  have hclip := rationalClipHalf_error
    (rationalFilter δ (E.cos.eval θ n trivial)) (Paper25.filterG δ φ)
    (Paper25.filterG_range_bound δ φ hδR)
  rw [rationalFilter_cast] at hclip
  have hfilter := Paper25.filterFn_abs_sub_le (δ : ℝ) (E.cos.eval θ n trivial) (Real.cos φ) hδR
  exact hclip.trans (hfilter.trans (div_le_div_of_nonneg_right hinput hδR.le))

open scoped Matrix.Norms.L2Operator

/-- The paper's own rational numerical pipeline has a matrix-error bound.
Only the four elementary real approximation inputs are external. -/
theorem approximatedFilterAngle_matrix_error (E : ElementaryAnalyticInputs)
    (δ θ : ℚ) (n k : ℕ) (φ η : ℝ) (hδ : 0 < δ)
    (hθ : |(θ : ℝ) - φ| ≤ η) :
    ‖Paper25.angleRotation (approximatedFilterAngle E δ θ n k) -
      Paper25.amplitudeRotation (Paper25.filterG δ φ)‖
      ≤ 2 * bitError k + (4 / Real.sqrt 3) * ((bitError n + η) / (δ : ℝ)) := by
  let u : ℚ := approximatedFilterAmplitude E δ θ n
  let a : ℝ := Paper25.filterG δ φ
  have hu : |(u : ℝ)| ≤ 1 / 2 := by
    have hcast : ((|u| : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) :=
      Rat.cast_mono (approximatedFilterAmplitude_mem E δ θ n)
    simpa only [Rat.cast_abs, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hcast
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  have ha : |a| ≤ 1 / 2 := Paper25.filterG_range_bound δ φ hδR
  have hu1 : |u| ≤ 1 := by have h := approximatedFilterAmplitude_mem E δ θ n; dsimp [u]; linarith
  have hacos := E.arccos.eval_error u k hu1
  have hstable := Paper25.arccos_abs_sub_le_half (u : ℝ) a hu ha
  have hamp := approximatedFilterAmplitude_error E δ θ n φ η hδ hθ
  have hangle : |(approximatedFilterAngle E δ θ n k : ℝ) - 2 * Real.arccos a|
      ≤ 2 * bitError k + (4 / Real.sqrt 3) * ((bitError n + η) / (δ : ℝ)) := by
    have htriangle := (abs_sub_le (E.arccos.eval u k hu1 : ℝ) (Real.arccos u)
      (Real.arccos a)).trans (add_le_add hacos hstable)
    have hmul := mul_le_mul_of_nonneg_left hamp (by positivity : 0 ≤ 2 / Real.sqrt 3)
    have hid : |(approximatedFilterAngle E δ θ n k : ℝ) - 2 * Real.arccos a| =
        2 * |(E.arccos.eval u k hu1 : ℝ) - Real.arccos a| := by
      unfold approximatedFilterAngle
      push_cast
      rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [hid]
    change (2 / Real.sqrt 3) * |(u : ℝ) - a| ≤ _ at hmul
    have hsum := htriangle.trans (add_le_add_left hmul (bitError k))
    calc
      _ ≤ 2 * (bitError k + (2 / Real.sqrt 3) * ((bitError n + η) / (δ : ℝ))) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = _ := by ring
  exact (Paper25.angleRotation_amplitude_error _ a (by linarith)).trans hangle

lemma rationalClipHalf_eq_if (q : ℚ) : rationalClipHalf q =
    if q < -(1 / 2) then -(1 / 2) else if 1 / 2 < q then 1 / 2 else q := by
  by_cases hlo : q < -(1 / 2)
  · rw [if_pos hlo]
    simp only [rationalClipHalf, min_eq_right (by linarith : q ≤ 1 / 2), max_eq_left hlo.le]
  · rw [if_neg hlo]
    by_cases hhi : 1 / 2 < q
    · rw [if_pos hhi]
      simp only [rationalClipHalf, min_eq_left hhi.le, max_eq_right (by norm_num : -(1 / 2 : ℚ) ≤ 1 / 2)]
    · rw [if_neg hhi]
      unfold rationalClipHalf
      rw [min_eq_right (le_of_not_gt hhi), max_eq_right (le_of_not_gt hlo)]


/-- The mathematical reference label angle; no canonical output-computation claim is made here. -/
def labelFilterAngle (E : ElementaryAnalyticInputs) (δ M j : ℚ) (n k : ℕ) : ℚ :=
  approximatedFilterAngle E δ (rationalLabelPhase E M j n) n k

/-- A complete label-angle error estimate for the actual rational output. -/
theorem labelFilterAngle_error (E : ElementaryAnalyticInputs) (δ M j : ℚ) (n k : ℕ)
    (hδ : 0 < δ) (hM : 0 < M) (hj : 0 ≤ j) (hjM : j ≤ M) :
    ‖Paper25.angleRotation (labelFilterAngle E δ M j n k) -
      Paper25.amplitudeRotation (Paper25.filterG δ (2 * Real.pi * (j : ℝ) / (M : ℝ)))‖
      ≤ 2 * bitError k + (20 / Real.sqrt 3) * (bitError n / (δ : ℝ)) := by
  have h := approximatedFilterAngle_matrix_error E δ (rationalLabelPhase E M j n) n k
    (2 * Real.pi * (j : ℝ) / (M : ℝ)) (4 * bitError n) hδ
    (rationalLabelPhase_error E M j n hM hj hjM)
  convert h using 1 <;> ring

/-- An explicit per-gate reciprocal-precision budget suffices for any desired
rotation error. Generation and arithmetic take place in the classical compiler. -/
theorem labelFilterAngle_error_of_budget (E : ElementaryAnalyticInputs)
    (δ M j : ℚ) (n k : ℕ) (ε : ℝ)
    (hδ : 0 < δ) (hM : 0 < M) (hj : 0 ≤ j) (hjM : j ≤ M)
    (hk : bitError k ≤ ε / 4) (hn : bitError n ≤ (δ : ℝ) * ε / 40) :
    ‖Paper25.angleRotation (labelFilterAngle E δ M j n k) -
      Paper25.amplitudeRotation (Paper25.filterG δ (2 * Real.pi * (j : ℝ) / (M : ℝ)))‖ ≤ ε := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hfrac : bitError n / (δ : ℝ) ≤ ε / 40 := by
    apply (div_le_iff₀ hδR).2
    nlinarith [hn]
  have hroot : 1 ≤ Real.sqrt 3 := Real.one_le_sqrt.mpr (by norm_num)
  have hcoef : (20 / Real.sqrt 3 : ℝ) ≤ 20 := by
    apply (div_le_iff₀ (by positivity : 0 < Real.sqrt 3)).2
    nlinarith
  have hterm : (20 / Real.sqrt 3) * (bitError n / (δ : ℝ)) ≤ 20 * (ε / 40) :=
    (mul_le_mul_of_nonneg_right hcoef (by have h := bitError_pos n; positivity)).trans
      (mul_le_mul_of_nonneg_left hfrac (by norm_num))
  exact (labelFilterAngle_error E δ M j n k hδ hM hj hjM).trans (by linarith)

end Paper25.OperationalModel
