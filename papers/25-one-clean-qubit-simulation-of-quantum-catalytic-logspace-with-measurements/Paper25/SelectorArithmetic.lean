import Paper25.RepresentedAnalytic
import Paper25.MatrixCompilationNorm
import Paper25.LocalCompilation
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Rational compilation of the fixed weighted selector

The ideal selector `prepareThird` uses sqrt(1/3) and sqrt(2/3). It is not an
exact rational-radian gate. This module derives a rational Ry angle from the
same elementary numerical external inputs as `ElementaryAnalytic`, proves the
full matrix error, and derives the classical angle-output computation by FL
composition. No exact selector gate or selector compiler is an external input.
-/

noncomputable section
set_option maxHeartbeats 600000

namespace Paper25

/-- The exact real amplitude of the fixed one-third selector. -/
def selectorAmplitude : ℝ := Real.sqrt (1 / 3)

lemma selectorAmplitude_bounds : 1 / 4 ≤ selectorAmplitude ∧ selectorAmplitude ≤ 3 / 4 := by
  have hs : selectorAmplitude ^ 2 = 1 / 3 := Real.sq_sqrt (by norm_num)
  have hn : 0 ≤ selectorAmplitude := Real.sqrt_nonneg _
  constructor <;> nlinarith

lemma prepareThird_eq_amplitudeRotation : prepareThird = amplitudeRotation selectorAmplitude := by
  unfold prepareThird amplitudeRotation selectorAmplitude
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 3)]
  norm_num

/-- A safe buffer containing sqrt(1/3). The derivative constant is two on
[1/4,3/4]; the smaller half-interval constant cannot be used at sqrt(1/3). -/
lemma arccos_abs_sub_le_selector (x y : ℝ)
    (hx : x ∈ Set.Icc (1 / 4 : ℝ) (3 / 4))
    (hy : y ∈ Set.Icc (1 / 4 : ℝ) (3 / 4)) :
    |Real.arccos x - Real.arccos y| ≤ 2 * |x - y| := by
  have hdiff : ∀ t ∈ Set.Icc (1 / 4 : ℝ) (3 / 4), DifferentiableAt ℝ Real.arccos t := by
    intro t ht
    exact (Real.hasDerivAt_arccos (by linarith [ht.1]) (by linarith [ht.2])).differentiableAt
  have hbound : ∀ t ∈ Set.Icc (1 / 4 : ℝ) (3 / 4), ‖deriv Real.arccos t‖ ≤ 2 := by
    intro t ht
    have hden : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
    have hs : (1 / 2 : ℝ) ≤ Real.sqrt (1 - t ^ 2) := by
      have hsq := Real.sq_sqrt hden.le
      nlinarith [Real.sqrt_nonneg (1 - t ^ 2), ht.1, ht.2]
    rw [(Real.hasDerivAt_arccos (by linarith [ht.1]) (by linarith [ht.2])).deriv,
      Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity : 0 < 1 / Real.sqrt (1 - t ^ 2))]
    calc
      _ ≤ 1 / (1 / 2 : ℝ) := one_div_le_one_div_of_le (by norm_num) hs
      _ = 2 := by norm_num
  have h := @Convex.norm_image_sub_le_of_norm_deriv_le ℝ ℝ _ _ _
    Real.arccos (Set.Icc (1 / 4 : ℝ) (3 / 4)) x y 2 hdiff hbound
    (convex_Icc _ _) hx hy
  simpa [Real.norm_eq_abs, abs_sub_comm] using h

end Paper25

namespace Paper25.OperationalModel

/-- Clipping a square-root approximation to a fixed interior interval. -/
def selectorClip (q : ℚ) : ℚ := max (1 / 4) (min (3 / 4) q)

lemma selectorClip_mem (q : ℚ) : selectorClip q ∈ Set.Icc (1 / 4 : ℚ) (3 / 4) := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

lemma selectorClip_cast (q : ℚ) :
    (selectorClip q : ℝ) = max (1 / 4) (min (3 / 4) (q : ℝ)) := by
  simp [selectorClip, Rat.cast_max, Rat.cast_min]

lemma selectorClip_error (q : ℚ) (a : ℝ) (ha : a ∈ Set.Icc (1 / 4 : ℝ) (3 / 4)) :
    |(selectorClip q : ℝ) - a| ≤ |(q : ℝ) - a| := by
  have hfix : max (1 / 4 : ℝ) (min (3 / 4) a) = a := by
    rw [min_eq_right ha.2, max_eq_right ha.1]
  rw [selectorClip_cast]
  have hmax := abs_max_sub_max_le_max (1 / 4 : ℝ) (min (3 / 4) (q : ℝ))
    (1 / 4) (min (3 / 4) a)
  have hmin := abs_min_sub_min_le_max (3 / 4 : ℝ) (q : ℝ) (3 / 4) a
  have hmax' : |max (1 / 4) (min (3 / 4) (q : ℝ)) - max (1 / 4) (min (3 / 4) a)|
      ≤ |min (3 / 4) (q : ℝ) - min (3 / 4) a| := by
    simpa only [sub_self, abs_zero,
      max_eq_right (abs_nonneg (min (3 / 4) (q : ℝ) - min (3 / 4) a))] using hmax
  have hmin' : |min (3 / 4) (q : ℝ) - min (3 / 4) a| ≤ |(q : ℝ) - a| := by
    simpa only [sub_self, abs_zero, max_eq_right (abs_nonneg ((q : ℝ) - a))] using hmin
  calc
    _ = |max (1 / 4) (min (3 / 4) (q : ℝ)) - max (1 / 4) (min (3 / 4) a)| := by rw [hfix]
    _ ≤ |min (3 / 4) (q : ℝ) - min (3 / 4) a| := hmax'
    _ ≤ |(q : ℝ) - a| := hmin'

/-- Raw clipping preserves one existing representation rather than reducing it. -/
def selectorClipRep (q : RationalRep) : RationalRep :=
  RationalRep.clip (RationalRep.ofRat (1 / 4)) (RationalRep.ofRat (3 / 4)) q

lemma selectorClipRep_value (q : RationalRep) : (selectorClipRep q).value = selectorClip q.value := by
  rw [selectorClipRep, RationalRep.value_clip]
  · simp only [RationalRep.ofRat_value, selectorClip]
  · norm_num

def selectorSqrtQuery (n : ℕ) : RepresentedQuery (fun q => 0 < q) :=
  ⟨RationalRep.ofRat (1 / 3), n, by norm_num⟩

def selectorRationalAmplitude (E : ElementaryAnalyticInputs) (n : ℕ) : RationalRep :=
  selectorClipRep (E.sqrt.representedValue (selectorSqrtQuery n))

lemma selectorRationalAmplitude_mem (E : ElementaryAnalyticInputs) (n : ℕ) :
    (selectorRationalAmplitude E n).value ∈ Set.Icc (1 / 4 : ℚ) (3 / 4) := by
  rw [selectorRationalAmplitude, selectorClipRep_value]
  exact selectorClip_mem _

lemma selectorRationalAmplitude_real_mem (E : ElementaryAnalyticInputs) (n : ℕ) :
    ((selectorRationalAmplitude E n).value : ℝ) ∈ Set.Icc (1 / 4 : ℝ) (3 / 4) := by
  constructor
  · have hc := Rat.cast_mono (K := ℝ) (selectorRationalAmplitude_mem E n).1
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hc
  · have hc := Rat.cast_mono (K := ℝ) (selectorRationalAmplitude_mem E n).2
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hc

lemma selectorRationalAmplitude_error (E : ElementaryAnalyticInputs) (n : ℕ) :
    |((selectorRationalAmplitude E n).value : ℝ) - Paper25.selectorAmplitude| ≤ bitError n := by
  have hs : |((E.sqrt.representedValue (selectorSqrtQuery n)).value : ℝ) - Paper25.selectorAmplitude|
      ≤ bitError n * Paper25.selectorAmplitude := by
    simpa only [selectorSqrtQuery, RationalRep.ofRat_value, Rat.cast_div, Rat.cast_one,
      Rat.cast_ofNat, Paper25.selectorAmplitude] using E.sqrt.represented_error (selectorSqrtQuery n)
  have hadd : |((E.sqrt.representedValue (selectorSqrtQuery n)).value : ℝ) - Paper25.selectorAmplitude|
      ≤ bitError n := hs.trans (mul_le_of_le_one_right (bitError_pos n).le
        (Paper25.selectorAmplitude_bounds.2.trans (by norm_num)))
  rw [selectorRationalAmplitude, selectorClipRep_value]
  exact (selectorClip_error _ _ Paper25.selectorAmplitude_bounds).trans hadd

def selectorArccosQuery (E : ElementaryAnalyticInputs) (n : ℕ) :
    RepresentedQuery (fun q => |q| ≤ 1) :=
  ⟨selectorRationalAmplitude E n, n, by
    have h := selectorRationalAmplitude_mem E n
    rw [abs_le]
    constructor <;> linarith [h.1, h.2]⟩

/-- The actual unreduced angle payload passed to `rotationRep`. -/
def selectorAngle (E : ElementaryAnalyticInputs) (n : ℕ) : RationalRep :=
  (RationalRep.ofRat 2).mul (E.arccos.representedValue (selectorArccosQuery E n))

lemma selectorAngle_error (E : ElementaryAnalyticInputs) (n : ℕ) :
    |((selectorAngle E n).value : ℝ) - 2 * Real.arccos Paper25.selectorAmplitude| ≤ 6 * bitError n := by
  let u := (selectorRationalAmplitude E n).value
  let v := (E.arccos.representedValue (selectorArccosQuery E n)).value
  have ha : |(v : ℝ) - Real.arccos u| ≤ bitError n :=
    E.arccos.represented_error (selectorArccosQuery E n)
  have hstable := Paper25.arccos_abs_sub_le_selector (u : ℝ) Paper25.selectorAmplitude
    (selectorRationalAmplitude_real_mem E n) Paper25.selectorAmplitude_bounds
  have hsqrt := selectorRationalAmplitude_error E n
  have htriangle := (abs_sub_le (v : ℝ) (Real.arccos u)
    (Real.arccos Paper25.selectorAmplitude)).trans (add_le_add ha hstable)
  have hmul := mul_le_mul_of_nonneg_left hsqrt (by norm_num : (0 : ℝ) ≤ 2)
  have htotal : |(v : ℝ) - Real.arccos Paper25.selectorAmplitude| ≤ 3 * bitError n := by
    change 2 * |(u : ℝ) - Paper25.selectorAmplitude| ≤ _ at hmul
    linarith
  have hid : ((selectorAngle E n).value : ℝ) = 2 * (v : ℝ) := by
    simp only [selectorAngle, RationalRep.value_mul, RationalRep.ofRat_value,
      Rat.cast_mul, Rat.cast_ofNat]
    rfl
  rw [hid, ← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

open scoped Matrix.Norms.L2Operator

lemma selectorAngle_matrix_error (E : ElementaryAnalyticInputs) (n : ℕ) :
    ‖Paper25.angleRotation (selectorAngle E n).value - Paper25.prepareThird‖ ≤ 6 * bitError n := by
  rw [Paper25.prepareThird_eq_amplitudeRotation]
  apply (Paper25.angleRotation_amplitude_error _ _ ?_).trans (selectorAngle_error E n)
  rw [abs_of_nonneg (show 0 ≤ Paper25.selectorAmplitude from Real.sqrt_nonneg _)]
  exact (Paper25.selectorAmplitude_bounds).2.trans (by norm_num)

lemma selectorClipRep_computes (C : ClassicalDescriptionClosure) {α : Type}
    (encode : α → Input) (f : α → RationalRep)
    (hf : LogspaceComputes encode (fun a => (f a).encode)) :
    LogspaceComputes encode (fun a => (selectorClipRep (f a)).encode) := by
  have hlo := C.constant encode ((RationalRep.ofRat (1 / 4)).encode)
  have hhi := C.constant encode ((RationalRep.ofRat (3 / 4)).encode)
  have hpLo : LogspaceComputes encode (fun a => encodeBool ((f a).less (RationalRep.ofRat (1 / 4)))) :=
    C.compose encode encodeRationalRepPair (fun a => (f a, RationalRep.ofRat (1 / 4))) _
      (C.pair encode _ _ hf hlo) C.rationalLess
  have hpHi : LogspaceComputes encode (fun a => encodeBool ((RationalRep.ofRat (3 / 4)).less (f a))) :=
    C.compose encode encodeRationalRepPair (fun a => (RationalRep.ofRat (3 / 4), f a)) _
      (C.pair encode _ _ hhi hf) C.rationalLess
  have hinner := C.conditional encode (fun a => (RationalRep.ofRat (3 / 4)).less (f a)) _ _ hpHi hhi hf
  have houter := C.conditional encode (fun a => (f a).less (RationalRep.ofRat (1 / 4))) _ _ hpLo hlo hinner
  have heq : (fun a => (selectorClipRep (f a)).encode) =
      (fun a => if (f a).less (RationalRep.ofRat (1 / 4)) then (RationalRep.ofRat (1 / 4)).encode
        else if (RationalRep.ofRat (3 / 4)).less (f a) then (RationalRep.ofRat (3 / 4)).encode else (f a).encode) := by
    funext a
    unfold selectorClipRep RationalRep.clip
    split_ifs <;> rfl
  rw [heq]
  exact houter

/-- One sqrt query, clipping, one arccos query, and unreduced multiplication
form the complete constant-angle algorithm. -/
theorem selectorAngle_computes (E : ElementaryAnalyticInputs) (C : ClassicalDescriptionClosure)
    {α : Type} (encode : α → Input) (n : α → ℕ)
    (hn : LogspaceComputes encode (fun a => encodeNat (n a))) :
    LogspaceComputes encode (fun a => (selectorAngle E (n a)).encode) := by
  have hsqrtquery : LogspaceComputes encode (fun a => RepresentedQuery.encode (selectorSqrtQuery (n a))) :=
    C.concat encode _ _ (C.constant encode ((RationalRep.ofRat (1 / 3)).encode)) hn
  have hsqrt := C.compose encode RepresentedQuery.encode (fun a => selectorSqrtQuery (n a)) _
    hsqrtquery E.sqrt.computes
  have hamp := selectorClipRep_computes C encode _ hsqrt
  have hquery : LogspaceComputes encode (fun a => RepresentedQuery.encode (selectorArccosQuery E (n a))) :=
    C.concat encode _ _ hamp hn
  have harccos := C.compose encode RepresentedQuery.encode (fun a => selectorArccosQuery E (n a)) _
    hquery E.arccos.computes
  exact computes_represented_binary C encode (fun _ => RationalRep.ofRat 2)
    (fun a => E.arccos.representedValue (selectorArccosQuery E (n a))) RationalRep.mul
    (C.constant encode ((RationalRep.ofRat 2).encode)) harccos C.rationalMul

/-- The precision-family takes the bit count in unary, exactly as in the
published numerical input. -/
theorem selectorAngle_precision_family (E : ElementaryAnalyticInputs) (C : ClassicalDescriptionClosure) :
    LogspaceComputes encodeNat (fun n => (selectorAngle E n).encode) :=
  selectorAngle_computes E C encodeNat id (C.identity encodeNat)

end Paper25.OperationalModel

namespace Paper25.OperationalModel.LocalCompilation

open scoped Matrix.Norms.L2Operator

lemma rotationMatrix_eq_angleRotation (q : ℚ) :
    rotationMatrix q = (Paper25.angleRotation q).submatrix oneBit oneBit := by
  ext i j
  rw [Matrix.submatrix_apply, Paper25.angleRotation_apply]
  rfl

/-- The actual rational-radian gate supplied by GateConvention approximates
the ideal weighted selector in full operator norm. -/
theorem selectorAngle_rotation_error (E : ElementaryAnalyticInputs) (n : ℕ) :
    ‖rotationMatrix (selectorAngle E n).value - Paper25.prepareThird.submatrix oneBit oneBit‖
      ≤ 6 * bitError n := by
  rw [rotationMatrix_eq_angleRotation]
  change ‖(Paper25.angleRotation (selectorAngle E n).value - Paper25.prepareThird).submatrix oneBit oneBit‖ ≤ _
  rw [Paper25.MatrixCompilationNorm.submatrix_equiv_opNorm]
  exact selectorAngle_matrix_error E n

theorem selectorAngle_rotation_error_of_precision (E : ElementaryAnalyticInputs)
    (n : ℕ) (τ : ℝ) (hprecision : bitError n ≤ τ / 6) :
    ‖rotationMatrix (selectorAngle E n).value - Paper25.prepareThird.submatrix oneBit oneBit‖ ≤ τ :=
  (selectorAngle_rotation_error E n).trans (by linarith)

/-- This is an actual returned finite gate list, rather than an exact selector
primitive assumption. Its numerical error is inherited from the chosen angle. -/
theorem selectorGate_error {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (n : ℕ) (τ : ℝ) (hprecision : bitError n ≤ τ / 6) :
    ‖(conv.rotationRep (selectorAngle E n)).matrix - Paper25.prepareThird.submatrix oneBit oneBit‖ ≤ τ := by
  rw [conv.rotationRep_matrix]
  exact selectorAngle_rotation_error_of_precision E n τ hprecision

end Paper25.OperationalModel.LocalCompilation
