import Paper25.ElementaryAnalytic

/-!
# Actual unreduced numerical outputs

Every numerical input, output, and intermediate value in this module is a
`RationalRep`. Its numerator and positive denominator are printed directly;
no normalization by gcd is performed. `value : RationalRep → ℚ` is only a
mathematical interpretation. The published elementary inputs retain their
raw query/output error guarantees, which need not be representation-independent.
The complete label-angle formula and its FL composition are derived here.
-/
noncomputable section
set_option maxHeartbeats 600000
namespace Paper25.OperationalModel

/-- One fixed raw query supplies the pi approximation. -/
def representedPiQuery (n : ℕ) : RepresentedQuery (fun q => |q| ≤ 1) :=
  ⟨RationalRep.ofRat 0, n, by simp [RationalRep.ofRat_value]⟩

def representedPi (E : ElementaryAnalyticInputs) (n : ℕ) : RationalRep :=
  (RationalRep.ofRat 2).mul (E.arccos.representedValue (representedPiQuery n))

lemma representedPi_value (E : ElementaryAnalyticInputs) (n : ℕ) :
    (representedPi E n).value = rationalPi E n := by
  simp only [representedPi, RationalRep.value_mul, RationalRep.ofRat_value, rationalPi,
    RationalAdditiveApproximation.eval, RationalAdditiveApproximation.value,
    RationalQuery.represented, representedPiQuery]

lemma representedPi_error (E : ElementaryAnalyticInputs) (n : ℕ) :
    |((representedPi E n).value : ℝ) - Real.pi| ≤ 2 * bitError n := by
  rw [representedPi_value]
  exact rationalPi_error E n

def representedLabelPhase (E : ElementaryAnalyticInputs) (M j : RationalRep) (n : ℕ) : RationalRep :=
  (((RationalRep.ofRat 2).mul (representedPi E n)).mul j).div M

lemma representedLabelPhase_value (E : ElementaryAnalyticInputs) (M j : RationalRep) (n : ℕ) :
    (representedLabelPhase E M j n).value = rationalLabelPhase E M.value j.value n := by
  simp only [representedLabelPhase, RationalRep.value_div, RationalRep.value_mul,
    RationalRep.ofRat_value, representedPi_value, rationalLabelPhase]

lemma representedLabelPhase_error (E : ElementaryAnalyticInputs) (M j : RationalRep) (n : ℕ)
    (hM : 0 < M.value) (hj : 0 ≤ j.value) (hjM : j.value ≤ M.value) :
    |((representedLabelPhase E M j n).value : ℝ) - 2 * Real.pi * (j.value : ℝ) / (M.value : ℝ)|
      ≤ 4 * bitError n := by
  rw [representedLabelPhase_value]
  exact rationalLabelPhase_error E M.value j.value n hM hj hjM

/-- Clipping selects one of the three existing raw fractions. -/
def representedClipHalf (q : RationalRep) : RationalRep :=
  if q.less (RationalRep.ofRat (-(1 / 2))) then RationalRep.ofRat (-(1 / 2))
  else if (RationalRep.ofRat (1 / 2)).less q then RationalRep.ofRat (1 / 2) else q

lemma representedClipHalf_value (q : RationalRep) :
    (representedClipHalf q).value = rationalClipHalf q.value := by
  rw [rationalClipHalf_eq_if]
  unfold representedClipHalf
  simp only [RationalRep.less_eq_true, RationalRep.ofRat_value]
  split_ifs <;> simp_all only [RationalRep.ofRat_value]

lemma representedClipHalf_mem (q : RationalRep) : |(representedClipHalf q).value| ≤ 1 / 2 := by
  rw [representedClipHalf_value]
  exact rationalClipHalf_mem _

/-- An exact raw quotient, with only numerator/denominator arithmetic. -/
def representedFilter (δ t : RationalRep) : RationalRep :=
  (δ.mul t).div ((t.mul t).add (δ.mul δ))

lemma representedFilter_value (δ t : RationalRep) :
    (representedFilter δ t).value = rationalFilter δ.value t.value := by
  simp only [representedFilter, RationalRep.value_div, RationalRep.value_mul,
    RationalRep.value_add, rationalFilter, pow_two]

def representedCosQuery (θ : RationalRep) (n : ℕ) : RepresentedQuery (fun _ => True) :=
  ⟨θ, n, trivial⟩

def representedFilterAmplitude (E : ElementaryAnalyticInputs) (δ θ : RationalRep) (n : ℕ) : RationalRep :=
  representedClipHalf (representedFilter δ (E.cos.representedValue (representedCosQuery θ n)))

lemma representedFilterAmplitude_mem (E : ElementaryAnalyticInputs) (δ θ : RationalRep) (n : ℕ) :
    |(representedFilterAmplitude E δ θ n).value| ≤ 1 / 2 := representedClipHalf_mem _

lemma representedFilterAmplitude_error (E : ElementaryAnalyticInputs)
    (δ θ : RationalRep) (n : ℕ) (φ η : ℝ) (hδ : 0 < δ.value)
    (hθ : |(θ.value : ℝ) - φ| ≤ η) :
    |((representedFilterAmplitude E δ θ n).value : ℝ) - Paper25.filterG δ.value φ|
      ≤ (bitError n + η) / (δ.value : ℝ) := by
  have hδR : (0 : ℝ) < δ.value := by exact_mod_cast hδ
  have hcos := E.cos.represented_error (representedCosQuery θ n)
  have hinput := (abs_sub_le ((E.cos.representedValue (representedCosQuery θ n)).value : ℝ)
    (Real.cos θ.value) (Real.cos φ)).trans
    (add_le_add hcos ((Paper25.cos_abs_sub_le θ.value φ).trans hθ))
  have hclip := rationalClipHalf_error
    (rationalFilter δ.value (E.cos.representedValue (representedCosQuery θ n)).value)
    (Paper25.filterG δ.value φ) (Paper25.filterG_range_bound δ.value φ hδR)
  rw [rationalFilter_cast] at hclip
  have hfilter := Paper25.filterFn_abs_sub_le (δ.value : ℝ)
    (E.cos.representedValue (representedCosQuery θ n)).value (Real.cos φ) hδR
  simpa only [representedFilterAmplitude, representedClipHalf_value, representedFilter_value]
    using hclip.trans (hfilter.trans (div_le_div_of_nonneg_right hinput hδR.le))

def representedFilterArccosQuery (E : ElementaryAnalyticInputs) (δ θ : RationalRep) (n k : ℕ) :
    RepresentedQuery (fun q => |q| ≤ 1) :=
  ⟨representedFilterAmplitude E δ θ n, k, by
    have h := representedFilterAmplitude_mem E δ θ n; linarith⟩

def representedFilterAngle (E : ElementaryAnalyticInputs) (δ θ : RationalRep) (n k : ℕ) : RationalRep :=
  (RationalRep.ofRat 2).mul (E.arccos.representedValue (representedFilterArccosQuery E δ θ n k))

open scoped Matrix.Norms.L2Operator

/-- Error for the actual raw output. It is not identified with a canonical
reference query's possibly different approximation. -/
theorem representedFilterAngle_matrix_error (E : ElementaryAnalyticInputs)
    (δ θ : RationalRep) (n k : ℕ) (φ η : ℝ) (hδ : 0 < δ.value)
    (hθ : |(θ.value : ℝ) - φ| ≤ η) :
    ‖Paper25.angleRotation (representedFilterAngle E δ θ n k).value -
      Paper25.amplitudeRotation (Paper25.filterG δ.value φ)‖
      ≤ 2 * bitError k + (4 / Real.sqrt 3) * ((bitError n + η) / (δ.value : ℝ)) := by
  let u := (representedFilterAmplitude E δ θ n).value
  let a := Paper25.filterG δ.value φ
  let v := (E.arccos.representedValue (representedFilterArccosQuery E δ θ n k)).value
  have hu : |(u : ℝ)| ≤ 1 / 2 := by
    have hc : ((|u| : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_mono (representedFilterAmplitude_mem E δ θ n)
    simpa only [Rat.cast_abs, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hc
  have hδR : (0 : ℝ) < δ.value := by exact_mod_cast hδ
  have ha : |a| ≤ 1 / 2 := Paper25.filterG_range_bound δ.value φ hδR
  have hv : |(v : ℝ) - Real.arccos u| ≤ bitError k :=
    E.arccos.represented_error (representedFilterArccosQuery E δ θ n k)
  have hstable := Paper25.arccos_abs_sub_le_half (u : ℝ) a hu ha
  have hamp := representedFilterAmplitude_error E δ θ n φ η hδ hθ
  have htriangle := (abs_sub_le (v : ℝ) (Real.arccos u) (Real.arccos a)).trans (add_le_add hv hstable)
  have hmul := mul_le_mul_of_nonneg_left hamp (by positivity : 0 ≤ 2 / Real.sqrt 3)
  change (2 / Real.sqrt 3) * |(u : ℝ) - a| ≤ _ at hmul
  have hsum := htriangle.trans (add_le_add_left hmul (bitError k))
  have hangle : |((representedFilterAngle E δ θ n k).value : ℝ) - 2 * Real.arccos a|
      ≤ 2 * bitError k + (4 / Real.sqrt 3) * ((bitError n + η) / (δ.value : ℝ)) := by
    have hid : ((representedFilterAngle E δ θ n k).value : ℝ) = 2 * (v : ℝ) := by
      simp only [representedFilterAngle, RationalRep.value_mul, RationalRep.ofRat_value, Rat.cast_mul, Rat.cast_ofNat]
      rfl
    rw [hid, ← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      _ ≤ 2 * (bitError k + (2 / Real.sqrt 3) * ((bitError n + η) / (δ.value : ℝ))) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = _ := by ring
  exact (Paper25.angleRotation_amplitude_error _ a (by linarith)).trans hangle

def representedLabelFilterAngle (E : ElementaryAnalyticInputs) (δ M j : RationalRep) (n k : ℕ) : RationalRep :=
  representedFilterAngle E δ (representedLabelPhase E M j n) n k

theorem representedLabelFilterAngle_error (E : ElementaryAnalyticInputs)
    (δ M j : RationalRep) (n k : ℕ) (hδ : 0 < δ.value) (hM : 0 < M.value)
    (hj : 0 ≤ j.value) (hjM : j.value ≤ M.value) :
    ‖Paper25.angleRotation (representedLabelFilterAngle E δ M j n k).value -
      Paper25.amplitudeRotation (Paper25.filterG δ.value (2 * Real.pi * (j.value : ℝ) / (M.value : ℝ)))‖
      ≤ 2 * bitError k + (20 / Real.sqrt 3) * (bitError n / (δ.value : ℝ)) := by
  have h := representedFilterAngle_matrix_error E δ (representedLabelPhase E M j n) n k
    (2 * Real.pi * (j.value : ℝ) / (M.value : ℝ)) (4 * bitError n) hδ
    (representedLabelPhase_error E M j n hM hj hjM)
  convert h using 1 <;> ring

/-- An explicit per-gate reciprocal-precision budget suffices for any desired
rotation error. Generation and arithmetic take place in the classical compiler. -/
theorem representedLabelFilterAngle_error_of_budget (E : ElementaryAnalyticInputs)
    (δ M j : RationalRep) (n k : ℕ) (ε : ℝ)
    (hδ : 0 < δ.value) (hM : 0 < M.value) (hj : 0 ≤ j.value) (hjM : j.value ≤ M.value)
    (hk : bitError k ≤ ε / 4) (hn : bitError n ≤ (δ.value : ℝ) * ε / 40) :
    ‖Paper25.angleRotation (representedLabelFilterAngle E δ M j n k).value -
      Paper25.amplitudeRotation (Paper25.filterG δ.value (2 * Real.pi * (j.value : ℝ) / (M.value : ℝ)))‖ ≤ ε := by
  have hδR : (0 : ℝ) < δ.value := by exact_mod_cast hδ
  have hfrac : bitError n / (δ.value : ℝ) ≤ ε / 40 := by
    apply (div_le_iff₀ hδR).2
    nlinarith [hn]
  have hroot : 1 ≤ Real.sqrt 3 := Real.one_le_sqrt.mpr (by norm_num)
  have hcoef : (20 / Real.sqrt 3 : ℝ) ≤ 20 := by
    apply (div_le_iff₀ (by positivity : 0 < Real.sqrt 3)).2
    nlinarith
  have hterm : (20 / Real.sqrt 3) * (bitError n / (δ.value : ℝ)) ≤ 20 * (ε / 40) :=
    (mul_le_mul_of_nonneg_right hcoef (by have h := bitError_pos n; positivity)).trans
      (mul_le_mul_of_nonneg_left hfrac (by norm_num))
  exact (representedLabelFilterAngle_error E δ M j n k hδ hM hj hjM).trans (by linarith)


/-- Exact raw arithmetic composition. No canonical encoding occurs. -/
lemma computes_represented_binary (C : ClassicalDescriptionClosure)
    {α : Type} (encode : α → Input) (f g : α → RationalRep) (op : RationalRep → RationalRep → RationalRep)
    (hf : LogspaceComputes encode (fun a => (f a).encode))
    (hg : LogspaceComputes encode (fun a => (g a).encode))
    (hop : LogspaceComputes encodeRationalRepPair (fun a => (op a.1 a.2).encode)) :
    LogspaceComputes encode (fun a => (op (f a) (g a)).encode) :=
  C.compose encode encodeRationalRepPair (fun a => (f a, g a)) _
    (C.pair encode _ _ hf hg) hop

lemma representedPi_computes (E : ElementaryAnalyticInputs) (C : ClassicalDescriptionClosure)
    {α : Type} (encode : α → Input) (n : α → ℕ)
    (hn : LogspaceComputes encode (fun a => encodeNat (n a))) :
    LogspaceComputes encode (fun a => (representedPi E (n a)).encode) := by
  have hquery : LogspaceComputes encode (fun a => RepresentedQuery.encode (representedPiQuery (n a))) :=
    C.concat encode _ _ (C.constant encode ((RationalRep.ofRat 0).encode)) hn
  have hcos := C.compose encode RepresentedQuery.encode (fun a => representedPiQuery (n a)) _
    hquery E.arccos.computes
  exact computes_represented_binary C encode (fun _ => RationalRep.ofRat 2)
    (fun a => E.arccos.representedValue (representedPiQuery (n a))) RationalRep.mul
    (C.constant encode ((RationalRep.ofRat 2).encode)) hcos C.rationalMul

lemma representedLabelPhase_computes (E : ElementaryAnalyticInputs) (C : ClassicalDescriptionClosure)
    {α : Type} (encode : α → Input) (M j : α → RationalRep) (n : α → ℕ)
    (hM : LogspaceComputes encode (fun a => (M a).encode))
    (hj : LogspaceComputes encode (fun a => (j a).encode))
    (hn : LogspaceComputes encode (fun a => encodeNat (n a))) :
    LogspaceComputes encode (fun a => (representedLabelPhase E (M a) (j a) (n a)).encode) := by
  have hpi := representedPi_computes E C encode n hn
  have htwoPi := computes_represented_binary C encode (fun _ => RationalRep.ofRat 2)
    (fun a => representedPi E (n a)) RationalRep.mul
    (C.constant encode ((RationalRep.ofRat 2).encode)) hpi C.rationalMul
  have hnum := computes_represented_binary C encode
    (fun a => (RationalRep.ofRat 2).mul (representedPi E (n a))) j RationalRep.mul htwoPi hj C.rationalMul
  exact computes_represented_binary C encode
    (fun a => ((RationalRep.ofRat 2).mul (representedPi E (n a))).mul (j a)) M
    RationalRep.div hnum hM C.rationalDiv

lemma representedClipHalf_computes (C : ClassicalDescriptionClosure) {α : Type}
    (encode : α → Input) (f : α → RationalRep)
    (hf : LogspaceComputes encode (fun a => (f a).encode)) :
    LogspaceComputes encode (fun a => (representedClipHalf (f a)).encode) := by
  have hlo := C.constant encode ((RationalRep.ofRat (-(1 / 2))).encode)
  have hhi := C.constant encode ((RationalRep.ofRat (1 / 2)).encode)
  have hpLo : LogspaceComputes encode (fun a => encodeBool ((f a).less (RationalRep.ofRat (-(1 / 2))))) :=
    C.compose encode encodeRationalRepPair (fun a => (f a, RationalRep.ofRat (-(1 / 2)))) _
      (C.pair encode _ _ hf hlo) C.rationalLess
  have hpHi : LogspaceComputes encode (fun a => encodeBool ((RationalRep.ofRat (1 / 2)).less (f a))) :=
    C.compose encode encodeRationalRepPair (fun a => (RationalRep.ofRat (1 / 2), f a)) _
      (C.pair encode _ _ hhi hf) C.rationalLess
  have hinner := C.conditional encode (fun a => (RationalRep.ofRat (1 / 2)).less (f a)) _ _ hpHi hhi hf
  have houter := C.conditional encode (fun a => (f a).less (RationalRep.ofRat (-(1 / 2)))) _ _ hpLo hlo hinner
  have heq : (fun a => (representedClipHalf (f a)).encode) =
      (fun a => if (f a).less (RationalRep.ofRat (-(1 / 2))) then (RationalRep.ofRat (-(1 / 2))).encode
        else if (RationalRep.ofRat (1 / 2)).less (f a) then (RationalRep.ofRat (1 / 2)).encode else (f a).encode) := by
    funext a
    unfold representedClipHalf
    split_ifs <;> rfl
  rw [heq]
  exact houter

lemma representedFilter_computes (C : ClassicalDescriptionClosure) {α : Type}
    (encode : α → Input) (δ t : α → RationalRep)
    (hδ : LogspaceComputes encode (fun a => (δ a).encode))
    (ht : LogspaceComputes encode (fun a => (t a).encode)) :
    LogspaceComputes encode (fun a => (representedFilter (δ a) (t a)).encode) := by
  have hnum := computes_represented_binary C encode δ t RationalRep.mul hδ ht C.rationalMul
  have ht2 := computes_represented_binary C encode t t RationalRep.mul ht ht C.rationalMul
  have hδ2 := computes_represented_binary C encode δ δ RationalRep.mul hδ hδ C.rationalMul
  have hden := computes_represented_binary C encode (fun a => (t a).mul (t a))
    (fun a => (δ a).mul (δ a)) RationalRep.add ht2 hδ2 C.rationalAdd
  exact computes_represented_binary C encode (fun a => (δ a).mul (t a))
    (fun a => ((t a).mul (t a)).add ((δ a).mul (δ a))) RationalRep.div hnum hden C.rationalDiv

theorem representedFilterAmplitude_computes (E : ElementaryAnalyticInputs) (C : ClassicalDescriptionClosure)
    {α : Type} (encode : α → Input) (δ θ : α → RationalRep) (n : α → ℕ)
    (hδ : LogspaceComputes encode (fun a => (δ a).encode))
    (hθ : LogspaceComputes encode (fun a => (θ a).encode))
    (hn : LogspaceComputes encode (fun a => encodeNat (n a))) :
    LogspaceComputes encode (fun a => (representedFilterAmplitude E (δ a) (θ a) (n a)).encode) := by
  have hquery : LogspaceComputes encode (fun a => RepresentedQuery.encode (representedCosQuery (θ a) (n a))) :=
    C.concat encode _ _ hθ hn
  have hcos := C.compose encode RepresentedQuery.encode (fun a => representedCosQuery (θ a) (n a)) _
    hquery E.cos.computes
  exact representedClipHalf_computes C encode _ (representedFilter_computes C encode δ _ hδ hcos)

theorem representedFilterAngle_computes (E : ElementaryAnalyticInputs) (C : ClassicalDescriptionClosure)
    {α : Type} (encode : α → Input) (δ θ : α → RationalRep) (n k : α → ℕ)
    (hδ : LogspaceComputes encode (fun a => (δ a).encode))
    (hθ : LogspaceComputes encode (fun a => (θ a).encode))
    (hn : LogspaceComputes encode (fun a => encodeNat (n a)))
    (hk : LogspaceComputes encode (fun a => encodeNat (k a))) :
    LogspaceComputes encode (fun a => (representedFilterAngle E (δ a) (θ a) (n a) (k a)).encode) := by
  have hamp := representedFilterAmplitude_computes E C encode δ θ n hδ hθ hn
  have hquery : LogspaceComputes encode
      (fun a => RepresentedQuery.encode (representedFilterArccosQuery E (δ a) (θ a) (n a) (k a))) :=
    C.concat encode _ _ hamp hk
  have harccos := C.compose encode RepresentedQuery.encode
    (fun a => representedFilterArccosQuery E (δ a) (θ a) (n a) (k a)) _ hquery E.arccos.computes
  exact computes_represented_binary C encode (fun _ => RationalRep.ofRat 2)
    (fun a => E.arccos.representedValue (representedFilterArccosQuery E (δ a) (θ a) (n a) (k a)))
    RationalRep.mul (C.constant encode ((RationalRep.ofRat 2).encode)) harccos C.rationalMul

theorem representedLabelFilterAngle_computes (E : ElementaryAnalyticInputs) (C : ClassicalDescriptionClosure)
    {α : Type} (encode : α → Input) (δ M j : α → RationalRep) (n k : α → ℕ)
    (hδ : LogspaceComputes encode (fun a => (δ a).encode))
    (hM : LogspaceComputes encode (fun a => (M a).encode))
    (hj : LogspaceComputes encode (fun a => (j a).encode))
    (hn : LogspaceComputes encode (fun a => encodeNat (n a)))
    (hk : LogspaceComputes encode (fun a => encodeNat (k a))) :
    LogspaceComputes encode (fun a => (representedLabelFilterAngle E (δ a) (M a) (j a) (n a) (k a)).encode) := by
  exact representedFilterAngle_computes E C encode δ
    (fun a => representedLabelPhase E (M a) (j a) (n a)) n k hδ
    (representedLabelPhase_computes E C encode M j n hM hj hn) hn hk

end Paper25.OperationalModel
