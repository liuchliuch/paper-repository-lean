import Paper35.GaussianSegments
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace Paper35.GaussianMarked

/-- An actual affine piece on the stated parameter subinterval. -/
def AffinePiece {m : ℕ} (y : ℝ → Source.Space m) (a b : ℝ) : Prop :=
  ∀ r ∈ Icc (0:ℝ) 1, y (a+r*(b-a)) = segment (y a) (y b) r

theorem normalized_affine_piece_variation {m : ℕ} (hlength : ACCurveLengthLaw)
    (y : ℝ → Source.Space m) (a b : ℝ) (hab : a ≤ b)
    (hpiece : AffinePiece y a b) (hnz : ∀ s ∈ Icc a b, y s ≠ 0) :
    eVariationOn (fun s => Gaussian.normalize (y s)) (Icc a b) =
      ENNReal.ofReal (Real.arccos (inner ℝ (y a) (y b)/(‖y a‖*‖y b‖))) := by
  have hmono : MonotoneOn (fun r : ℝ => a+r*(b-a)) (Icc 0 1) := by
    intro r _ s _ hrs
    exact add_le_add_left (mul_le_mul_of_nonneg_right hrs (sub_nonneg.mpr hab)) a
  have himage : (fun r : ℝ => a+r*(b-a)) '' Icc 0 1 = Icc a b := by
    rw [ContinuousOn.image_Icc_of_monotoneOn (by norm_num : (0:ℝ)≤1) (by fun_prop) hmono]
    simp
  have hparam (r : ℝ) (hr : r ∈ Icc 0 1) : a+r*(b-a) ∈ Icc a b := by
    constructor <;> nlinarith [hr.1,hr.2]
  have heqon : EqOn (((fun s => Gaussian.normalize (y s)) ∘
      fun r : ℝ => a+r*(b-a))) (fun r => Gaussian.normalize (segment (y a) (y b) r))
      (Icc 0 1) := by
    intro r hr
    simp only [Function.comp_apply,hpiece r hr]
  have hvar := eVariationOn.comp_eq_of_monotoneOn (fun s => Gaussian.normalize (y s))
    (fun r : ℝ => a+r*(b-a)) hmono
  rw [himage] at hvar
  rw [← hvar,eVariationOn.eq_of_eqOn heqon]
  apply normalized_segment_variation hlength
  intro r hr
  rw [← hpiece r hr]
  exact hnz _ (hparam r hr)

/-- Piecewise affine paths have the sum of the actual endpoint minor-arc lengths,
including repeated vertices and zero-length pieces. -/
theorem normalized_polyline_variation {m : ℕ} (hlength : ACCurveLengthLaw)
    (y : ℝ → Source.Space m) (knots : ℕ → ℝ) (hmono : Monotone knots)
    (N : ℕ) (L : ℝ) (h0 : knots 0 = 0) (hN : knots N = L)
    (hpieces : ∀ i < N, AffinePiece y (knots i) (knots (i+1)))
    (hnz : ∀ s ∈ Icc 0 L, y s ≠ 0) :
    eVariationOn (fun s => Gaussian.normalize (y s)) (Icc 0 L) =
      ∑ i ∈ Finset.range N, ENNReal.ofReal (Real.arccos
        (inner ℝ (y (knots i)) (y (knots (i+1)))/(‖y (knots i)‖*‖y (knots (i+1))‖))) := by
  have hsum := eVariationOn.sum' (fun s => Gaussian.normalize (y s)) hmono (n := N)
  rw [h0,hN] at hsum
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro i hi
  have hiN : i < N := Finset.mem_range.mp hi
  apply normalized_affine_piece_variation hlength y (knots i) (knots (i+1))
    (hmono (Nat.le_succ i)) (hpieces i hiN)
  intro s hs
  apply hnz s
  constructor
  · have hh := hmono (Nat.zero_le i)
    rw [h0] at hh
    exact hh.trans hs.1
  · have hh := hmono (show i+1 ≤ N by omega)
    rw [hN] at hh
    exact hs.2.trans hh

/-- Corollary 6.3 for the actual full piecewise affine lifted path. The output
counts all local switches on the original interval, so knot parameters and
repeated visits are handled by the original count definition. -/
theorem gaussian_polyline_expectedSwitchCount
    (hcrofton : ClassicalCroftonLaw) (hregular : ClassicalCroftonRegularityLaw)
    (hproj : GaussianUnitProjectionLaw) (hrot : GaussianPairReconstructionLaw)
    (hmax : GaussianMaxIntegralLaw) (hlength : ACCurveLengthLaw)
    (m n : ℕ) (hm : 1 ≤ m) (L : ℝ) (hL : 0 < L) (y : ℝ → Source.Space m)
    (mean : ℝ → ℝ) (C : ℝ≥0) (hlip : LipschitzOnWith C y (Icc 0 L))
    (hnz : ∀ s ∈ Icc 0 L, y s ≠ 0)
    (knots : ℕ → ℝ) (hmono : Monotone knots) (N : ℕ)
    (h0 : knots 0 = 0) (hN : knots N = L)
    (hpieces : ∀ i < N, AffinePiece y (knots i) (knots (i+1)))
    (hLN : VisibleCrossing.LusinNovikovInput (MarkSample m n) (CurveParameter L)) :
    expectedSwitchCount (gaussianIid m (n+2)) (fun Z j s => mean s+inner ℝ (Z j) (y s)) L =
      ENNReal.ofReal (Paper35.gaussianRankCoefficient (n+2)) *
        ∑ i ∈ Finset.range N, ENNReal.ofReal (Real.arccos
          (inner ℝ (y (knots i)) (y (knots (i+1)))/(‖y (knots i)‖*‖y (knots (i+1))‖))) := by
  have hcount (Z : Fin (n+2) → Source.Space m) :
      switchCount (fun j s => mean s+inner ℝ (Z j) (y s)) L =
      switchCount (gaussianScores (fun s => Gaussian.normalize (y s)) Z) L := by
    unfold switchCount
    congr 2
    exact Gaussian.covarianceLift_switchSet_on Z y mean L
      (fun s hs => hnz s ⟨hs.1.le,hs.2.le⟩)
  obtain ⟨D,hD⟩ := GaussianLift.normalized_lipschitzOn hL.le hlip hnz
  have hac : AbsolutelyContinuousOnInterval (fun s => Gaussian.normalize (y s)) 0 L := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := D)
    simpa only [uIcc_of_le hL.le] using hD
  unfold expectedSwitchCount
  simp_rw [hcount]
  change expectedSwitchCount (gaussianIid m (n+2))
    (gaussianScores (fun s => Gaussian.normalize (y s))) L = _
  rw [gaussian_upper_envelope_all_dimensions hcrofton hregular hproj hrot hmax hlength
    m n hm L hL _ hac (fun s hs => Gaussian.normalize_norm _ (hnz s hs)) hLN,
    normalized_polyline_variation hlength y knots hmono N L h0 hN hpieces hnz]
end Paper35.GaussianMarked
