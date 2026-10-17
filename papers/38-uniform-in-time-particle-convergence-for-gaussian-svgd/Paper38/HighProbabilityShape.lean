import Paper38.StandardizedShape
import Paper38.ExpectedRates

/-! Raw concentration is lifted through the proved standardization identity.
The source all-time event is not an external input. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace Paper38.HighProbabilityShape
open Model Sampling ExternalStatisticalInputs

variable {d : ℕ}

/-- From raw Gaussian concentration to the standardized cloud, uniformly for
N≥d+1 and 1≤x≤c0N. Constants are fixed before N,x. -/
theorem standardized_event (hd : 1 ≤ d) (mom : CovarianceMoments d)
    (conc : Concentration d) :
    ∃ C c c0 : ℝ, 0 < C ∧ 0 < c ∧ 0 < c0 ∧
    ∀ N : ℕ, d + 1 ≤ N → ∀ x : ℝ, 1 ≤ x → x ≤ c0 * N →
    ∃ H : Set (Sample d N), MeasurableSet H ∧
      law d N Hᶜ ≤ ENNReal.ofReal (C * Real.exp (-c * x)) ∧
      ∀ ω ∈ H, (covariance d N ω).PosDef ∧
        defect d N ω ≤ conc.C * (1 + x) / N ∧
        opNorm (covariance d N ω - 1) ≤ 1 / 2 ∧
        shapeError d N ω ≤ ENNReal.ofReal (C * (rate d N + x / N)) := by
  let C : ℝ := 1 + 5 * conc.C
  let c : ℝ := min 1 conc.c
  have hCp := conc.C_pos
  have hcp : 0 < c := lt_min zero_lt_one conc.c_pos
  refine ⟨C, c, conc.c0, by dsimp [C]; positivity, hcp, conc.c0_pos, ?_⟩
  intro N hN x hx hxc
  have hNpos : 0 < N := lt_of_lt_of_le (Nat.succ_pos d) hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hr := Model.rate_pos d N hd hNpos
  have hx0 : 0 ≤ x := (by norm_num : (0 : ℝ) ≤ 1).trans hx
  obtain ⟨H1, hH1, hP1, hraw⟩ := conc.raw_matching_event N hN x hx
  obtain ⟨H2, hH2, hP2, hcov⟩ := conc.raw_covariance_event N hN x hx hxc
  obtain ⟨H3, hH3, hP3, hrank⟩ := ExpectedRates.measurable_core (law d N)
    (fun ω => (covariance d N ω).PosDef) (mom.full_rank N hN)
  let H := (H1 ∩ H2) ∩ H3
  have hH : MeasurableSet H := (hH1.inter hH2).inter hH3
  refine ⟨H, hH, ?_, ?_⟩
  · have hmeasure : law d N Hᶜ ≤ law d N H1ᶜ + law d N H2ᶜ := by
      calc
        _ = law d N ((H1ᶜ ∪ H2ᶜ) ∪ H3ᶜ) := by simp only [H, compl_inter]
        _ ≤ (law d N H1ᶜ + law d N H2ᶜ) + law d N H3ᶜ :=
          (measure_union_le _ _).trans (add_le_add_right (measure_union_le _ _) _)
        _ = _ := by rw [hP3, add_zero]
    have he1 : Real.exp (-x) ≤ Real.exp (-c * x) := by
      apply Real.exp_le_exp.mpr
      have : c ≤ 1 := min_le_left _ _
      nlinarith
    have he2 : Real.exp (-conc.c * x) ≤ Real.exp (-c * x) := by
      apply Real.exp_le_exp.mpr
      have : c ≤ conc.c := min_le_right _ _
      nlinarith
    calc
      _ ≤ _ := hmeasure
      _ ≤ ENNReal.ofReal (Real.exp (-x)) +
          ENNReal.ofReal (conc.C * Real.exp (-conc.c * x)) := add_le_add hP1 hP2
      _ = ENNReal.ofReal (Real.exp (-x) + conc.C * Real.exp (-conc.c * x)) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity)]
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have h2 := mul_le_mul_of_nonneg_left he2 hCp.le
        have hp := Real.exp_pos (-c * x)
        dsimp [C]
        nlinarith
  · intro ω hω
    rcases hω with ⟨⟨h1, h2⟩, h3⟩
    have hS := hrank ω h3
    rcases hcov ω h2 with ⟨hdef, hop⟩
    refine ⟨hS, hdef, hop, ?_⟩
    have hrate := Model.inv_sampleSize_le_rate d N hd hNpos
    have hδ : defect d N ω ≤ conc.C * (rate d N + x / N) := by
      apply hdef.trans
      have hdiv : conc.C * (1 + x) / N = conc.C * ((N : ℝ)⁻¹ + x / N) := by ring
      rw [hdiv]
      exact mul_le_mul_of_nonneg_left (add_le_add_right hrate _) hCp.le
    have hshape := StandardizedShape.shape_bound hNpos (cloud d N ω) hS
    calc
      shapeError d N ω ≤ 2 * ENNReal.ofReal (defect d N ω) + 2 * rawError d N ω := hshape
      _ ≤ 2 * ENNReal.ofReal (conc.C * (rate d N + x / N)) +
          2 * ENNReal.ofReal (conc.C * (rate d N + x / N)) :=
        add_le_add (mul_le_mul_left' (ENNReal.ofReal_le_ofReal hδ) 2)
          (mul_le_mul_left' (hraw ω h1) 2)
      _ = ENNReal.ofReal (4 * conc.C * (rate d N + x / N)) := by
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have hr := Model.rate_pos d N hd hNpos
        have hrx : 0 ≤ rate d N + x / N := by positivity
        dsimp [C]
        nlinarith

end Paper38.HighProbabilityShape
