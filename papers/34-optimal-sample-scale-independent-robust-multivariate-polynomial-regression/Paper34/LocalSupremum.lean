import Paper34.Kernel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Local supremum bounds for the actual torus kernels

The interval estimates are proved by the fundamental theorem of calculus. All
suprema are of values of actual functions on closed intervals. Haar integrals
retain the normalized measure used in `Paper34.Kernel`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory Set

namespace Paper34.LocalSupremum

open Paper34.Kernel

/-- The supremum of the norm on an actual closed interval. -/
def intervalSup (v : ℝ → ℂ) (a b : ℝ) : ℝ :=
  sSup ((fun t => ‖v t‖) '' Icc a b)

lemma intervalSup_attained {v : ℝ → ℂ} (hv : Continuous v) {a b : ℝ} (hab : a ≤ b) :
    ∃ t ∈ Icc a b, ‖v t‖ = intervalSup v a b := by
  obtain ⟨t, ht, hmax⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_isMaxOn
    ⟨a, le_rfl, hab⟩ hv.norm.continuousOn
  refine ⟨t, ht, ?_⟩
  apply le_antisymm
  · exact le_csSup ((isCompact_Icc.image hv.norm).bddAbove) ⟨t, ht, rfl⟩
  · change sSup ((fun s => ‖v s‖) '' Icc a b) ≤ ‖v t‖
    apply csSup_le (s := ((fun s => ‖v s‖) '' Icc a b))
      ⟨‖v a‖, a, ⟨le_rfl, hab⟩, rfl⟩
    rintro y ⟨s, hs, rfl⟩
    exact hmax hs

lemma norm_le_intervalSup {v : ℝ → ℂ} (hv : Continuous v) {a b t : ℝ}
    (ht : t ∈ Icc a b) : ‖v t‖ ≤ intervalSup v a b :=
  le_csSup ((isCompact_Icc.image hv.norm).bddAbove) ⟨t, ht, rfl⟩

/-- The oscillation between any two points of an interval is bounded by the
integral of the norm of the genuine derivative on the whole interval. -/
lemma norm_sub_le_integral_norm {v v' : ℝ → ℂ} (hv' : Continuous v')
    (hder : ∀ x : ℝ, HasDerivAt v (v' x) x) {a b s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ‖v t - v s‖ ≤ ∫ x in a..b, ‖v' x‖ := by
  have hordered (s t : ℝ) (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
      ‖v t - v s‖ ≤ ∫ x in a..b, ‖v' x‖ := by
    have hftc : (∫ x in s..t, v' x) = v t - v s :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hder x)
        (hv'.intervalIntegrable s t)
    rw [← hftc]
    exact (intervalIntegral.norm_integral_le_integral_norm hst).trans
      (intervalIntegral.integral_mono_interval has hst htb
        (ae_of_all _ fun x => norm_nonneg _) (hv'.norm.intervalIntegrable a b))
  rcases le_total s t with hst | hts
  · exact hordered s t hs.1 hst ht.2
  · rw [norm_sub_rev]
    exact hordered t s ht.1 hts hs.2

/-- The interval inequality used before equation (3.6). It applies to every
continuously differentiable function, in particular to the paper's kernels. -/
theorem length_mul_intervalSup_le {v v' : ℝ → ℂ} (hv : Continuous v)
    (hv' : Continuous v') (hder : ∀ x : ℝ, HasDerivAt v (v' x) x)
    {a b : ℝ} (hab : a ≤ b) :
    (b - a) * intervalSup v a b ≤
      (∫ x in a..b, ‖v x‖) + (b - a) * ∫ x in a..b, ‖v' x‖ := by
  obtain ⟨t, ht, heq⟩ := intervalSup_attained hv hab
  have hpoint (s : ℝ) (hs : s ∈ Icc a b) :
      ‖v t‖ ≤ ‖v s‖ + ∫ x in a..b, ‖v' x‖ := by
    calc
      ‖v t‖ = ‖v s + (v t - v s)‖ := by congr 1; abel
      _ ≤ ‖v s‖ + ‖v t - v s‖ := norm_add_le _ _
      _ ≤ _ := add_le_add_left (norm_sub_le_integral_norm hv' hder hs ht) _
  have hi := intervalIntegral.integral_mono_on hab
    (continuous_const.intervalIntegrable a b : IntervalIntegrable (fun _ : ℝ => ‖v t‖) volume a b)
    ((hv.norm.add continuous_const).intervalIntegrable a b) hpoint
  rw [intervalIntegral.integral_const,
    intervalIntegral.integral_add (hv.norm.intervalIntegrable a b) (continuous_const.intervalIntegrable a b),
    intervalIntegral.integral_const, smul_eq_mul, smul_eq_mul, heq] at hi
  exact hi

/-- Summing the local FTC estimate over an actual adjacent equal-length grid. -/
theorem grid_intervalSup_le {v v' : ℝ → ℂ} (hv : Continuous v) (hv' : Continuous v')
    (hder : ∀ x : ℝ, HasDerivAt v (v' x) x) (N : ℕ) {h : ℝ} (hh : 0 ≤ h) :
    h * ∑ j ∈ Finset.range N, intervalSup v (j * h) ((j + 1) * h) ≤
      (∫ x in 0..N * h, ‖v x‖) + h * ∫ x in 0..N * h, ‖v' x‖ := by
  have hcell (j : ℕ) : h * intervalSup v (j * h) ((j + 1) * h) ≤
      (∫ x in j * h..(j + 1) * h, ‖v x‖) +
        h * ∫ x in j * h..(j + 1) * h, ‖v' x‖ := by
    have hj : (j : ℝ) * h ≤ (j + 1) * h := by nlinarith
    have hlength : ((j : ℝ) + 1) * h - j * h = h := by ring
    simpa only [hlength] using length_mul_intervalSup_le hv hv' hder hj
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range N) => hcell j)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hvsum := intervalIntegral.sum_integral_adjacent_intervals (a := fun j : ℕ => (j : ℝ) * h)
    (n := N) (μ := volume) (f := fun x => ‖v x‖) (fun _ _ => hv.norm.intervalIntegrable _ _)
  have hv'sum := intervalIntegral.sum_integral_adjacent_intervals (a := fun j : ℕ => (j : ℝ) * h)
    (n := N) (μ := volume) (f := fun x => ‖v' x‖) (fun _ _ => hv'.norm.intervalIntegrable _ _)
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul] at hvsum hv'sum
  rw [hvsum, hv'sum] at hsum
  exact hsum

/-- The real-angle lift after a torus translation. -/
def shiftLift (f : C(Torus, ℂ)) (u : Torus) (t : ℝ) : ℂ := f ((t : Torus) - u)

lemma continuous_shiftLift (f : C(Torus, ℂ)) (u : Torus) : Continuous (shiftLift f u) :=
  f.continuous.comp ((AddCircle.continuous_mk' (2 * Real.pi)).sub continuous_const)

lemma hasDerivAt_shiftLift_valleePoussin (d : ℕ) (u : Torus) (t : ℝ) :
    HasDerivAt (shiftLift (valleePoussin d) u)
      (shiftLift (valleePoussinDerivative d) u t) t := by
  induction u using QuotientAddGroup.induction_on with
  | H u =>
    have hi : HasDerivAt (fun y : ℝ => y - u) (1 : ℝ) t :=
      (hasDerivAt_id t).sub_const u
    have h := (hasDerivAt_valleePoussin d (t - u)).scomp t hi
    simpa only [shiftLift, Function.comp_def, AddCircle.coe_sub, one_smul] using h

/-- The normalized Haar integral is exactly the angular integral divided by `2π`. -/
lemma integral_shiftLift_norm (f : C(Torus, ℂ)) (u : Torus) :
    (∫ t in (0 : ℝ)..2 * Real.pi, ‖shiftLift f u t‖) =
      (2 * Real.pi) * ∫ x : Torus, ‖f x‖ ∂haar := by
  have h := AddCircle.intervalIntegral_preimage (2 * Real.pi) 0
    (fun x : Torus => ‖f (x - u)‖)
  simp only [zero_add] at h
  unfold shiftLift
  rw [h, AddCircle.volume_eq_smul_haarAddCircle, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  congr 1
  exact integral_sub_right_eq_self (μ := haar) (fun x : Torus => ‖f x‖) u

/-- The left side of equation (3.6), with its actual closed angular cells. -/
def kernelGridSup (d m : ℕ) (u : Torus) : ℝ :=
  ((Real.pi / m) / (2 * Real.pi)) *
    ∑ j ∈ Finset.range (2 * m),
      intervalSup (shiftLift (valleePoussin d) u)
        (j * (Real.pi / m)) ((j + 1) * (Real.pi / m))

/-- Equation (3.6), uniformly in the torus shift, with an explicit constant. -/
theorem kernelGridSup_le (d m : ℕ) (hd : 1 ≤ d) (hm : d ≤ m) (u : Torus) :
    kernelGridSup d m u ≤ 3 + 10 * Real.pi := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have h := grid_intervalSup_le (continuous_shiftLift (valleePoussin d) u)
    (continuous_shiftLift (valleePoussinDerivative d) u)
    (hasDerivAt_shiftLift_valleePoussin d u) (2 * m)
    (show 0 ≤ Real.pi / m by positivity)
  have hperiod : ((2 * m : ℕ) : ℝ) * (Real.pi / m) = 2 * Real.pi := by
    push_cast
    field_simp
  rw [hperiod, integral_shiftLift_norm, integral_shiftLift_norm] at h
  have hL1 := valleePoussin_L1 d hd
  have hD := valleePoussinDerivative_L1 d hd
  have hdm : (d : ℝ) ≤ m := by exact_mod_cast hm
  have hhd : (Real.pi / m) * d ≤ Real.pi := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hmpos).2
    nlinarith [mul_le_mul_of_nonneg_left hdm Real.pi_pos.le]
  unfold kernelGridSup
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (show 0 < 2 * Real.pi by positivity)).2
  nlinarith [mul_le_mul_of_nonneg_left hL1 (show 0 ≤ 2 * Real.pi by positivity),
    mul_le_mul_of_nonneg_left hD (show 0 ≤ (Real.pi / m) * (2 * Real.pi) by positivity),
    mul_le_mul_of_nonneg_left hhd (show 0 ≤ 20 * Real.pi by positivity)]

end Paper34.LocalSupremum
