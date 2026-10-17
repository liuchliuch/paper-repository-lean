import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic
import GeometricMedianCoresets.FeatureMap

/-! The actual indicator feature map on the real line, used in Corollary 4.2. -/
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
namespace GeometricMedianCoresets.RealFeature

/-- The signed interval between zero and `a`, as an ordinary measurable function. -/
def step (a : ℝ) : ℝ → ℝ :=
  (Ioc 0 a).indicator (fun _ => 1) - (Ioc a 0).indicator (fun _ => 1)

theorem step_halfline (a t : ℝ) :
    step a t = (if t ≤ a then 1 else 0) - (if t ≤ 0 then 1 else 0) := by
  unfold step
  simp only [Pi.sub_apply, Set.indicator_apply, Set.mem_Ioc]
  split_ifs <;> simp_all <;> linarith

theorem step_memLp (a : ℝ) : MemLp (step a) 2 volume := by
  exact (memLp_indicator_const 2 measurableSet_Ioc (1:ℝ)
    (Or.inr measure_Ioc_lt_top.ne)).sub
      (memLp_indicator_const 2 measurableSet_Ioc (1:ℝ) (Or.inr measure_Ioc_lt_top.ne))

/-- The map `ψ(a)(t) = 1_{t≤a} - 1_{t≤0}` in the actual Lebesgue L2 space. -/
def ψ (a : ℝ) : Lp ℝ 2 (volume : Measure ℝ) := (step_memLp a).toLp (step a)

theorem step_sub_sq (a b t : ℝ) :
    (step a t - step b t) ^ 2 = (uIoc a b).indicator (fun _ => (1:ℝ)) t := by
  rw [step_halfline, step_halfline]
  rcases le_total a b with hab | hba
  · rw [uIoc_of_le hab]
    simp only [Set.indicator_apply, Set.mem_Ioc]
    split_ifs <;> simp_all <;> linarith
  · rw [uIoc_of_ge hba]
    simp only [Set.indicator_apply, Set.mem_Ioc]
    split_ifs <;> simp_all <;> linarith

/-- The exact squared-Hilbert identity for real distance. -/
theorem norm_sub_sq (a b : ℝ) : ‖ψ a - ψ b‖ ^ 2 = |a - b| := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  have heq : (fun t => ⟪(ψ a - ψ b) t, (ψ a - ψ b) t⟫) =ᵐ[volume]
      (uIoc a b).indicator (fun _ => (1:ℝ)) := by
    filter_upwards [Lp.coeFn_sub (ψ a) (ψ b), (step_memLp a).coeFn_toLp,
      (step_memLp b).coeFn_toLp] with t hs ha hb
    change (ψ a) t = step a t at ha
    change (ψ b) t = step b t at hb
    rw [hs]
    change ((ψ a) t - (ψ b) t) * ((ψ a) t - (ψ b) t) = _
    rw [ha, hb, ← pow_two, step_sub_sq]
  rw [integral_congr_ae heq, integral_indicator measurableSet_uIoc, setIntegral_const]
  simp only [smul_eq_mul, mul_one]
  rcases le_total a b with hab | hba
  · rw [uIoc_of_le hab, Real.volume_real_Ioc_of_le hab, abs_of_nonpos (sub_nonpos.2 hab)]
    ring
  · rw [uIoc_of_ge hba, Real.volume_real_Ioc_of_le hba, abs_of_nonneg (sub_nonneg.2 hba)]

/-- A genuine squared-feature metric instance on all real candidate points. -/
def squaredMetric : SquaredMetric ℝ where
  H := Lp ℝ 2 (volume : Measure ℝ)
  d a b := |a - b|
  Φ := ψ
  dist_sq := norm_sub_sq
  triangle a b c := by
    simpa only [sub_add_sub_cancel] using abs_add_le (a - c) (c - b)

end GeometricMedianCoresets.RealFeature
