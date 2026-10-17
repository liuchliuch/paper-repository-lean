import BoundaryReduction.Pinsker
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Topology.Algebra.Module.FiniteDimension

open Real Set BigOperators Filter
open scoped Classical
namespace BoundaryReduction.FiniteExponential

variable {α : Type*} [Fintype α] [Nonempty α] {d : ℕ}
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)
variable (p : FinProb α) (hp : ∀ y, 0 < p.w y) (Y : α → E d)

noncomputable def partition (θ : E d) : ℝ := ∑ y, p.w y*exp (inner ℝ θ (Y y))

include hp

lemma partition_pos (θ : E d) : 0 < partition p Y θ :=
  Finset.sum_pos (fun y _ => mul_pos (hp y) (exp_pos _)) Finset.univ_nonempty

noncomputable def tilt (θ : E d) : FinProb α where
  w := fun y => p.w y*exp (inner ℝ θ (Y y))/partition p Y θ
  nonneg := fun y => (div_pos (mul_pos (hp y) (exp_pos _)) (partition_pos p hp Y θ)).le
  sum_eq_one := by
    rw [← Finset.sum_div]
    exact div_self (partition_pos p hp Y θ).ne'

lemma tilt_pos (θ : E d) (y : α) : 0 < (tilt p hp Y θ).w y :=
  div_pos (mul_pos (hp y) (exp_pos _)) (partition_pos p hp Y θ)

noncomputable def mean (θ : E d) : E d := ∑ y, (tilt p hp Y θ).w y • Y y

noncomputable def ratio (v : α) (n : E d) (t : ℝ) (y : α) : ℝ :=
  (p.w y/p.w v)*exp (t*(inner ℝ n (Y y)-inner ℝ n (Y v)))

lemma ratio_self (v : α) (n : E d) (t : ℝ) : ratio p Y v n t v = 1 := by
  simp [ratio,div_self (hp v).ne']

lemma ratio_pos (v : α) (n : E d) (t : ℝ) (y : α) : 0 < ratio p Y v n t y :=
  mul_pos (div_pos (hp y) (hp v)) (exp_pos _)

lemma tilt_as_ratio (v : α) (n : E d) (t : ℝ) (y : α) :
    (tilt p hp Y (t • n)).w y = ratio p Y v n t y/(∑ z, ratio p Y v n t z) := by
  have heq (z : α) : ratio p Y v n t z =
      (p.w z*exp (inner ℝ (t • n) (Y z)))/(p.w v*exp (inner ℝ (t • n) (Y v))) := by
    simp only [ratio,real_inner_smul_left]
    rw [show t*(inner ℝ n (Y z)-inner ℝ n (Y v)) =
      t*inner ℝ n (Y z)-t*inner ℝ n (Y v) by ring,exp_sub]
    field_simp
  simp_rw [heq]
  rw [← Finset.sum_div]
  change _/partition p Y (t • n) = (_/_)/(partition p Y (t • n)/_)
  field_simp [(partition_pos p hp Y (t • n)).ne', (hp v).ne']

/-- An exposed natural tilt tends pointwise to the point mass at its exposed vertex. -/
theorem tilt_tendsto_vertex (v : α) (n : E d)
    (hexpose : ∀ y, y ≠ v → inner ℝ n (Y y) < inner ℝ n (Y v)) (y : α) :
    Tendsto (fun t : ℝ => (tilt p hp Y (t • n)).w y) atTop (nhds (if y = v then 1 else 0)) := by
  have hr (z : α) : Tendsto (fun t : ℝ => ratio p Y v n t z) atTop (nhds (if z = v then 1 else 0)) := by
    by_cases hz : z = v
    · subst z
      simpa only [ratio_self p hp,if_pos rfl] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1:ℝ)) atTop (nhds 1))
    · have hn : inner ℝ n (Y z)-inner ℝ n (Y v) < 0 := sub_neg.mpr (hexpose z hz)
      have he := Real.tendsto_exp_atBot.comp (tendsto_id.atTop_mul_const_of_neg hn)
      simpa only [ratio,if_neg hz,mul_zero] using he.const_mul (p.w z/p.w v)
  have hs : Tendsto (fun t : ℝ => ∑ z, ratio p Y v n t z) atTop (nhds 1) := by
    simpa using tendsto_finset_sum Finset.univ (fun z _ => hr z)
  have hh := (hr y).div hs (by norm_num : (1:ℝ) ≠ 0)
  simpa only [tilt_as_ratio p hp Y v n,div_one] using hh

/-- The means of the same tilts converge to the exposed vertex. -/
theorem mean_tendsto_vertex (v : α) (n : E d)
    (hexpose : ∀ y, y ≠ v → inner ℝ n (Y y) < inner ℝ n (Y v)) :
    Tendsto (fun t : ℝ => mean p hp Y (t • n)) atTop (nhds (Y v)) := by
  have h := tendsto_finset_sum Finset.univ (fun y _ =>
    (tilt_tendsto_vertex p hp Y v n hexpose y).smul_const (Y y))
  simpa [mean] using h

end BoundaryReduction.FiniteExponential
