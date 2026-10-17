import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic

/-! Explicit strong Lipschitz contraction estimates for a neighborhood
retraction: spatial constant L and time constant L times diameter(E). -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Metric Set
variable {H Y : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [PseudoMetricSpace Y]

def retractionContraction (r : H → Y) (a : H) (t : ℝ) (x : H) : Y :=
  r ((1-t) • x+t • a)

theorem contraction_segment_mem_ball (p a x : H) (ρ t : ℝ)
    (ha : a ∈ ball p ρ) (hx : x ∈ ball p ρ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1-t) • x+t • a ∈ ball p ρ :=
  convex_ball p ρ hx ha (by linarith) ht0 (by ring)

theorem retractionContraction_spatial (r : H → Y) (U : Set H) (L : NNReal)
    (hLip : LipschitzOnWith L r U) (a x y : H) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : (1-t) • x+t • a ∈ U) (hy : (1-t) • y+t • a ∈ U) :
    dist (retractionContraction r a t x) (retractionContraction r a t y) ≤ (L : ℝ)*dist x y := by
  have he : (1-t) • x+t • a-((1-t) • y+t • a) = (1-t) • (x-y) := by module
  have hdist : dist ((1-t) • x+t • a) ((1-t) • y+t • a) ≤ dist x y := by
    rw [dist_eq_norm,dist_eq_norm,he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by linarith)]
    nlinarith [norm_nonneg (x-y)]
  exact (hLip.dist_le_mul _ hx _ hy).trans (mul_le_mul_of_nonneg_left hdist L.coe_nonneg)

theorem retractionContraction_time (r : H → Y) (U : Set H) (L : NNReal)
    (hLip : LipschitzOnWith L r U) (a x : H) (s t : ℝ) (D : ℝ) (hD : dist x a ≤ D)
    (hs : (1-s) • x+s • a ∈ U) (ht : (1-t) • x+t • a ∈ U) :
    dist (retractionContraction r a s x) (retractionContraction r a t x) ≤
      (L : ℝ)*D*|s-t| := by
  have he : (1-s) • x+s • a-((1-t) • x+t • a) = (s-t) • (a-x) := by module
  have hdist : dist ((1-s) • x+s • a) ((1-t) • x+t • a) ≤ |s-t| * D := by
    rw [dist_eq_norm,he,norm_smul,Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left
    · simpa only [dist_eq_norm,norm_sub_rev] using hD
    · exact abs_nonneg _
  have h := (hLip.dist_le_mul _ hs _ ht).trans (mul_le_mul_of_nonneg_left hdist L.coe_nonneg)
  exact h.trans_eq (by ring)

theorem retractionContraction_time_diameter (r : H → Y) (U E : Set H) (L : NNReal)
    (hLip : LipschitzOnWith L r U) (hE : Bornology.IsBounded E)
    (a x : H) (ha : a ∈ E) (hx : x ∈ E) (s t : ℝ)
    (hs : (1-s) • x+s • a ∈ U) (ht : (1-t) • x+t • a ∈ U) :
    dist (retractionContraction r a s x) (retractionContraction r a t x) ≤
      (L : ℝ)*Metric.diam E*|s-t| :=
  retractionContraction_time r U L hLip a x s t _ (Metric.dist_le_diam_of_mem hE hx ha) hs ht

theorem retractionContraction_endpoints (r : H → H) (a x : H) (ha : r a = a) (hx : r x = x) :
    retractionContraction r a 0 x = x ∧ retractionContraction r a 1 x = a := by
  simp only [retractionContraction,sub_zero,one_smul,zero_smul,add_zero,sub_self,zero_add,ha,hx,and_self]

end Paper28
