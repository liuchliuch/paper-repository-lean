import Paper28.NormalizationGlobalLipschitz
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.Lipschitz

/-! Actual normalized straight arcs in a common hemisphere ball. Clamping
the parameter makes a globally defined Lipschitz unit-sphere map, with the
correct endpoints and preservation of every common coordinate subspace. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set Metric
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

abbrev UnitHilbertVector (H : Type*) [NormedAddCommGroup H] := {u : H // ‖u‖ = 1}

def clampedLinearSphereRaw (x y : H) (t : ℝ) : H :=
  (1-(projIcc (0 : ℝ) 1 (by norm_num) t).val) • x+(projIcc (0 : ℝ) 1 (by norm_num) t).val • y

theorem clampedLinearSphereRaw_norm_lower (u x y : UnitHilbertVector H)
    (hx : ‖x.val-u.val‖ ≤ 1/2) (hy : ‖y.val-u.val‖ ≤ 1/2) (t : ℝ) :
    (1/2 : ℝ) ≤ ‖clampedLinearSphereRaw x.val y.val t‖ := by
  let s := projIcc (0 : ℝ) 1 (by norm_num) t
  have hxb : x.val ∈ closedBall u.val (1/2) := by simpa only [mem_closedBall,dist_eq_norm] using hx
  have hyb : y.val ∈ closedBall u.val (1/2) := by simpa only [mem_closedBall,dist_eq_norm] using hy
  have hb := (convex_closedBall u.val (1/2)) hxb hyb (by linarith [s.property.2] : 0 ≤ 1-s.val)
    s.property.1 (by ring : (1-s.val)+s.val = 1)
  change clampedLinearSphereRaw x.val y.val t ∈ closedBall u.val (1/2) at hb
  simp only [mem_closedBall,dist_eq_norm] at hb
  have hn := norm_sub_norm_le u.val (clampedLinearSphereRaw x.val y.val t)
  rw [u.property,norm_sub_rev] at hn
  linarith

theorem clampedLinearSphereRaw_lipschitz (x y : H) :
    LipschitzWith ‖x-y‖₊ (clampedLinearSphereRaw x y) := by
  have hClamp : LipschitzWith 1 (fun t : ℝ => (projIcc (0 : ℝ) 1 (by norm_num) t).val) := by
    simpa only [one_mul] using isometry_subtype_coe.lipschitz.comp (LipschitzWith.projIcc (by norm_num : (0 : ℝ) ≤ 1))
  apply LipschitzWith.of_dist_le_mul
  intro s t
  have hh := hClamp.dist_le_mul s t
  simp only [NNReal.coe_one,one_mul,Real.dist_eq] at hh
  have he : clampedLinearSphereRaw x y s-clampedLinearSphereRaw x y t =
      ((projIcc (0 : ℝ) 1 (by norm_num) s).val-(projIcc (0 : ℝ) 1 (by norm_num) t).val) • (y-x) := by
    unfold clampedLinearSphereRaw
    module
  rw [dist_eq_norm,he,norm_smul,Real.norm_eq_abs]
  calc
    _ ≤ |s-t| *‖y-x‖ := mul_le_mul_of_nonneg_right hh (norm_nonneg _)
    _ = _ := by rw [norm_sub_rev,Real.dist_eq]; simp only [coe_nnnorm]; ring

def normalizedStraightSphereArc (u x y : UnitHilbertVector H)
    (hx : ‖x.val-u.val‖ ≤ 1/2) (hy : ‖y.val-u.val‖ ≤ 1/2) (t : ℝ) : UnitHilbertVector H :=
  ⟨sphericalNormalize (clampedLinearSphereRaw x.val y.val t),sphericalNormalize_norm _
    (norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) (clampedLinearSphereRaw_norm_lower u x y hx hy t)))⟩

theorem normalizedStraightSphereArc_lipschitz (u x y : UnitHilbertVector H)
    (hx : ‖x.val-u.val‖ ≤ 1/2) (hy : ‖y.val-u.val‖ ≤ 1/2) :
    LipschitzWith (4*‖x.val-y.val‖₊) (normalizedStraightSphereArc u x y hx hy) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  have hn := sphericalNormalize_sub_le_of_lower_norm (clampedLinearSphereRaw x.val y.val s)
    (clampedLinearSphereRaw x.val y.val t) (1/2) (by norm_num)
    (clampedLinearSphereRaw_norm_lower u x y hx hy s) (clampedLinearSphereRaw_norm_lower u x y hx hy t)
  have hh : ‖clampedLinearSphereRaw x.val y.val s-clampedLinearSphereRaw x.val y.val t‖ ≤
      ‖x.val-y.val‖*dist s t := by
    simpa only [dist_eq_norm,coe_nnnorm] using (clampedLinearSphereRaw_lipschitz x.val y.val).dist_le_mul s t
  have hNorm : ‖sphericalNormalize (clampedLinearSphereRaw x.val y.val s)-sphericalNormalize (clampedLinearSphereRaw x.val y.val t)‖ ≤
      (4*‖x.val-y.val‖)*dist s t := by
    calc
      _ ≤ 4*‖clampedLinearSphereRaw x.val y.val s-clampedLinearSphereRaw x.val y.val t‖ := by norm_num at hn ⊢; exact hn
      _ ≤ 4*(‖x.val-y.val‖*dist s t) := mul_le_mul_of_nonneg_left hh (by norm_num)
      _ = _ := by ring
  simpa only [normalizedStraightSphereArc,Subtype.dist_eq,dist_eq_norm,NNReal.coe_mul,NNReal.coe_ofNat,coe_nnnorm] using hNorm

theorem normalizedStraightSphereArc_zero (u x y : UnitHilbertVector H)
    (hx : ‖x.val-u.val‖ ≤ 1/2) (hy : ‖y.val-u.val‖ ≤ 1/2) :
    normalizedStraightSphereArc u x y hx hy 0 = x := by
  apply Subtype.ext
  change sphericalNormalize (clampedLinearSphereRaw x.val y.val 0) = x.val
  simp [clampedLinearSphereRaw,sphericalNormalize_fixed x.val x.property]

theorem normalizedStraightSphereArc_one (u x y : UnitHilbertVector H)
    (hx : ‖x.val-u.val‖ ≤ 1/2) (hy : ‖y.val-u.val‖ ≤ 1/2) :
    normalizedStraightSphereArc u x y hx hy 1 = y := by
  apply Subtype.ext
  change sphericalNormalize (clampedLinearSphereRaw x.val y.val 1) = y.val
  simp [clampedLinearSphereRaw,sphericalNormalize_fixed y.val y.property]

theorem normalizedStraightSphereArc_mem_subspace (u x y : UnitHilbertVector H)
    (hx : ‖x.val-u.val‖ ≤ 1/2) (hy : ‖y.val-u.val‖ ≤ 1/2)
    (S : Submodule ℝ H) (hSx : x.val ∈ S) (hSy : y.val ∈ S) (t : ℝ) :
    (normalizedStraightSphereArc u x y hx hy t).val ∈ S :=
  S.smul_mem _ (S.add_mem (S.smul_mem _ hSx) (S.smul_mem _ hSy))

end Paper28
