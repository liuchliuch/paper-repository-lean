import Paper28.RegularSlices
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! Explicit stabilizer-invariant smooth cutoffs, obtained by finite averaging
of a native Hilbert-space bump. This derives the equivariant chart cutoff
rather than assuming a partition adapted to the relative deformation. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Metric
variable {G : Type*} [Group G] [DecidableEq G]
variable (H : Subgroup G) [Fintype H]

def averagedBump {c : CoordinateHilbert G} (b : ContDiffBump c) (x : CoordinateHilbert G) : ℝ :=
  (Fintype.card H : ℝ)⁻¹ * ∑ h : H, b (leftRegular h.val x)

theorem averagedBump_nonneg {c : CoordinateHilbert G} (b : ContDiffBump c) (x : CoordinateHilbert G) :
    0 ≤ averagedBump H b x :=
  mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg (fun _ _ => b.nonneg))

theorem averagedBump_contDiff {c : CoordinateHilbert G} (b : ContDiffBump c) (n : ℕ∞) :
    ContDiff ℝ n (averagedBump H b) := by
  apply contDiff_const.mul
  exact ContDiff.sum (fun h _ => b.contDiff.comp (leftRegular h.val).toContinuousLinearEquiv.contDiff)

theorem averagedBump_invariant {c : CoordinateHilbert G} (b : ContDiffBump c)
    (k : H) (x : CoordinateHilbert G) : averagedBump H b (leftRegular k.val x) = averagedBump H b x := by
  unfold averagedBump
  congr 1
  calc
    _ = ∑ h : H, b (leftRegular (h*k).val x) := by
      apply Finset.sum_congr rfl
      intro h _
      change b (leftRegular h.val (leftRegular k.val x)) = b (leftRegular (h.val*k.val) x)
      rw [leftRegular_mul]
    _ = _ := Fintype.sum_equiv (Equiv.mulRight k) _ _ (fun _ => rfl)

theorem averagedBump_dist {c : CoordinateHilbert G} (hFix : ∀ h : H, leftRegular h.val c = c)
    (h : H) (x : CoordinateHilbert G) : dist (leftRegular h.val x) c = dist x c := by
  calc
    _ = dist (leftRegular h.val x) (leftRegular h.val c) := by rw [hFix h]
    _ = _ := (leftRegular h.val).isometry.dist_eq x c

theorem averagedBump_one {c : CoordinateHilbert G} (b : ContDiffBump c)
    (hFix : ∀ h : H, leftRegular h.val c = c) (x : CoordinateHilbert G)
    (hx : x ∈ closedBall c b.rIn) : averagedBump H b x = 1 := by
  have he (h : H) : b (leftRegular h.val x) = 1 := by
    apply b.one_of_mem_closedBall
    change dist (leftRegular h.val x) c ≤ b.rIn
    rw [averagedBump_dist H hFix]
    exact hx
  simp only [averagedBump,he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

theorem averagedBump_zero {c : CoordinateHilbert G} (b : ContDiffBump c)
    (hFix : ∀ h : H, leftRegular h.val c = c) (x : CoordinateHilbert G)
    (hx : b.rOut ≤ dist x c) : averagedBump H b x = 0 := by
  have he (h : H) : b (leftRegular h.val x) = 0 := by
    apply b.zero_of_le_dist
    rw [averagedBump_dist H hFix]
    exact hx
  simp only [averagedBump,he,Finset.sum_const_zero,mul_zero]

end Paper28
