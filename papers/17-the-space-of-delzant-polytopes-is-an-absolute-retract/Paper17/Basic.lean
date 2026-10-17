import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Analysis.Convex.Hull
import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Positive convex bodies and Hausdorff geometry (paper §2)

We work in `V n = Fin n → ℝ`.  A *positive convex body* is a nonempty compact
convex set with nonempty interior (`𝒞_p(n)` in the paper).

Equation (2.1) identifies the Hausdorff metric with the sup-norm of the
difference of support functions and gives Minkowski-linearity of `h`.
Equation (2.2) is the convex-combination error estimate used later to keep the
boundary error of the extension independent of the number of labels.
-/

noncomputable section

open scoped Pointwise Topology BigOperators

namespace Paper17

/-! ## Ambient space -/

/-- The ambient space `ℝ^n` as a Pi type, with the standard Euclidean inner product. -/
abbrev V (n : ℕ) : Type := Fin n → ℝ

/-- Euclidean inner product on `V n`. -/
def dot {n : ℕ} (u x : V n) : ℝ := ∑ i, u i * x i

@[simp]
theorem dot_apply {n : ℕ} (u x : V n) : dot u x = ∑ i, u i * x i := rfl

theorem dot_comm {n : ℕ} (u x : V n) : dot u x = dot x u := by
  unfold dot
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem dot_self_nonneg {n : ℕ} (u : V n) : 0 ≤ dot u u := by
  unfold dot
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

theorem dot_add_left {n : ℕ} (u v x : V n) : dot (u + v) x = dot u x + dot v x := by
  unfold dot
  simp [add_mul, Finset.sum_add_distrib]

theorem dot_smul_left {n : ℕ} (t : ℝ) (u x : V n) : dot (t • u) x = t * dot u x := by
  unfold dot
  simp [mul_assoc, Finset.mul_sum]

theorem dot_add_right {n : ℕ} (u x y : V n) : dot u (x + y) = dot u x + dot u y := by
  unfold dot
  simp [mul_add, Finset.sum_add_distrib]

theorem dot_smul_right {n : ℕ} (t : ℝ) (u x : V n) : dot u (t • x) = t * dot u x := by
  unfold dot
  simp [mul_left_comm, Finset.mul_sum]

theorem continuous_dot {n : ℕ} (u : V n) : Continuous (fun x : V n => dot u x) := by
  unfold dot
  exact continuous_finset_sum _ fun i _ => continuous_const.mul (continuous_apply i)

/-! ## Positive convex bodies -/

/-- A positive convex body: compact convex, nonempty, with nonempty interior.
This is the paper's `𝒞_p(n)`. -/
structure PosBody (n : ℕ) where
  /-- underlying set -/
  carrier : Set (V n)
  /-- convexity -/
  convex' : Convex ℝ carrier
  /-- compactness -/
  isCompact' : IsCompact carrier
  /-- nonempty interior -/
  interior_nonempty' : (interior carrier).Nonempty

namespace PosBody

variable {n : ℕ}

instance : SetLike (PosBody n) (V n) where
  coe := carrier
  coe_injective' K L h := by
    cases K; cases L; congr

@[ext]
theorem ext {K L : PosBody n} (h : (K : Set (V n)) = L) : K = L :=
  SetLike.ext' h

theorem convex (K : PosBody n) : Convex ℝ (K : Set (V n)) := K.convex'
theorem isCompact (K : PosBody n) : IsCompact (K : Set (V n)) := K.isCompact'
theorem nonempty (K : PosBody n) : (K : Set (V n)).Nonempty := by
  obtain ⟨x, hx⟩ := K.interior_nonempty'
  exact ⟨x, interior_subset hx⟩
theorem interior_nonempty (K : PosBody n) : (interior (K : Set (V n))).Nonempty :=
  K.interior_nonempty'
theorem isClosed (K : PosBody n) : IsClosed (K : Set (V n)) := K.isCompact.isClosed

/-- A closed ball of positive radius is a positive body. -/
def ball (x : V n) {r : ℝ} (hr : 0 < r) : PosBody n where
  carrier := Metric.closedBall x r
  convex' := convex_closedBall x r
  isCompact' := isCompact_closedBall x r
  interior_nonempty' := by
    refine ⟨x, ?_⟩
    have h : Metric.ball x r ⊆ interior (Metric.closedBall x r) :=
      interior_maximal Metric.ball_subset_closedBall Metric.isOpen_ball
    exact h (Metric.mem_ball_self hr)

/-- Minkowski sum of two positive bodies. -/
def add (K L : PosBody n) : PosBody n where
  carrier := (K : Set (V n)) + L
  convex' := K.convex.add L.convex
  isCompact' := K.isCompact.add L.isCompact
  interior_nonempty' := by
    obtain ⟨x, hx⟩ := K.interior_nonempty
    obtain ⟨y, hy⟩ := L.nonempty
    exact ⟨x + y, subset_interior_add_left (Set.add_mem_add hx hy)⟩

/-- Dilation `t • K` for `t ≠ 0`. -/
def smul (t : ℝ) (ht : t ≠ 0) (K : PosBody n) : PosBody n where
  carrier := t • (K : Set (V n))
  convex' := K.convex.smul t
  isCompact' := K.isCompact.smul t
  interior_nonempty' := by
    obtain ⟨x, hx⟩ := K.interior_nonempty'
    have h : interior (t • (K : Set (V n))) = t • interior (K : Set (V n)) :=
      interior_smul₀ ht _
    rw [h]
    exact ⟨t • x, Set.smul_mem_smul_set hx⟩

end PosBody

/-! ## Support functions -/

/-- The support function `h_K(u) = max_{x ∈ K} ⟨u, x⟩`. -/
def supportFunction {n : ℕ} (K : Set (V n)) (u : V n) : ℝ :=
  sSup (Set.image (fun x => dot u x) K)

theorem supportFunction_def {n : ℕ} (K : Set (V n)) (u : V n) :
    supportFunction K u = sSup (Set.image (fun x => dot u x) K) := rfl

/-- Support function of a nonempty compact set is attained. -/
theorem exists_mem_eq_supportFunction {n : ℕ} {K : Set (V n)}
    (hK : IsCompact K) (hne : K.Nonempty) (u : V n) :
    ∃ x ∈ K, supportFunction K u = dot u x := by
  obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hne (continuous_dot u).continuousOn
  refine ⟨x, hx, ?_⟩
  have hbdd : BddAbove ((fun y => dot u y) '' K) :=
    hK.bddAbove_image (continuous_dot u).continuousOn
  have hmem : (fun y => dot u y) x ∈ (fun y => dot u y) '' K := ⟨x, hx, rfl⟩
  have hne' : ((fun y => dot u y) '' K).Nonempty := ⟨_, hmem⟩
  apply le_antisymm
  · exact csSup_le hne' fun b hb => by
      obtain ⟨y, hy, rfl⟩ := hb
      exact hmax hy
  · exact le_csSup hbdd hmem

/-- Every point of `K` realizes a value at most `h_K(u)`. -/
theorem supportFunction_ub {n : ℕ} {K : Set (V n)}
    (hK : IsCompact K) {u x : V n} (hx : x ∈ K) : dot u x ≤ supportFunction K u := by
  have hbdd : BddAbove (Set.image (fun y => dot u y) K) :=
    hK.bddAbove_image (continuous_dot u).continuousOn
  have hmem : dot u x ∈ Set.image (fun y => dot u y) K := ⟨x, hx, rfl⟩
  unfold supportFunction
  exact le_csSup hbdd hmem

/-- `h_{t K} = t h_K` for `t ≥ 0`. -/
theorem supportFunction_smul {n : ℕ} {K : Set (V n)}
    (hK : IsCompact K) (hneK : K.Nonempty) {t : ℝ} (ht : 0 ≤ t) (u : V n) :
    supportFunction (t • K) u = t * supportFunction K u := by
  have hmap : (fun x => dot u x) '' (t • K) = t • ((fun y => dot u y) '' K) := by
    ext r
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.1 hx
      refine ⟨dot u y, ⟨y, hy, rfl⟩, ?_⟩
      show (t : ℝ) * dot u y = dot u (t • y)
      rw [dot_smul_right]
    · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨t • y, Set.smul_mem_smul_set hy, ?_⟩
      show dot u (t • y) = (t : ℝ) * dot u y
      rw [dot_smul_right]
  unfold supportFunction
  rw [hmap, Real.sSup_smul_of_nonneg ht, smul_eq_mul]

/-- `h_{K + L} = h_K + h_L` (Minkowski sum). -/
theorem supportFunction_add {n : ℕ} {K L : Set (V n)}
    (hK : IsCompact K) (hneK : K.Nonempty) (hL : IsCompact L) (hneL : L.Nonempty)
    (u : V n) :
    supportFunction (K + L) u = supportFunction K u + supportFunction L u := by
  have hmap : (fun x => dot u x) '' (K + L)
      = ((fun x => dot u x) '' K) + ((fun x => dot u x) '' L) := by
    ext r
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.1 hx
      exact ⟨dot u a, ⟨a, ha, rfl⟩, dot u b, ⟨b, hb, rfl⟩, (dot_add_right u a b).symm⟩
    · rintro ⟨r1, hr1, r2, hr2, rfl⟩
      obtain ⟨a, ha, rfl⟩ := hr1
      obtain ⟨b, hb, rfl⟩ := hr2
      exact ⟨a + b, Set.mem_add.2 ⟨a, ha, b, hb, rfl⟩, dot_add_right u a b⟩
  unfold supportFunction
  rw [hmap]
  exact csSup_add (hneK.image _) (hK.bddAbove_image (continuous_dot u).continuousOn)
    (hneL.image _) (hL.bddAbove_image (continuous_dot u).continuousOn)

/-- Equation (2.1): `h_{α K + β L} = α h_K + β h_L` for `α, β ≥ 0`. -/
theorem supportFunction_minkowski {n : ℕ} {K L : Set (V n)}
    (hK : IsCompact K) (hneK : K.Nonempty) (hL : IsCompact L) (hneL : L.Nonempty)
    (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (u : V n) :
    supportFunction (α • K + β • L) u
      = α * supportFunction K u + β * supportFunction L u := by
  rw [supportFunction_add (hK.smul α) hneK.smul_set (hL.smul β) hneL.smul_set u,
    supportFunction_smul hK hneK hα u, supportFunction_smul hL hneL hβ u]

/-! ## Hausdorff metric -/

/-- Convex combinations are nonexpansive for `dist`:
`dist (∑ wᵢ xᵢ) (∑ wᵢ yᵢ) ≤ ∑ wᵢ dist xᵢ yᵢ`. -/
theorem dist_sum_smul_le {n : ℕ} {ι : Type*} (s : Finset ι) (w : ι → ℝ) (x y : ι → V n)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    dist (∑ i ∈ s, w i • x i) (∑ i ∈ s, w i • y i) ≤ ∑ i ∈ s, w i * dist (x i) (y i) := by
  have h0 : 0 ≤ ∑ i ∈ s, w i * dist (x i) (y i) :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) dist_nonneg
  rw [dist_pi_le_iff h0]
  intro b
  have hx : (∑ i ∈ s, w i • x i) b = ∑ i ∈ s, w i * x i b := by
    simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hy : (∑ i ∈ s, w i • y i) b = ∑ i ∈ s, w i * y i b := by
    simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hx, hy, Real.dist_eq]
  calc |∑ i ∈ s, w i * x i b - ∑ i ∈ s, w i * y i b|
      = |∑ i ∈ s, (w i * x i b - w i * y i b)| := by rw [← Finset.sum_sub_distrib]
    _ = |∑ i ∈ s, w i * (x i b - y i b)| := by
      congr 1
      exact Finset.sum_congr rfl fun i _ => (mul_sub _ _ _).symm
    _ ≤ ∑ i ∈ s, |w i * (x i b - y i b)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ s, w i * |x i b - y i b| := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [abs_mul, abs_of_nonneg (hw i hi)]
    _ ≤ ∑ i ∈ s, w i * dist (x i) (y i) := by
      refine Finset.sum_le_sum fun i hi => ?_
      refine mul_le_mul_of_nonneg_left ?_ (hw i hi)
      rw [← Real.dist_eq]
      exact (dist_pi_le_iff dist_nonneg).mp le_rfl b

/-- Two-term nonexpansiveness of convex combinations. -/
theorem dist_smul_add_le {n : ℕ} {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (a c b d : V n) :
    dist (s • a + t • b) (s • c + t • d) ≤ s * dist a c + t * dist b d := by
  have h0 : 0 ≤ s * dist a c + t * dist b d :=
    add_nonneg (mul_nonneg hs dist_nonneg) (mul_nonneg ht dist_nonneg)
  rw [dist_pi_le_iff h0]
  intro i
  calc dist ((s • a + t • b) i) ((s • c + t • d) i)
      = |(s • a + t • b) i - (s • c + t • d) i| := Real.dist_eq _ _
    _ = |s * a i + t * b i - (s * c i + t * d i)| := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    _ = |s * (a i - c i) + t * (b i - d i)| := by congr 1; ring
    _ ≤ |s * (a i - c i)| + |t * (b i - d i)| := abs_add_le _ _
    _ = s * |a i - c i| + t * |b i - d i| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]
    _ ≤ s * dist a c + t * dist b d := by
      refine add_le_add (mul_le_mul_of_nonneg_left ?_ hs)
        (mul_le_mul_of_nonneg_left ?_ ht)
      · rw [← Real.dist_eq]; exact (dist_pi_le_iff dist_nonneg).mp le_rfl i
      · rw [← Real.dist_eq]; exact (dist_pi_le_iff dist_nonneg).mp le_rfl i

/-- Equation (2.2): the Hausdorff distance of a Minkowski convex combination
to a target is at most the largest distance of the summands.  Independent of
the number of summands — this is the boundary estimate of §1.
Convexity of `K` is essential (without it the convex combination of nearest
points need not lie in `K`). -/
theorem hausdorffDist_minkowskiComb_le_max {n : ℕ} {K : Set (V n)}
    (hK : IsCompact K) (hneK : K.Nonempty) (hconvK : Convex ℝ K)
    (ι : Type*) (s : Finset ι) (w : ι → ℝ) (P : ι → Set (V n))
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1)
    (hP : ∀ i ∈ s, IsCompact (P i) ∧ (P i).Nonempty)
    {δ : ℝ} (hδ : ∀ i ∈ s, Metric.hausdorffDist (P i) K ≤ δ) :
    Metric.hausdorffDist ((∑ i ∈ s, (w i) • (P i : Set (V n)) : Set (V n))) K ≤ δ := by
  classical
  have hsne : s.Nonempty := by
    by_contra h
    simp [Finset.not_nonempty_iff_eq_empty.1 h] at hsum
  have hδ0 : 0 ≤ δ := by
    obtain ⟨i0, hi0⟩ := hsne
    exact le_trans Metric.hausdorffDist_nonneg (hδ i0 hi0)
  refine Metric.hausdorffDist_le_of_mem_dist hδ0 ?_ ?_
  · -- Every point of S = ∑ wᵢ • Pᵢ is within δ of some point of K.
    intro x hx
    have hx' : x ∈ ∑ i ∈ s, (w i) • (P i : Set (V n)) := hx
    rw [Set.mem_finset_sum] at hx'
    obtain ⟨g, hg, hgsum⟩ := hx'
    have hex : ∀ i : ι, ∃ p, (i ∈ s → p ∈ P i) ∧ (i ∈ s → g i = w i • p) := by
      intro i
      by_cases hi : i ∈ s
      · obtain ⟨p, hp, hgip⟩ := Set.mem_smul_set.1 (hg (i := i) hi)
        exact ⟨p, fun _ => hp, fun _ => hgip.symm⟩
      · exact ⟨0, fun h => absurd h hi, fun h => absurd h hi⟩
    choose p hp hgp using hex
    have hnear : ∀ i : ι, ∃ y, (i ∈ s → y ∈ K) ∧ (i ∈ s → dist (p i) y ≤ δ) := by
      intro i
      by_cases hi : i ∈ s
      · obtain ⟨y, hy, hyd⟩ := hK.exists_infDist_eq_dist hneK (p i)
        refine ⟨y, fun _ => hy, fun _ => ?_⟩
        rw [← hyd]
        have hfin : EMetric.hausdorffEdist (P i) K ≠ ⊤ :=
          Metric.hausdorffEdist_ne_top_of_nonempty_of_bounded (hP i hi).2 hneK
            (hP i hi).1.isBounded hK.isBounded
        exact le_trans (Metric.infDist_le_hausdorffDist_of_mem (hp i hi) hfin) (hδ i hi)
      · exact ⟨0, fun h => absurd h hi, fun h => absurd h hi⟩
    choose y hy hdy using hnear
    refine ⟨∑ i ∈ s, w i • y i, hconvK.sum_mem hw hsum (fun i hi => hy i hi), ?_⟩
    have hrew : x = ∑ i ∈ s, w i • p i := by
      rw [← hgsum]
      exact Finset.sum_congr rfl fun i hi => hgp i hi
    rw [hrew]
    refine le_trans (dist_sum_smul_le s w p y (fun i hi => hw i hi)) ?_
    refine le_trans (Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_left (hdy i hi) (hw i hi)) ?_
    rw [← Finset.sum_mul, hsum, one_mul]
  · -- Every point of K is within δ of some point of S.
    intro y hy
    have hy' : y = ∑ i ∈ s, w i • y := by
      rw [← Finset.sum_smul, hsum, one_smul]
    have hnear : ∀ i : ι, ∃ x, (i ∈ s → x ∈ P i) ∧ (i ∈ s → dist y x ≤ δ) := by
      intro i
      by_cases hi : i ∈ s
      · obtain ⟨x, hx, hxd⟩ := (hP i hi).1.exists_infDist_eq_dist (hP i hi).2 y
        refine ⟨x, fun _ => hx, fun _ => ?_⟩
        rw [← hxd]
        have hfin : EMetric.hausdorffEdist K (P i) ≠ ⊤ :=
          Metric.hausdorffEdist_ne_top_of_nonempty_of_bounded hneK (hP i hi).2
            hK.isBounded (hP i hi).1.isBounded
        calc Metric.infDist y (P i) ≤ Metric.hausdorffDist K (P i) :=
               Metric.infDist_le_hausdorffDist_of_mem hy hfin
             _ = Metric.hausdorffDist (P i) K := Metric.hausdorffDist_comm
             _ ≤ δ := hδ i hi
      · exact ⟨0, fun h => absurd h hi, fun h => absurd h hi⟩
    choose x hx hdx using hnear
    refine ⟨∑ i ∈ s, w i • x i, ?_, ?_⟩
    · rw [Set.mem_finset_sum]
      refine ⟨fun i => w i • x i, ?_, rfl⟩
      intro i hi
      exact Set.smul_mem_smul_set (hx i hi)
    · rw [hy']
      refine le_trans (dist_sum_smul_le s w (fun _ => y) x (fun i hi => hw i hi)) ?_
      refine le_trans (Finset.sum_le_sum fun i hi =>
        mul_le_mul_of_nonneg_left (hdx i hi) (hw i hi)) ?_
      rw [← Finset.sum_mul, hsum, one_mul]

/-- Two-term form of (2.2): the weighted-average estimate.
Convexity of `K` is essential. -/
theorem hausdorffDist_smul_add_le {n : ℕ} {K P Q : Set (V n)}
    (hK : IsCompact K) (hneK : K.Nonempty) (hconvK : Convex ℝ K)
    (hP : IsCompact P) (hneP : P.Nonempty) (hQ : IsCompact Q) (hneQ : Q.Nonempty)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) :
    Metric.hausdorffDist (s • P + t • Q) K
      ≤ s * Metric.hausdorffDist P K + t * Metric.hausdorffDist Q K := by
  have hδ0 : 0 ≤ s * Metric.hausdorffDist P K + t * Metric.hausdorffDist Q K :=
    add_nonneg (mul_nonneg hs Metric.hausdorffDist_nonneg)
      (mul_nonneg ht Metric.hausdorffDist_nonneg)
  refine Metric.hausdorffDist_le_of_mem_dist hδ0 ?_ ?_
  · intro x hx
    obtain ⟨xp, hxp, xq, hxq, rfl⟩ := Set.mem_add.1 hx
    obtain ⟨yp, hyp, rfl⟩ := Set.mem_smul_set.1 hxp
    obtain ⟨yq, hyq, rfl⟩ := Set.mem_smul_set.1 hxq
    obtain ⟨kp, hkp, hkpdist⟩ := hK.exists_infDist_eq_dist hneK yp
    obtain ⟨kq, hkq, hkqdist⟩ := hK.exists_infDist_eq_dist hneK yq
    have hmemK : s • kp + t • kq ∈ K := by
      have h := hconvK.sum_mem (t := ({0, 1} : Finset (Fin 2)))
        (w := fun i : Fin 2 => if i = 0 then s else t)
        (z := fun i : Fin 2 => if i = 0 then kp else kq)
        (fun i hi => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hi
          rcases hi with rfl | rfl <;> simp [hs, ht])
        (by
          rw [Finset.sum_pair (by decide : (0 : Fin 2) ≠ 1)]
          simp [hst])
        (fun i hi => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hi
          rcases hi with rfl | rfl <;> simp [hkp, hkq])
      rw [Finset.sum_pair (by decide : (0 : Fin 2) ≠ 1)] at h
      simpa using h
    refine ⟨s • kp + t • kq, hmemK, ?_⟩
    have hdistP : dist yp kp ≤ Metric.hausdorffDist P K := by
      rw [← hkpdist]
      exact Metric.infDist_le_hausdorffDist_of_mem hyp
        (Metric.hausdorffEdist_ne_top_of_nonempty_of_bounded hneP hneK hP.isBounded hK.isBounded)
    have hdistQ : dist yq kq ≤ Metric.hausdorffDist Q K := by
      rw [← hkqdist]
      exact Metric.infDist_le_hausdorffDist_of_mem hyq
        (Metric.hausdorffEdist_ne_top_of_nonempty_of_bounded hneQ hneK hQ.isBounded hK.isBounded)
    refine le_trans (dist_smul_add_le hs ht yp kp yq kq) ?_
    exact add_le_add (mul_le_mul_of_nonneg_left hdistP hs)
      (mul_le_mul_of_nonneg_left hdistQ ht)
  · intro y hy
    have hy' : y = s • y + t • y := by
      rw [← add_smul, hst, one_smul]
    obtain ⟨kp, hkp, hkpdist⟩ := hP.exists_infDist_eq_dist hneP y
    obtain ⟨kq, hkq, hkqdist⟩ := hQ.exists_infDist_eq_dist hneQ y
    refine ⟨s • kp + t • kq, ?_, ?_⟩
    · rw [Set.mem_add]
      exact ⟨s • kp, Set.smul_mem_smul_set hkp, t • kq, Set.smul_mem_smul_set hkq, rfl⟩
    · rw [hy']
      have hdistP : dist y kp ≤ Metric.hausdorffDist P K := by
        rw [← hkpdist, (Metric.hausdorffDist_comm (s := P) (t := K))]
        exact Metric.infDist_le_hausdorffDist_of_mem hy
          (Metric.hausdorffEdist_ne_top_of_nonempty_of_bounded hneK hneP hK.isBounded hP.isBounded)
      have hdistQ : dist y kq ≤ Metric.hausdorffDist Q K := by
        rw [← hkqdist, (Metric.hausdorffDist_comm (s := Q) (t := K))]
        exact Metric.infDist_le_hausdorffDist_of_mem hy
          (Metric.hausdorffEdist_ne_top_of_nonempty_of_bounded hneK hneQ hK.isBounded hQ.isBounded)
      refine le_trans (dist_smul_add_le hs ht y kp y kq) ?_
      exact add_le_add (mul_le_mul_of_nonneg_left hdistP hs)
        (mul_le_mul_of_nonneg_left hdistQ ht)

/-- Hausdorff balls in `𝒞_p(n)` are convex in support-function coordinates. -/
theorem hausdorffBall_convex {n : ℕ} {K : Set (V n)}
    (hK : IsCompact K) (hneK : K.Nonempty) (hconvK : Convex ℝ K)
    {δ : ℝ} (hδ : 0 < δ) :
    Convex ℝ {L : Set (V n) | IsCompact L ∧ L.Nonempty ∧ Metric.hausdorffDist L K < δ} := by
  intro P hP Q hQ s t hs ht hst
  refine ⟨(hP.1.smul s).add (hQ.1.smul t),
    hP.2.1.smul_set.add hQ.2.1.smul_set, ?_⟩
  have hbound := hausdorffDist_smul_add_le hK hneK hconvK
    hP.1 hP.2.1 hQ.1 hQ.2.1 hs ht hst
  have herr : s * Metric.hausdorffDist P K + t * Metric.hausdorffDist Q K < δ := by
    have heq : s * δ + t * δ = δ := by rw [← add_mul, hst, one_mul]
    rcases eq_or_lt_of_le hs with rfl | hs'
    · simp only [zero_add] at hst
      simpa [hst] using hQ.2.2
    · calc s * Metric.hausdorffDist P K + t * Metric.hausdorffDist Q K
          < s * δ + t * δ := add_lt_add_of_lt_of_le
            (mul_lt_mul_of_pos_left hP.2.2 hs')
            (mul_le_mul_of_nonneg_left hQ.2.2.le ht)
           _ = δ := heq
  exact hbound.trans_lt herr

end Paper17
