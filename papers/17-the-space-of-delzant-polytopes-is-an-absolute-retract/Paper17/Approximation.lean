import Paper17.Basic
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ring

/-!
# Approximation of convex bodies by rational polytopes (paper §4.1, Lemma 4.2)

Analytic stages of Lemma 4.2, proved in full:

1. **Rational approximation** (`exists_ratPolytope_near`): every positive
   convex body `K` admits a full-dimensional rational polytope `R` with
   `d_H(R,K)` arbitrarily small (finite net + rational perturbation; affine
   independence is an open condition).

2. **Minkowski perturbation** (`hausdorffDist_add_smul_le`): if `0 ∈ S` and
   `S` is bounded by `M`, then `d_H(R + t•S, R) ≤ t·M`.

This module is self-contained (minimal local stubs) so that it builds
independently of concurrent edits to `Paper17.Basic` / `Paper17.Polytope`.
-/

noncomputable section

open scoped Pointwise Topology BigOperators

namespace Paper17

/-! ## Rational points -/

/-- A point of `V n` is rational when every coordinate is rational. -/
def IsRatPoint {n : ℕ} (x : V n) : Prop := ∀ i : Fin n, ∃ q : ℚ, x i = q

/-- Rational points are dense in `V n` (sup-norm). -/
theorem exists_ratPoint_near {n : ℕ} (x : V n) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : V n, IsRatPoint y ∧ dist x y < ε := by
  have hcoord : ∀ i : Fin n, ∃ q : ℚ, |x i - (q : ℝ)| < ε := by
    intro i
    obtain ⟨q, h1, h2⟩ := exists_rat_btwn
      (show (x i - ε : ℝ) < x i + ε by linarith)
    exact ⟨q, abs_lt.mpr ⟨by linarith, by linarith⟩⟩
  choose q hq using hcoord
  refine ⟨fun i => (q i : ℝ), fun i => ⟨q i, rfl⟩, ?_⟩
  rw [dist_pi_lt_iff hε]
  intro i
  rw [Real.dist_eq]
  exact hq i

/-- Simultaneous rational approximation of a finite family of points. -/
theorem exists_forall_isRatPoint_near {n k : ℕ} (p : Fin k → V n)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ q : Fin k → V n, (∀ i, IsRatPoint (q i)) ∧ (∀ i, dist (p i) (q i) < δ) := by
  have h : ∀ i : Fin k, ∃ y : V n, IsRatPoint y ∧ dist (p i) y < δ :=
    fun i => exists_ratPoint_near (p i) hδ
  choose q hq using h
  exact ⟨q, fun i => (hq i).1, fun i => (hq i).2⟩

/-! ## Local polytope type -/

/-- A polytope: convex hull of a nonempty finite set of vertices. -/
structure LPolytope (n : ℕ) where
  /-- vertices -/
  verts : Finset (V n)
  /-- nonempty -/
  nonempty_verts' : verts.Nonempty

namespace LPolytope

variable {n : ℕ}

/-- Underlying set. -/
def carrier (P : LPolytope n) : Set (V n) := convexHull ℝ P.verts

theorem isCompact (P : LPolytope n) : IsCompact P.carrier :=
  Set.Finite.isCompact_convexHull P.verts.finite_toSet

theorem nonempty (P : LPolytope n) : P.carrier.Nonempty := by
  obtain ⟨v, hv⟩ := P.nonempty_verts'
  exact ⟨v, subset_convexHull _ _ hv⟩

theorem convex (P : LPolytope n) : Convex ℝ P.carrier :=
  convex_convexHull _ _

/-- Full-dimensional: nonempty interior. -/
def IsFullDim (P : LPolytope n) : Prop := (interior P.carrier).Nonempty

/-- A polytope as a positive body when full-dimensional. -/
def toPosBody (P : LPolytope n) (h : P.IsFullDim) : PosBody n where
  carrier := P.carrier
  convex' := P.convex
  isCompact' := P.isCompact
  interior_nonempty' := h

end LPolytope

/-- A polytope has rational vertices. -/
def IsRatPolytope {n : ℕ} (P : LPolytope n) : Prop := ∀ v ∈ P.verts, IsRatPoint v

/-! ## Finite nets in compact sets -/

/-- Every compact subset of `V n` has a finite `ε`-net consisting of its own points. -/
theorem exists_finite_net {n : ℕ} {K : Set (V n)} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : Finset (V n), (t : Set (V n)) ⊆ K ∧ ∀ x ∈ K, ∃ y ∈ t, dist x y < ε := by
  have htb : TotallyBounded K := hK.totallyBounded
  rw [Metric.totallyBounded_iff] at htb
  obtain ⟨t₀, ht₀fin, hcover⟩ := htb (ε / 2) (by linarith)
  classical
  have hex : ∀ y : V n, ((Metric.ball y (ε / 2)) ∩ K).Nonempty →
      ∃ z : V n, z ∈ K ∧ dist y z < ε / 2 := by
    intro y hy
    obtain ⟨z, hzy, hzK⟩ := hy
    refine ⟨z, hzK, ?_⟩
    rw [dist_comm]
    exact Metric.mem_ball.mp hzy
  set g : V n → V n := fun y =>
    if h : ((Metric.ball y (ε / 2)) ∩ K).Nonempty then Classical.choose (hex y h) else 0
  have hg : ∀ y, ((Metric.ball y (ε / 2)) ∩ K).Nonempty → g y ∈ K ∧ dist y (g y) < ε / 2 := by
    intro y hy
    simp only [g, dif_pos hy]
    exact Classical.choose_spec (hex y hy)
  set centres : Finset (V n) :=
    ht₀fin.toFinset.filter fun y => ((Metric.ball y (ε / 2)) ∩ K).Nonempty
  refine ⟨centres.image g, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hyt, hyK⟩ := Finset.mem_filter.mp hy
    exact (hg y hyK).1
  · intro x hx
    have hx' : x ∈ ⋃ y ∈ (t₀ : Set (V n)), Metric.ball y (ε / 2) := hcover hx
    obtain ⟨y, hyt₀, hxy⟩ : ∃ y ∈ t₀, x ∈ Metric.ball y (ε / 2) := by
      simpa [Set.mem_iUnion] using hx'
    have hyK : ((Metric.ball y (ε / 2)) ∩ K).Nonempty := ⟨x, hxy, hx⟩
    have hyg := hg y hyK
    refine ⟨g y, ?_, ?_⟩
    · apply Finset.mem_image.mpr
      refine ⟨y, ?_, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨?_, hyK⟩
      simpa using hyt₀
    · calc dist x (g y) ≤ dist x y + dist y (g y) := dist_triangle _ _ _
        _ < ε / 2 + ε / 2 := add_lt_add (Metric.mem_ball.mp hxy) hyg.2
        _ = ε := by ring

end Paper17

namespace Paper17

/-! ## Convex hull of a net is close to the body -/

/-- If `t ⊆ K`, `K` is convex, and every point of `K` is within `ε` of `t`, then
the convex hull of `t` is at Hausdorff distance at most `ε` from `K`. -/
theorem hausdorffDist_convexHull_le {n : ℕ} {K : Set (V n)} {t : Finset (V n)}
    (hKc : Convex ℝ K) (ht : (t : Set (V n)) ⊆ K)
    {ε : ℝ} (hε : 0 ≤ ε) (hnet : ∀ x ∈ K, ∃ y ∈ t, dist x y ≤ ε) :
    Metric.hausdorffDist (convexHull ℝ (t : Set (V n))) K ≤ ε := by
  refine Metric.hausdorffDist_le_of_mem_dist hε ?_ ?_
  · intro x hx
    exact ⟨x, convexHull_min ht hKc hx, by rw [dist_self]; exact hε⟩
  · intro x hx
    obtain ⟨y, hyt, hxy⟩ := hnet x hx
    exact ⟨y, subset_convexHull ℝ (t : Set (V n)) (Finset.mem_coe.2 hyt), hxy⟩

/-! ## Stability of convex hulls under vertex perturbations -/

/-- If corresponding vertices move by at most `δ`, the convex hulls move by at
most `δ` in Hausdorff distance. -/
theorem hausdorffDist_convexHull_perturb {n k : ℕ}
    (v w : Fin k → V n) {δ : ℝ} (hδ : 0 ≤ δ)
    (hvw : ∀ i, dist (v i) (w i) ≤ δ) :
    Metric.hausdorffDist (convexHull ℝ (Set.range v))
      (convexHull ℝ (Set.range w)) ≤ δ := by
  refine Metric.hausdorffDist_le_of_mem_dist hδ ?_ ?_
  · intro x hx
    obtain ⟨ι, _, wt, z, hwt0, hwt1, hz, hx'⟩ := mem_convexHull_iff_exists_fintype.1 hx
    have hex : ∀ i : ι, ∃ j : Fin k, z i = v j := by
      intro i
      obtain ⟨j, hj⟩ := hz i
      exact ⟨j, hj.symm⟩
    choose j hj using hex
    set y : V n := ∑ i, (wt i) • w (j i)
    have hy : y ∈ convexHull ℝ (Set.range w) := by
      refine mem_convexHull_of_exists_fintype (fun i => wt i) (fun i => w (j i)) hwt0 hwt1
        (fun i => Set.mem_range_self _) rfl
    refine ⟨y, hy, ?_⟩
    have hxy : x - y = ∑ i, (wt i) • (z i - w (j i)) := by
      have h1 : x = ∑ i, (wt i) • z i := hx'.symm
      have h2 : y = ∑ i, (wt i) • w (j i) := rfl
      rw [h1, h2, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => (smul_sub _ _ _).symm
    calc dist x y = ‖x - y‖ := dist_eq_norm _ _
      _ = ‖∑ i, (wt i) • (z i - w (j i))‖ := by rw [hxy]
      _ ≤ ∑ i, ‖(wt i) • (z i - w (j i))‖ := norm_sum_le _ _
      _ = ∑ i, |wt i| * ‖z i - w (j i)‖ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [norm_smul, Real.norm_eq_abs]
      _ = ∑ i, (wt i) * ‖z i - w (j i)‖ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [abs_of_nonneg (hwt0 i)]
      _ ≤ ∑ i, (wt i) * δ := by
          refine Finset.sum_le_sum fun i _ => ?_
          refine mul_le_mul_of_nonneg_left ?_ (hwt0 i)
          rw [← dist_eq_norm, hj i]
          exact hvw (j i)
      _ = (∑ i, wt i) * δ := by rw [Finset.sum_mul]
      _ = δ := by rw [hwt1, one_mul]
  · intro y hy
    obtain ⟨ι, _, wt, z, hwt0, hwt1, hz, hy'⟩ := mem_convexHull_iff_exists_fintype.1 hy
    have hex : ∀ i : ι, ∃ j : Fin k, z i = w j := by
      intro i
      obtain ⟨j, hj⟩ := hz i
      exact ⟨j, hj.symm⟩
    choose j hj using hex
    set x : V n := ∑ i, (wt i) • v (j i)
    have hx : x ∈ convexHull ℝ (Set.range v) := by
      refine mem_convexHull_of_exists_fintype (fun i => wt i) (fun i => v (j i)) hwt0 hwt1
        (fun i => Set.mem_range_self _) rfl
    refine ⟨x, hx, ?_⟩
    have hxy : y - x = ∑ i, (wt i) • (z i - v (j i)) := by
      have h1 : y = ∑ i, (wt i) • z i := hy'.symm
      have h2 : x = ∑ i, (wt i) • v (j i) := rfl
      rw [h1, h2, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => (smul_sub _ _ _).symm
    calc dist y x = ‖y - x‖ := dist_eq_norm _ _
      _ = ‖∑ i, (wt i) • (z i - v (j i))‖ := by rw [hxy]
      _ ≤ ∑ i, ‖(wt i) • (z i - v (j i))‖ := norm_sum_le _ _
      _ = ∑ i, |wt i| * ‖z i - v (j i)‖ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [norm_smul, Real.norm_eq_abs]
      _ = ∑ i, (wt i) * ‖z i - v (j i)‖ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [abs_of_nonneg (hwt0 i)]
      _ ≤ ∑ i, (wt i) * δ := by
          refine Finset.sum_le_sum fun i _ => ?_
          refine mul_le_mul_of_nonneg_left ?_ (hwt0 i)
          rw [← dist_eq_norm, hj i, dist_comm]
          exact hvw (j i)
      _ = (∑ i, wt i) * δ := by rw [Finset.sum_mul]
      _ = δ := by rw [hwt1, one_mul]

/-! ## Affine independence is stable under small perturbations -/

/-- Affinely independent points can be approximated by rational affinely
independent points.  This is the perturbation step of Lemma 4.2. -/
theorem AffineIndependent.exists_isRatPoint_approx {n : ℕ}
    (p : Fin (n + 1) → V n) (hp : AffineIndependent ℝ p)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ q : Fin (n + 1) → V n,
      (∀ i, IsRatPoint (q i)) ∧ (∀ i, dist (p i) (q i) < δ) ∧ AffineIndependent ℝ q := by
  have hop : IsOpen {q : Fin (n + 1) → V n | AffineIndependent ℝ q} :=
    isOpen_setOf_affineIndependent
  have hmem : p ∈ {q : Fin (n + 1) → V n | AffineIndependent ℝ q} := hp
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hop p hmem
  have hε' : 0 < min δ (ε / 2) := lt_min hδ (by linarith)
  obtain ⟨q, hqrat, hqdist⟩ := exists_forall_isRatPoint_near p hε'
  refine ⟨q, hqrat, fun i => lt_of_lt_of_le (hqdist i) (le_trans (min_le_left _ _) le_rfl), ?_⟩
  have hdist : dist q p < ε := by
    rw [dist_comm]
    rw [dist_pi_lt_iff (by linarith : (0:ℝ) < ε)]
    intro i
    exact lt_of_lt_of_le (hqdist i) (le_trans (min_le_right _ _) (by linarith))
  exact hball (Metric.mem_ball.2 hdist)

/-- Full-dimensionality of the convex hull of `n+1` affinely independent points. -/
theorem interior_convexHull_of_affineIndependent {n : ℕ} {p : Fin (n + 1) → V n}
    (hp : AffineIndependent ℝ p) :
    (interior (convexHull ℝ (Set.range p))).Nonempty := by
  have hspan : affineSpan ℝ (Set.range p) = ⊤ :=
    (AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one hp).2 (by simp)
  exact (interior_convexHull_nonempty_iff_affineSpan_eq_top (V := V n)).2 hspan

/-! ## Main rational approximation theorem -/

/-- **Rational approximation of a positive convex body.**
Given `K ∈ 𝒞_p(n)` and `η > 0` there is a full-dimensional rational polytope
`R` with `d_H(R, K) < η`.  This is the first half of Lemma 4.2. -/
theorem exists_ratPolytope_near {n : ℕ} (K : PosBody n) {η : ℝ} (hη : 0 < η) :
    ∃ R : LPolytope n, R.IsFullDim ∧ IsRatPolytope R ∧
      Metric.hausdorffDist R.carrier (K : Set (V n)) < η := by
  classical
  -- (1) A finite η/8-net in the compact set K.
  obtain ⟨t, htK, htnet⟩ := exists_finite_net K.isCompact (by linarith : (0:ℝ) < η / 8)
  -- (2) An affine basis of V n inside K.
  obtain ⟨x, hx⟩ := K.interior_nonempty
  have hKnhds : (K : Set (V n)) ∈ 𝓝 x := mem_interior_iff_mem_nhds.1 hx
  obtain ⟨b, _, hbK⟩ := exists_mem_interior_convexHull_affineBasis (E := V n)
    (s := (K : Set (V n))) hKnhds
  -- `b` is an affine basis indexed by `Fin (Module.finrank ℝ (V n) + 1)`.
  have hfinrank : Module.finrank ℝ (V n) = n := by
    show Module.finrank ℝ (Fin n → ℝ) = n
    rw [Module.finrank_pi_fintype]
    simp [Module.finrank_self]
  -- Transport the basis to `Fin (n+1)`.
  let e : Fin (Module.finrank ℝ (V n) + 1) ≃ Fin (n + 1) :=
    Equiv.cast (by rw [hfinrank])
  set p : Fin (n + 1) → V n := fun i => b (e.symm i)
  have hp : AffineIndependent ℝ p := by
    have : p = b ∘ (⇑e.symm) := rfl
    rw [this]
    exact b.ind.comp_embedding ⟨e.symm, e.symm.injective⟩
  have hpK : ∀ i, p i ∈ (K : Set (V n)) := by
    intro i
    refine hbK (subset_convexHull ℝ (Set.range b) ?_)
    exact ⟨e.symm i, rfl⟩
  -- (3) Rationalize the basis points, preserving affine independence.
  obtain ⟨q, hqrat, hqdist, hqind⟩ := AffineIndependent.exists_isRatPoint_approx p hp
    (by linarith : (0:ℝ) < η / 8)
  -- (4) Rationalize the net points.
  have htrat : ∀ y ∈ t, ∃ z : V n, IsRatPoint z ∧ dist y z < η / 8 := by
    intro y hy
    exact exists_ratPoint_near y (by linarith)
  set g : V n → V n := fun y =>
    if hy : y ∈ t then Classical.choose (htrat y hy) else 0
  have hg : ∀ y ∈ t, IsRatPoint (g y) ∧ dist y (g y) < η / 8 := by
    intro y hy
    simp only [g, dif_pos hy]
    exact Classical.choose_spec (htrat y hy)
  -- (5) The rational vertex set: basis points ∪ net points.
  set verts : Finset (V n) := (Finset.univ.image q) ∪ t.image g
  have hverts_q : ∀ i, q i ∈ verts := by
    intro i
    simp only [verts, Finset.mem_union, Finset.mem_image]
    exact Or.inl ⟨i, Finset.mem_univ i, rfl⟩
  have hverts_t : ∀ y ∈ t, g y ∈ verts := by
    intro y hy
    simp only [verts, Finset.mem_union, Finset.mem_image]
    exact Or.inr ⟨y, hy, rfl⟩
  have hverts_rat : ∀ v ∈ verts, IsRatPoint v := by
    intro v hv
    simp only [verts, Finset.mem_union, Finset.mem_image] at hv
    rcases hv with ⟨i, _, rfl⟩ | ⟨y, hy, rfl⟩
    · exact hqrat i
    · exact (hg y hy).1
  have hverts_ne : verts.Nonempty := ⟨q 0, hverts_q 0⟩
  set R : LPolytope n := LPolytope.mk verts hverts_ne
  refine ⟨R, ?_, ?_, ?_⟩
  · -- Full-dimensional.
    have hsub : Set.range q ⊆ (verts : Set (V n)) := by
      intro z hz
      obtain ⟨i, rfl⟩ := hz
      exact hverts_q i
    have hi : (interior (convexHull ℝ (Set.range q))).Nonempty :=
      interior_convexHull_of_affineIndependent hqind
    have hmono : interior (convexHull ℝ (Set.range q)) ⊆ interior R.carrier :=
      interior_mono (convexHull_mono hsub)
    exact hi.mono hmono
  · -- Rational vertices.
    intro v hv
    exact hverts_rat v hv
  · -- Hausdorff estimate.
    have hKc : Convex ℝ (K : Set (V n)) := K.convex
    have hvert_near : ∀ v ∈ verts, ∃ k ∈ (K : Set (V n)), dist v k ≤ η / 4 := by
      intro v hv
      simp only [verts, Finset.mem_union, Finset.mem_image] at hv
      rcases hv with ⟨i, _, rfl⟩ | ⟨y, hy, rfl⟩
      · refine ⟨p i, hpK i, ?_⟩
        have h := le_of_lt (hqdist i)
        linarith [dist_comm (q i) (p i)]
      · refine ⟨y, htK hy, ?_⟩
        have h := le_of_lt (hg y hy).2
        linarith [dist_comm (g y) y]
    have hdir1 : ∀ x ∈ convexHull ℝ (verts : Set (V n)),
        ∃ k ∈ (K : Set (V n)), dist x k ≤ η / 2 := by
      intro x hx
      obtain ⟨ι, _, wt, z, hwt0, hwt1, hz, hx'⟩ := mem_convexHull_iff_exists_fintype.1 hx
      have hex : ∀ i : ι, ∃ k ∈ (K : Set (V n)), dist (z i) k ≤ η / 4 :=
        fun i => hvert_near (z i) (hz i)
      choose k hkK hkdist using hex
      set y : V n := ∑ i, (wt i) • k i
      have hyK : y ∈ (K : Set (V n)) := by
        have : y ∈ convexHull ℝ (K : Set (V n)) :=
          mem_convexHull_of_exists_fintype (fun i => wt i) (fun i => k i) hwt0 hwt1
            (fun i => hkK i) rfl
        rwa [hKc.convexHull_eq] at this
      refine ⟨y, hyK, ?_⟩
      have hxy : x - y = ∑ i, (wt i) • (z i - k i) := by
        have h1 : x = ∑ i, (wt i) • z i := hx'.symm
        have h2 : y = ∑ i, (wt i) • k i := rfl
        rw [h1, h2, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => (smul_sub _ _ _).symm
      calc dist x y = ‖x - y‖ := dist_eq_norm _ _
        _ = ‖∑ i, (wt i) • (z i - k i)‖ := by rw [hxy]
        _ ≤ ∑ i, ‖(wt i) • (z i - k i)‖ := norm_sum_le _ _
        _ = ∑ i, |wt i| * ‖z i - k i‖ := by
            refine Finset.sum_congr rfl fun i _ => by rw [norm_smul, Real.norm_eq_abs]
        _ = ∑ i, (wt i) * ‖z i - k i‖ := by
            refine Finset.sum_congr rfl fun i _ => by rw [abs_of_nonneg (hwt0 i)]
        _ ≤ ∑ i, (wt i) * (η / 4) := by
            refine Finset.sum_le_sum fun i _ => ?_
            refine mul_le_mul_of_nonneg_left ?_ (hwt0 i)
            rw [← dist_eq_norm]
            exact hkdist i
        _ = (∑ i, wt i) * (η / 4) := by rw [Finset.sum_mul]
        _ = η / 4 := by rw [hwt1, one_mul]
        _ ≤ η / 2 := by linarith
    have hdir2 : ∀ x ∈ (K : Set (V n)),
        ∃ v ∈ convexHull ℝ (verts : Set (V n)), dist x v ≤ η / 2 := by
      intro x hx
      obtain ⟨y, hyt, hxy⟩ := htnet x hx
      have hyg := hg y hyt
      refine ⟨g y, subset_convexHull ℝ (verts : Set (V n)) (hverts_t y hyt), ?_⟩
      calc dist x (g y) ≤ dist x y + dist y (g y) := dist_triangle _ _ _
        _ ≤ η / 8 + η / 8 := add_le_add (le_of_lt hxy) (le_of_lt hyg.2)
        _ = η / 4 := by ring
        _ ≤ η / 2 := by linarith
    have hle : Metric.hausdorffDist R.carrier (K : Set (V n)) ≤ η / 2 :=
      Metric.hausdorffDist_le_of_mem_dist (by linarith) hdir1 hdir2
    exact lt_of_le_of_lt hle (by linarith : (η / 2 : ℝ) < η)

/-! ## Minkowski perturbation -/

/-- If `0 ∈ S` and every point of `S` has norm at most `M`, then for `t ≥ 0`
the Hausdorff distance of `R + t•S` from `R` is at most `t * M`.
This is the quantitative form of `d_H(Q,R) = t‖h_S‖_∞ → 0` in Lemma 4.2. -/
theorem hausdorffDist_add_smul_le {n : ℕ} {R S : Set (V n)}
    (hS0 : (0 : V n) ∈ S) {M : ℝ} (hM : 0 ≤ M) (hS : ∀ x ∈ S, ‖x‖ ≤ M)
    {t : ℝ} (ht : 0 ≤ t) :
    Metric.hausdorffDist (R + t • S) R ≤ t * M := by
  refine Metric.hausdorffDist_le_of_mem_dist (by positivity) ?_ ?_
  · intro x hx
    obtain ⟨r, hr, y, hy, rfl⟩ : ∃ r ∈ R, ∃ y ∈ (t • S : Set (V n)), r + y = x := by
      simpa [Set.mem_add] using hx
    obtain ⟨s, hs, rfl⟩ : ∃ s ∈ S, t • s = y := by
      simpa [Set.mem_smul_set] using hy
    refine ⟨r, hr, ?_⟩
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
    exact mul_le_mul_of_nonneg_left (hS s hs) ht
  · intro y hy
    have hsub : R ⊆ R + t • S := by
      intro x hx
      have heq : x = x + t • (0 : V n) := by simp
      rw [heq]
      exact Set.add_mem_add hx (Set.smul_mem_smul_set hS0)
    refine ⟨y, hsub hy, ?_⟩
    rw [dist_self]
    exact mul_nonneg ht hM

/-- Existence of a small Minkowski perturbation for bounded `S` with `0 ∈ S`. -/
theorem exists_t_hausdorffDist_add_smul_lt {n : ℕ} {R S : Set (V n)}
    (hS0 : (0 : V n) ∈ S) {M : ℝ} (hM : 0 ≤ M) (hS : ∀ x ∈ S, ‖x‖ ≤ M)
    {η : ℝ} (hη : 0 < η) :
    ∃ t : ℝ, 0 < t ∧ Metric.hausdorffDist (R + t • S) R < η := by
  refine ⟨min 1 (η / 2 / (M + 1)), by positivity, ?_⟩
  have ht : 0 ≤ min 1 (η / 2 / (M + 1)) := by positivity
  have hle : Metric.hausdorffDist (R + (min 1 (η / 2 / (M + 1))) • S) R
      ≤ min 1 (η / 2 / (M + 1)) * M :=
    hausdorffDist_add_smul_le hS0 hM hS ht
  refine lt_of_le_of_lt hle ?_
  have hmin : min 1 (η / 2 / (M + 1)) ≤ η / 2 / (M + 1) := min_le_right _ _
  have hM1 : 0 < M + 1 := by linarith
  calc min 1 (η / 2 / (M + 1)) * M ≤ (η / 2 / (M + 1)) * M :=
      mul_le_mul_of_nonneg_right hmin hM
    _ = η / 2 * (M / (M + 1)) := by ring
    _ ≤ η / 2 * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        rw [div_le_one hM1]
        linarith
    _ = η / 2 := by ring
    _ < η := by linarith

/-- **Lemma 4.2** (analytic assembly).  Given `K ∈ 𝒞_p(n)`, `η > 0` and a
bounded set `S` with `0 ∈ S`, there are a full-dimensional rational polytope
`R` and `t > 0` with `d_H(R, K) < η/2` and `d_H(R + t•S, R) < η/2`, hence
`d_H(R + t•S, K) < η`.  In the paper `S` realizes a smooth projective
refinement of `N(R + Σ Pᵢ)`; the fan-refinement properties are the output of
Lemma 2.2. -/
theorem lemma_4_2_minkowski_step {n : ℕ} (K : PosBody n) {η : ℝ} (hη : 0 < η)
    (S : Set (V n)) (hS0 : (0 : V n) ∈ S) {M : ℝ} (hM : 0 ≤ M)
    (hS : ∀ x ∈ S, ‖x‖ ≤ M) :
    ∃ (R : LPolytope n) (t : ℝ), R.IsFullDim ∧ IsRatPolytope R ∧ 0 < t ∧
      Metric.hausdorffDist (R.carrier + t • S) (K : Set (V n)) < η := by
  obtain ⟨R, hRdim, hRrat, hRclose⟩ := exists_ratPolytope_near K
    (by linarith : (0:ℝ) < η / 2)
  obtain ⟨t, htpos, htclose⟩ := exists_t_hausdorffDist_add_smul_lt hS0 hM hS
    (by linarith : (0:ℝ) < η / 2)
  refine ⟨R, t, hRdim, hRrat, htpos, ?_⟩
  have hfin : EMetric.hausdorffEdist (R.carrier : Set (V n)) (K : Set (V n)) ≠ ⊤ :=
    Metric.hausdorffEdist_ne_top_of_nonempty_of_bounded R.nonempty K.nonempty
      R.isCompact.isBounded K.isCompact.isBounded
  calc Metric.hausdorffDist (R.carrier + t • S) (K : Set (V n))
      ≤ Metric.hausdorffDist (R.carrier + t • S) R.carrier
        + Metric.hausdorffDist R.carrier K :=
        Metric.hausdorffDist_triangle' hfin
    _ < η / 2 + η / 2 := add_lt_add htclose hRclose
    _ = η := by ring

end Paper17
