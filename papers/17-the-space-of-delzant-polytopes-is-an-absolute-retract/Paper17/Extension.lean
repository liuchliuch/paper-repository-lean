import Paper17.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.PartitionOfUnity
import Mathlib.Topology.MetricSpace.PartitionOfUnity
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Extension along refinement chains (Theorem 3.1)

This is the abstract topological core of the paper.  A nonempty subset `Y` of a
real normed space `E`, equipped with a preorder `≼`, is an absolute extensor for
metrizable spaces provided

(i) finite upper bounds exist arbitrarily close to any prescribed point of `Y`;
(ii) the convex hull of every finite chain in `Y` stays in `Y`.

The construction is Dugundji's extension method with the convexity of the target
replaced by convexity along chains: labels on the nerve of a locally finite
cover of `X \ A` are chosen so that each face label is above its proper-face
labels, and interpolation is performed only along chains (barycentric
subdivision).  A boundary estimate independent of the number of labels gives
continuity at `A`.

Definition 1.1 (`IsAbsoluteExtensor`, `IsAbsoluteRetract`) lives in
`Paper17.AbsExt`.  This module provides `ExtensionHypotheses`, proves the
analytic estimates of §3 (the interpolation coefficients (3.3), the scale
estimate (3.8), the boundary estimate (3.11), subordinate partitions of unity),
and assembles Theorem 3.1 from them.
-/

noncomputable section

open scoped Topology BigOperators

open Topology Set

namespace Paper17

/-! ## Absolute extensors and absolute retracts (Definition 1.1) -/

/-- A subset `Y` of a topological space is an absolute extensor for metrizable
spaces if every continuous map from a closed subset of a metric space into `Y`
extends continuously to the whole space. -/
def IsAbsoluteExtensor {E : Type u} [TopologicalSpace E] (Y : Set E) : Prop :=
  ∀ (X : Type u) [MetricSpace X] (A : Set X) (_ : IsClosed A)
    (f : A → E), Continuous f → (∀ a, f a ∈ Y) →
    ∃ F : X → E, Continuous F ∧ (∀ x, F x ∈ Y) ∧ (∀ a : A, F a = f a)

/-- A target is an absolute retract when every closed embedding of its
actual subtype into a metric space admits a continuous retraction. -/
def IsAbsoluteRetract {E : Type u} [TopologicalSpace E] (Y : Set E) : Prop :=
  ∀ (X : Type u) [MetricSpace X] (ι : ↥Y → X), IsClosedEmbedding ι →
    ∃ r : X → ↥Y, Continuous r ∧ (∀ y, r (ι y) = y)

/-- Definition 1.1: extend the inverse of an arbitrary closed embedding of the
target subtype. The embedding need not extend to the ambient vector space. -/
theorem isAbsoluteRetract_of_isAbsoluteExtensor {E : Type u} [TopologicalSpace E]
    {Y : Set E} (h : IsAbsoluteExtensor Y) (hne : Y.Nonempty) :
    IsAbsoluteRetract Y := by
  intro X _ ι hι
  let A : Set X := Set.range ι
  let e : ↥Y ≃ₜ A := hι.isEmbedding.toHomeomorph
  obtain ⟨F, hFc, hFY, hFeq⟩ := h X A hι.isClosed_range
    (fun a => (e.symm a : E))
    (continuous_subtype_val.comp e.symm.continuous) (fun a => (e.symm a).property)
  refine ⟨fun x => ⟨F x, hFY x⟩, hFc.subtype_mk _, ?_⟩
  intro y
  apply Subtype.ext
  have hcoe : (e y : X) = ι y := hι.isEmbedding.toHomeomorph_apply_coe y
  simpa only [hcoe, Homeomorph.symm_apply_apply] using hFeq (e y)

/-! ## Theorem 3.1: extension by refinement chains -/

/-- Conditions (i) and (ii) of Theorem 3.1. -/
structure ExtensionHypotheses {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Y : Set E) (preceq : E → E → Prop) : Prop where
  /-- (i) finite upper bounds arbitrarily close to a prescribed point -/
  upper_bounds :
    ∀ (m : ℕ) (ys : Fin m → E) (y : E) (η : ℝ),
      (∀ i, ys i ∈ Y) → y ∈ Y → 0 < η →
      ∃ z ∈ Y, (∀ i, preceq (ys i) z) ∧ dist z y < η
  /-- (ii) convex hulls of finite chains stay in `Y` -/
  chain_convex :
    ∀ (k : ℕ) (ys : Fin (k + 1) → E),
      (∀ i, ys i ∈ Y) →
      (∀ i j : Fin (k + 1), (i : ℕ) ≤ j → preceq (ys i) (ys j)) →
      convexHull ℝ (Set.range ys) ⊆ Y
  /-- preorder axioms -/
  refl : ∀ y ∈ Y, preceq y y
  trans : ∀ y z w, y ∈ Y → z ∈ Y → w ∈ Y →
    preceq y z → preceq z w → preceq y w

/-! ## Degenerate cases of the extension theorem -/

/-- Trivial case of Theorem 3.1: if `A = ∅` or `A = X`, the extension exists
without any hypotheses on `Y` beyond nonemptiness. -/
theorem theorem_3_1_degenerate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Y : Set E} (hne : Y.Nonempty) {X : Type*} [MetricSpace X] {A : Set X}
    (f : A → E) (hf : Continuous f) (hfY : ∀ a, f a ∈ Y)
    (hA0 : A = ∅ ∨ A = univ) :
    ∃ F : X → E, Continuous F ∧ (∀ x, F x ∈ Y) ∧ (∀ a : A, F a = f a) := by
  rcases hA0 with h0 | h1
  · -- `A = ∅`: any constant map into `Y` is an extension.
    obtain ⟨y0, hy0⟩ := hne
    exact ⟨fun _ => y0, continuous_const, fun _ => hy0, fun a => absurd a.2 (by simp [h0])⟩
  · -- `A = univ`: take `F x = f ⟨x, _⟩`.
    refine ⟨fun x => f ⟨x, ?_⟩, ?_, ?_, ?_⟩
    · rw [h1]; exact mem_univ _
    · refine hf.comp ?_
      exact continuous_id.subtype_mk fun _ => by rw [h1]; exact mem_univ _
    · intro x
      exact hfY _
    · intro a
      rfl

/-! ## Convex-combination estimates -/

/-- A convex combination of points, each within `ε` of `p`, is within `ε` of `p`.
This is the engine of the boundary estimate (3.11): the error does not depend on
the number of summands. -/
theorem convexComb_norm_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} {s : Finset ι} {c : ι → ℝ} {q : ι → E} {p : E} {ε : ℝ}
    (hc : ∀ i ∈ s, 0 ≤ c i) (hsum : ∑ i ∈ s, c i = 1)
    (hq : ∀ i ∈ s, ‖q i - p‖ ≤ ε) :
    ‖(∑ i ∈ s, c i • q i) - p‖ ≤ ε := by
  -- `∑ c i • q i - p = ∑ c i • (q i - p)` because `∑ c i = 1`.
  have key : (∑ i ∈ s, c i • q i) - p = ∑ i ∈ s, c i • (q i - p) := by
    have h1 : (∑ i ∈ s, c i • q i) - p = (∑ i ∈ s, c i • q i) - (∑ i ∈ s, c i) • p := by
      rw [hsum, one_smul]
    have h2 : (∑ i ∈ s, c i) • p = ∑ i ∈ s, c i • p :=
      Finset.sum_smul
    rw [h1, h2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [smul_sub]
  rw [key]
  calc ‖∑ i ∈ s, c i • (q i - p)‖ ≤ ∑ i ∈ s, ‖c i • (q i - p)‖ := norm_sum_le _ _
    _ = ∑ i ∈ s, |c i| * ‖q i - p‖ := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ i ∈ s, |c i| * ε := by
      refine Finset.sum_le_sum fun i hi => ?_
      exact mul_le_mul_of_nonneg_left (hq i hi) (abs_nonneg _)
    _ = (∑ i ∈ s, |c i|) * ε := by rw [← Finset.sum_mul]
    _ = (∑ i ∈ s, c i) * ε := by
      refine congrArg (fun t => t * ε) (Finset.sum_congr rfl fun i hi => ?_)
      rw [abs_of_nonneg (hc i hi)]
    _ = ε := by rw [hsum, one_mul]

/-- Equation (3.11): the boundary estimate.  A convex combination of labels
`q i`, each of which lies within `ε` of the target value `p`, lies within `ε` of
`p`.  In the construction of Theorem 3.1 the labels contributing at `x` satisfy
(3.9)–(3.10) with `ε = (4/3) d(x,a) + ω (4 d(x,a))`, where `ω` is a modulus of
continuity of `f` at `a`; the bound does not depend on the number of labels. -/
theorem boundary_estimate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} {s : Finset ι} {c : ι → ℝ} {q : ι → E} {p : E} {ε : ℝ}
    (hc : ∀ i ∈ s, 0 ≤ c i) (hsum : ∑ i ∈ s, c i = 1)
    (hq : ∀ i ∈ s, ‖q i - p‖ ≤ ε) :
    ‖(∑ i ∈ s, c i • q i) - p‖ ≤ ε :=
  convexComb_norm_sub_le hc hsum hq

/-- Full form of (3.11): if the labels contributing at `x` are within
`(4/3) dx` of the values `f (b i)` (equation 3.9), the anchor points `b i` lie
within `4 dx` of `a` (equation 3.10), and `ω` dominates `‖f (b i) - f a‖`, then
the interpolated value is within `(4/3) dx + ω` of `f a`.  This is the estimate
that gives continuity of the extension at the closed set `A`, independently of
the number of contributing labels.  In the construction `dx = d(x,a)`. -/
theorem boundary_estimate_of_labels
    {X E : Type*} [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : Set X} {f : A → E} {a : A} {dx : ℝ}
    {ι : Type*} {s : Finset ι} {c : ι → ℝ} {q : ι → E} {b : ι → A} {ω : ℝ}
    (hc : ∀ i ∈ s, 0 ≤ c i) (hsum : ∑ i ∈ s, c i = 1)
    (hq : ∀ i ∈ s, ‖q i - f (b i)‖ ≤ (4 / 3) * dx)
    (_hd : ∀ i ∈ s, dist (b i : X) (a : X) < 4 * dx)
    (hω : ∀ i ∈ s, ‖f (b i) - f a‖ ≤ ω) :
    ‖(∑ i ∈ s, c i • q i) - f a‖ ≤ (4 / 3) * dx + ω := by
  -- Each label is within `(4/3) dx + ω` of `f a`, then apply the convex estimate.
  have hq' : ∀ i ∈ s, ‖q i - f a‖ ≤ (4 / 3) * dx + ω := by
    intro i hi
    have h1 := hq i hi
    have h2 := hω i hi
    calc ‖q i - f a‖ = ‖(q i - f (b i)) + (f (b i) - f a)‖ := by
          rw [sub_add_sub_cancel]
      _ ≤ ‖q i - f (b i)‖ + ‖f (b i) - f a‖ := norm_add_le _ _
      _ ≤ (4 / 3) * dx + ω := add_le_add h1 h2
  exact convexComb_norm_sub_le hc hsum hq'

/-- Convex combination along a chain stays in `Y` (condition (ii), pointwise
form).  This is what puts the interpolated values of Theorem 3.1 into `Y`. -/
theorem convexComb_mem_of_chain {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Y : Set E} {preceq : E → E → Prop}
    (h : ExtensionHypotheses Y preceq)
    {n : ℕ} {ys : Fin (n + 1) → E}
    (hmem : ∀ i, ys i ∈ Y)
    (hchain : ∀ i j : Fin (n + 1), (i : ℕ) ≤ j → preceq (ys i) (ys j))
    {ι : Type*} {t : Finset ι} {w : ι → ℝ} {p : ι → E}
    (hw : ∀ i ∈ t, 0 ≤ w i) (hwt : ∑ i ∈ t, w i = 1)
    (hp : ∀ i ∈ t, p i ∈ Set.range ys) :
    (∑ i ∈ t, w i • p i) ∈ Y := by
  -- The sum is the center of mass of the `p i` with weights `w i`, hence lies in
  -- `convexHull ℝ (range ys) ⊆ Y` by condition (ii).
  have hsumpos : 0 < ∑ i ∈ t, w i := by
    rw [hwt]; exact one_pos
  have hcm : t.centerMass w p = ∑ i ∈ t, w i • p i :=
    t.centerMass_eq_of_sum_1 _ hwt
  have h1 : t.centerMass w p ∈ convexHull ℝ (Set.range ys) :=
    t.centerMass_mem_convexHull hw hsumpos fun i hi => hp i hi
  rw [hcm] at h1
  exact h.chain_convex n ys hmem hchain h1

/-! ## Key estimates of the construction (paper §3) -/

/-- Auxiliary `ℕ`-level telescoping identity for the coefficients of (3.3):
`∑_{j<m} (j+1) (u j - u (j+1)) = ∑_{j<m} u j - m * u m`. -/
theorem sum_range_mul_sub (u : ℕ → ℝ) (m : ℕ) :
    ∑ j ∈ Finset.range m, ((j : ℝ) + 1) * (u j - u (j + 1))
      = ∑ j ∈ Finset.range m, u j - (m : ℝ) * u m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : ∑ j ∈ Finset.range (m + 1), ((j : ℝ) + 1) * (u j - u (j + 1))
        = (∑ j ∈ Finset.range m, ((j : ℝ) + 1) * (u j - u (j + 1)))
          + ((m : ℝ) + 1) * (u m - u (m + 1)) :=
      Finset.sum_range_succ _ _
    have h2 : ∑ j ∈ Finset.range (m + 1), u j
        = ∑ j ∈ Finset.range m, u j + u m :=
      Finset.sum_range_succ _ _
    rw [h1, ih, h2]
    push_cast
    ring

/-- Equation (3.3): the interpolation formula on the barycentric subdivision.
List the positive partition weights at `x` in decreasing order as
`a₁ ≥ ⋯ ≥ a_m > 0`, put `a_{m+1} = 0`, and let `I_j` index the first `j`
weights.  Then `G(x) = ∑_{j=1}^m j (a_j - a_{j+1}) q_{I_j}`: the coefficient of
the label indexed by the first `j` weights is `j (a_j - a_{j+1})`.

In 0-based form the weights are `w 0 ≥ w 1 ≥ ⋯ ≥ w (m-1) > 0` with `w m = 0`
(`hzero`), and the coefficient of the label indexed by the first `j+1` weights
is `c j = (j+1) (w j - w (j+1))` for `j < m`.  These coefficients are
nonnegative and sum to `∑_{j<m} w j = 1`.  Monotonicity of `w` gives
nonnegativity; the sum is the telescoping identity
`∑_j j (a_j - a_{j+1}) = ∑_j a_j`.  At a tie `a_j = a_{j+1}` the
order-dependent term has coefficient zero, so the formula is independent of the
ordering within ties. -/
theorem interpolation_coefficients_nonneg
    {m : ℕ} (w : ℕ → ℝ)
    (hmono : ∀ i j, i ≤ j → w j ≤ w i)
    (hsum : ∑ i ∈ Finset.range m, w i = 1)
    (hzero : w m = 0) :
    ∃ c : ℕ → ℝ,
      (∀ j < m, 0 ≤ c j) ∧
      (∑ j ∈ Finset.range m, c j = 1) ∧
      (∀ j < m, c j = ((j : ℝ) + 1) * (w j - w (j + 1))) := by
  -- Take the coefficients of (3.3) and verify nonnegativity and the sum identity.
  set c : ℕ → ℝ := fun j => ((j : ℝ) + 1) * (w j - w (j + 1))
  refine ⟨c, ?_, ?_, fun j _ => rfl⟩
  · -- Nonnegativity: `w j - w (j+1) ≥ 0` by monotonicity, and `j+1 > 0`.
    intro j hj
    have hdiff : 0 ≤ w j - w (j + 1) :=
      sub_nonneg.mpr (hmono j (j + 1) (Nat.le_succ _))
    have hpos : 0 ≤ ((j : ℝ) + 1) := by positivity
    exact mul_nonneg hpos hdiff
  · -- Summation identity: `∑_{j<m} (j+1)(w j - w (j+1)) = ∑_{j<m} w j - m * w m = 1`.
    rw [sum_range_mul_sub, hsum, hzero]
    ring

/-- Equation (3.8): if `x ∈ B(z, r/4)` with `r = d(z,A)`, then
`r < (4/3) d(x,A)`, and some `a ∈ A` satisfies `d(x,a) < 3 d(x,A)`. -/
theorem scale_estimate {X : Type*} [MetricSpace X] {A : Set X} (hA : IsClosed A)
    {x z : X} {r : ℝ} (hx : x ∈ Metric.ball z (r / 4))
    (hz : r = Metric.infDist z A) (hAne : A.Nonempty) (hxout : x ∉ A) :
    r < (4 / 3) * Metric.infDist x A ∧
      ∃ a ∈ A, dist x a < 3 * Metric.infDist x A := by
  have hdist : dist x z < r / 4 := hx
  have hpos : 0 < r := by
    have h4 : (4 : ℝ) * dist x z < r := by
      have h := mul_lt_mul_of_pos_left hdist (by norm_num : (0:ℝ) < 4)
      have hcancel : (4 : ℝ) * (r / 4) = r := by ring
      linarith
    have : 0 ≤ dist x z := dist_nonneg
    linarith
  have hdpos : 0 < Metric.infDist x A :=
    (hA.notMem_iff_infDist_pos hAne).1 hxout
  -- `3r/4 < d(x,A)`: distance to `A` is 1-Lipschitz, and `d(x,z) < r/4`.
  have hstrict : (3 / 4 : ℝ) * r < Metric.infDist x A := by
    have h1 : r - dist x z > r - r / 4 := by linarith
    have hlip : Metric.infDist z A - dist x z ≤ Metric.infDist x A := by
      have := Metric.infDist_le_infDist_add_dist (x := z) (y := x) (s := A)
      rw [dist_comm] at this
      linarith
    have h3 : r - r / 4 = (3 / 4 : ℝ) * r := by ring
    rw [← hz] at hlip
    linarith
  refine ⟨?_, ?_⟩
  · -- `r < (4/3) d(x,A)` from `(3/4) r < d(x,A)`.
    have hmul : (4 / 3 : ℝ) * ((3 / 4 : ℝ) * r) = r := by ring
    have : (4 / 3 : ℝ) * ((3 / 4 : ℝ) * r) < (4 / 3 : ℝ) * Metric.infDist x A :=
      mul_lt_mul_of_pos_left hstrict (by norm_num)
    linarith
  · -- Existence of `a ∈ A` with `d(x,a) < 3 d(x,A)`: the infimum is approached.
    have hlt : Metric.infDist x A < 3 * Metric.infDist x A := by
      nlinarith [hdpos]
    obtain ⟨a, ha, hda⟩ := (Metric.infDist_lt_iff hAne).1 hlt
    exact ⟨a, ha, hda⟩

/-- Approximate minimizer (3.5): if `r = d(z,A) > 0` then some `a ∈ A`
satisfies `d(z,a) < 2 r`. -/
theorem exists_approx_minimizer {X : Type*} [MetricSpace X] {A : Set X} (hAne : A.Nonempty)
    {z : X} {r : ℝ} (hz : r = Metric.infDist z A) (hr : 0 < r) :
    ∃ a ∈ A, dist z a < 2 * r := by
  have hlt : Metric.infDist z A < 2 * r := by
    rw [hz]; linarith
  exact (Metric.infDist_lt_iff hAne).1 hlt

/-- Every point `z ∉ A` of the complement lies in its own ball
`B(z, d(z,A)/4)`, so these balls cover `Z = X \ A`. -/
theorem mem_ball_infDiv_quarter {X : Type*} [MetricSpace X] {A : Set X}
    (hA : IsClosed A) (hAne : A.Nonempty) {z : X} (hz : z ∉ A) :
    z ∈ Metric.ball z (Metric.infDist z A / 4) := by
  have hpos : 0 < Metric.infDist z A :=
    (hA.notMem_iff_infDist_pos hAne).1 hz
  simp only [Metric.mem_ball, dist_self]
  positivity

/-- Support for the existence of locally finite refinements and subordinate
partitions of unity on metric spaces (used in the construction of Theorem 3.1).
This is the paracompactness of metric spaces, packaged as a family of
continuous functions subordinate to an open cover of `X`. -/
theorem exists_partitionOfUnity_subordinate
    {X : Type*} [MetricSpace X] {ι : Type*} {U : ι → Set X}
    (hU : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = univ) :
    ∃ (φ : ι → X → ℝ),
      (∀ i x, 0 ≤ φ i x) ∧
      (∀ x, {i | φ i x > 0}.Finite) ∧
      (∀ x, ∑ᶠ i, φ i x = 1) ∧
      (∀ i x, φ i x > 0 → x ∈ U i) ∧
      (∀ i, Continuous (φ i)) := by
  -- A partition of unity subordinate to the open cover `U` of the closed set `univ`.
  have hcover' : (univ : Set X) ⊆ ⋃ i, U i := by
    intro x _
    rw [hcover]
    exact mem_univ x
  obtain ⟨ρ, hρ⟩ :
      ∃ ρ : PartitionOfUnity ι X univ, ρ.IsSubordinate U :=
    PartitionOfUnity.exists_isSubordinate isClosed_univ U hU hcover'
  refine ⟨fun i x => ρ i x, ?_, ?_, ?_, ?_, ?_⟩
  · intro i x
    exact ρ.nonneg i x
  · intro x
    have hfin : {i | x ∈ Function.support (ρ i)}.Finite :=
      ρ.locallyFinite.point_finite x
    refine hfin.subset fun i hi => ?_
    show x ∈ Function.support (ρ i)
    exact Function.mem_support.mpr (ne_of_gt hi)
  · intro x
    exact ρ.sum_eq_one (mem_univ x)
  · intro i x hx
    have hxsupp : x ∈ Function.support (ρ i) :=
      Function.mem_support.mpr (ne_of_gt hx)
    exact (hρ i) (subset_tsupport _ hxsupp)
  · intro i
    exact (ρ i).continuous


/-! ## Sorted interpolation (barycentric subdivision formula (3.3))

Finite-dimensional piece of the Dugundji construction: formula (3.3) as a
function of the partition weights.  On each ordering chamber the formula is
affine in `w` (`continuous_interpPerm`); the chambers are closed
(`isClosed_sortedBy`) and cover the space of weights.  Once tie-breaking
independence is available, the affine pieces paste to a global continuous map
via `continuous_of_finite_closed_cover`. -/

section SortedInterp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Initial segment of length `j` of the ordering `σ`, as a `Finset`. -/
def seg {n : ℕ} (σ : Equiv.Perm (Fin n)) (j : ℕ) : Finset (Fin n) :=
  (Finset.univ.filter (fun k : Fin n => (k : ℕ) < j)).image (fun k => σ k)

/-- Formula (3.3) along the ordering `σ`:
`∑_{j<n} (j+1) (a_j - a_{j+1}) q (first j+1)` with `a_j = w (σ j)`, `a_n = 0`. -/
def interpPerm {n : ℕ} (q : Finset (Fin n) → E) (σ : Equiv.Perm (Fin n)) (w : Fin n → ℝ) : E :=
  ∑ j : Fin n,
    ((((j : ℕ) : ℝ) + 1) *
      (w (σ j) - (if h : (j : ℕ) + 1 < n then w (σ ⟨j + 1, h⟩) else 0))) • q (seg σ (j + 1))

/-- Weights along `σ` are nonincreasing. -/
def Decreasing {n : ℕ} (w : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j : Fin n, (i : ℕ) ≤ (j : ℕ) → w (σ j) ≤ w (σ i)

/-- Continuity of the fixed-order formula: it is affine in `w`. -/
theorem continuous_interpPerm {n : ℕ} (q : Finset (Fin n) → E) (σ : Equiv.Perm (Fin n)) :
    Continuous fun w : Fin n → ℝ => interpPerm q σ w := by
  unfold interpPerm
  refine continuous_finset_sum Finset.univ fun j _ => ?_
  apply Continuous.smul _ continuous_const
  apply Continuous.mul continuous_const
  apply Continuous.sub (continuous_apply _)
  by_cases h : (j : ℕ) + 1 < n
  · simp only [dif_pos h]
    exact continuous_apply _
  · simp only [dif_neg h]
    exact continuous_const

/-- The set of weight vectors sorted by `σ`, closed in `Fin n → ℝ`. -/
def sortedBy {n : ℕ} (σ : Equiv.Perm (Fin n)) : Set (Fin n → ℝ) :=
  {w | Decreasing w σ}

theorem isClosed_sortedBy {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    IsClosed (sortedBy σ : Set (Fin n → ℝ)) := by
  have h : sortedBy σ = {w | ∀ i j : Fin n, (i : ℕ) ≤ (j : ℕ) → w (σ j) ≤ w (σ i)} := rfl
  rw [h]
  simp only [Set.setOf_forall]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => ?_
  exact isClosed_le (continuous_apply _) (continuous_apply _)

/-- Flags along an ordering form a nested chain (the flag of the barycentric
subdivision used in (3.3)). -/
theorem seg_mono {n : ℕ} (σ : Equiv.Perm (Fin n)) {j k : ℕ} (hjk : j ≤ k) :
    seg σ j ⊆ seg σ k := by
  intro x hx
  simp only [seg, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨a, lt_of_lt_of_le ha hjk, rfl⟩

/-- The flags `seg σ j` are exactly the first `j` indices of `σ`. -/
theorem mem_seg {n : ℕ} (σ : Equiv.Perm (Fin n)) {x : Fin n} {j : ℕ} :
    x ∈ seg σ j ↔ (σ.symm x : ℕ) < j := by
  simp only [seg, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hk, rfl⟩
    simpa using hk
  · intro hx
    exact ⟨σ.symm x, hx, by simp⟩

/-- Finite closed-cover pasting: continuous on each of finitely many closed sets
covering the space implies continuous. -/
theorem continuous_of_finite_closed_cover {X : Type*} [TopologicalSpace X] {ι : Type*}
    [Finite ι] {f : X → E} {s : ι → Set X}
    (hc : ∀ i, IsClosed (s i)) (hcover : univ ⊆ ⋃ i, s i)
    (hf : ∀ i, ContinuousOn f (s i)) : Continuous f := by
  exact (locallyFinite_of_finite (f := s)).continuous
    (Set.Subset.antisymm (Set.subset_univ _) hcover) hc hf

end SortedInterp


/-! The complete global proof of Theorem 3.1 is in `Paper17.Dugundji`,
which imports these estimates and the actual face-label/interpolation modules. -/

end Paper17
