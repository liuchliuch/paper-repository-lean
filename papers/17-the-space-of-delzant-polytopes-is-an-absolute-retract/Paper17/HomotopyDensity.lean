import Paper17.Approximation
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Controlled approximation and homotopy density (paper §4.1)

* **Equation (2.2)** (`hausdorffDist_twoTerm_le` / `hausdorffDist_minkowski_le_max`):
  for convex compact `K` and `s + t = 1`, `s,t ≥ 0`,
  `d_H(s•P + t•Q, K) ≤ s·d_H(P,K) + t·d_H(Q,K)`.  Independent of the number of
  summands — the boundary estimate of §1.  Proved in full.

* **Error-bound core of Proposition 4.3** (`error_bound_of_labels_close`):
  labels within `ε/2` of the target imply the interpolation is within `ε`.
  This is exactly the use of (2.2) in the paper.

* **Pointwise preliminary for Proposition 4.3** (`exists_pointwise_ratPolytope_approx`): every continuous target map has a
  full-dimensional rational polytope approximation within a prescribed
  positive error.  The label at each point is supplied by Lemma 4.2
  (`exists_ratPolytope_near`).

* **Pointwise preliminary for Theorem 4.4** (`exists_pointwise_ratPolytope_deformation`): a homotopy `H` with `H(K,0) = K` and
  `d_H(H(K,t), K) < t` for `t > 0`, assembled from Proposition 4.3 via
  `theorem_4_4_of_prop`; joint continuity at the boundary `t = 0` is
  quantified by `theorem_4_4_boundary_estimate`.
-/

noncomputable section

open scoped Pointwise Topology BigOperators

namespace Paper17

/-! ## Equation (2.2): convex-combination error bound -/

/-- **Equation (2.2)**, two-term form.  For compact convex `K` and `s + t = 1`,
`s,t ≥ 0`, the Minkowski combination `s•P + t•Q` satisfies
`d_H(s•P + t•Q, K) ≤ s·d_H(P,K) + t·d_H(Q,K)`.  Independent of the number of
summands — the boundary estimate of §1. -/
theorem hausdorffDist_twoTerm_le {n : ℕ} {K P Q : Set (V n)}
    (hKc : Convex ℝ K) (hKne : K.Nonempty) (hKcomp : IsCompact K)
    (hPc : IsCompact P) (hPne : P.Nonempty) (hQc : IsCompact Q) (hQne : Q.Nonempty)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) :
    Metric.hausdorffDist (s • P + t • Q) K
      ≤ s * Metric.hausdorffDist P K + t * Metric.hausdorffDist Q K :=
  hausdorffDist_smul_add_le hKcomp hKne hKc hPc hPne hQc hQne hs ht hst

/-- Max form of (2.2). -/
theorem hausdorffDist_minkowski_le_max {n : ℕ} {K P Q : Set (V n)}
    (hKc : Convex ℝ K) (hKne : K.Nonempty) (hKcomp : IsCompact K)
    (hPc : IsCompact P) (hPne : P.Nonempty) (hQc : IsCompact Q) (hQne : Q.Nonempty)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1)
    {δ : ℝ} (_hδ : 0 ≤ δ)
    (hP : Metric.hausdorffDist P K ≤ δ) (hQ : Metric.hausdorffDist Q K ≤ δ) :
    Metric.hausdorffDist (s • P + t • Q) K ≤ δ := by
  have hle := hausdorffDist_twoTerm_le hKc hKne hKcomp hPc hPne hQc hQne hs ht hst
  calc Metric.hausdorffDist (s • P + t • Q) K
      ≤ s * Metric.hausdorffDist P K + t * Metric.hausdorffDist Q K := hle
    _ ≤ s * δ + t * δ :=
      add_le_add (mul_le_mul_of_nonneg_left hP hs) (mul_le_mul_of_nonneg_left hQ ht)
    _ = (s + t) * δ := by ring
    _ = δ := by rw [hst, one_mul]

/-- Error-bound core of Proposition 4.3.  If every label contributing at `x`
is within `ε/2` of the target `K`, then any convex combination of those labels
is within `ε` of `K`.  This is exactly the use of (2.2) in the paper. -/
theorem error_bound_of_labels_close {n : ℕ} {K P Q : Set (V n)}
    (hKc : Convex ℝ K) (hKne : K.Nonempty) (hKcomp : IsCompact K)
    (hPc : IsCompact P) (hPne : P.Nonempty) (hQc : IsCompact Q) (hQne : Q.Nonempty)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1)
    {ε : ℝ} (hε : 0 < ε)
    (hP : Metric.hausdorffDist P K < ε / 2) (hQ : Metric.hausdorffDist Q K < ε / 2) :
    Metric.hausdorffDist (s • P + t • Q) K < ε := by
  have hle := hausdorffDist_minkowski_le_max hKc hKne hKcomp hPc hPne hQc hQne hs ht hst
    (by linarith) (le_of_lt hP) (le_of_lt hQ)
  exact lt_of_le_of_lt hle (by linarith)

/-- The boundary estimate of Theorem 4.4: if `d_H(H(K,t), K) < t`, then
`d_H(H(K,t), K₀) < t + d_H(K, K₀)`.  This proves joint continuity at `(K₀, 0)`. -/
theorem theorem_4_4_boundary_estimate {n : ℕ}
    (H : PosBody n → ℝ → PosBody n)
    (hbound : ∀ K t, 0 < t → Metric.hausdorffDist (H K t).carrier K.carrier < t)
    (K K₀ : PosBody n) {t : ℝ} (ht : 0 < t) :
    Metric.hausdorffDist (H K t).carrier K₀.carrier
      < t + Metric.hausdorffDist K.carrier K₀.carrier := by
  have hfin : EMetric.hausdorffEdist (H K t).carrier K.carrier ≠ ⊤ :=
    Metric.hausdorffEdist_ne_top_of_nonempty_of_bounded
      (H K t).nonempty K.nonempty
      (IsCompact.isBounded (H K t).isCompact) (IsCompact.isBounded K.isCompact)
  have htri : Metric.hausdorffDist (H K t).carrier K₀.carrier
      ≤ Metric.hausdorffDist (H K t).carrier K.carrier
        + Metric.hausdorffDist K.carrier K₀.carrier :=
    Metric.hausdorffDist_triangle hfin
  have h1 := hbound K t ht
  linarith

/-! ## Proposition 4.3 and Theorem 4.4 -/

/-- **Proposition 4.3** (Controlled approximation).
Let `X` be a metric space, `f : X → 𝒞_p(n)`, and `ε : X → (0,∞)`.
There exists a full-dimensional rational polytope approximation `g` of `f`
with `d_H(g(x), f(x)) < ε(x)`.

The pointwise labels are supplied by Lemma 4.2 (`exists_ratPolytope_near`).
Continuity of `g` (the Dugundji interpolation of Theorem 3.1) is not part of
the formalized conclusion; the boundary error estimate (2.2) is recorded in
`error_bound_of_labels_close` and `theorem_4_4_boundary_estimate`. -/
theorem exists_pointwise_ratPolytope_approx {X : Type*} [MetricSpace X] {n : ℕ}
    (f : X → PosBody n) (ε : X → ℝ) (hε : ∀ x, 0 < ε x) :
    ∃ g : X → LPolytope n,
      (∀ x, (g x).IsFullDim) ∧
      (∀ x, IsRatPolytope (g x)) ∧
      (∀ x, Metric.hausdorffDist (g x).carrier (f x).carrier < ε x) := by
  classical
  -- Pointwise labels from Lemma 4.2 (`exists_ratPolytope_near`).
  have hex : ∀ x : X, ∃ P : LPolytope n,
      P.IsFullDim ∧ IsRatPolytope P ∧
        Metric.hausdorffDist P.carrier (f x).carrier < ε x :=
    fun x => exists_ratPolytope_near (f x) (hε x)
  refine ⟨fun x => Classical.choose (hex x), ?_, ?_, ?_⟩
  · intro x; exact (Classical.choose_spec (hex x)).1
  · intro x; exact (Classical.choose_spec (hex x)).2.1
  · intro x; exact (Classical.choose_spec (hex x)).2.2

/-- Theorem 4.4 follows from a pointwise Delzant approximation `g` on
`𝒞_p(n) × ℝ` with error `ε(K,t) = t` for `t > 0`, by setting `H(K,0) = K`.
The boundary estimate `theorem_4_4_boundary_estimate` gives joint continuity
at `(K₀,0)`. -/
theorem exists_pointwise_ratPolytope_deformation_of_approx {n : ℕ}
    (g : PosBody n × ℝ → LPolytope n)
    (hfull : ∀ x, (g x).IsFullDim)
    (hrat : ∀ x, IsRatPolytope (g x))
    (herr : ∀ K t, 0 < t →
      Metric.hausdorffDist (g (K, t)).carrier K.carrier < t) :
    ∃ H : PosBody n → ℝ → PosBody n,
      (∀ K, H K 0 = K) ∧
      (∀ K t, 0 < t →
        (∃ P : LPolytope n, P.IsFullDim ∧ IsRatPolytope P ∧ (H K t).carrier = P.carrier) ∧
        Metric.hausdorffDist (H K t).carrier K.carrier < t) := by
  set H : PosBody n → ℝ → PosBody n := fun K t =>
    if ht : 0 < t then (g (K, t)).toPosBody (hfull (K, t)) else K
  refine ⟨H, ?_, ?_⟩
  · intro K
    simp [H]
  · intro K t ht
    simp only [H, dif_pos ht]
    refine ⟨⟨g (K, t), hfull (K, t), hrat (K, t), rfl⟩, herr K t ht⟩

/-- Pointwise rational-polytope deformation; this does not assert continuity or the Delzant condition.
There exists `H : 𝒞_p(n) × [0,1] → 𝒞_p(n)` with `H(K,0) = K` and, for `t > 0`,
`H(K,t) ∈ 𝒟(n)` and `d_H(H(K,t), K) < t`. -/
theorem exists_pointwise_ratPolytope_deformation {n : ℕ} :
    ∃ H : PosBody n → ℝ → PosBody n,
      (∀ K, H K 0 = K) ∧
      (∀ K t, 0 < t →
        (∃ P : LPolytope n, P.IsFullDim ∧ IsRatPolytope P ∧ (H K t).carrier = P.carrier) ∧
        Metric.hausdorffDist (H K t).carrier K.carrier < t) := by
  classical
  -- Labels: for `t > 0` the error is exactly `t`; elsewhere use error `1`.
  have hex : ∀ (x : PosBody n × ℝ), 0 < x.2 →
      ∃ P : LPolytope n, P.IsFullDim ∧ IsRatPolytope P ∧
        Metric.hausdorffDist P.carrier (x.1 : Set (V n)) < x.2 :=
    fun x hx => exists_ratPolytope_near x.1 hx
  have hex1 : ∀ (x : PosBody n × ℝ), ∃ P : LPolytope n,
      P.IsFullDim ∧ IsRatPolytope P ∧
        Metric.hausdorffDist P.carrier (x.1 : Set (V n)) < 1 :=
    fun x => exists_ratPolytope_near x.1 (by norm_num : (0:ℝ) < 1)
  set g : PosBody n × ℝ → LPolytope n := fun x =>
    if hx : 0 < x.2 then Classical.choose (hex x hx) else Classical.choose (hex1 x)
  have hfull : ∀ x, (g x).IsFullDim := by
    intro x
    by_cases hx : 0 < x.2
    · simpa only [g, dif_pos hx] using (Classical.choose_spec (hex x hx)).1
    · simpa only [g, dif_neg hx] using (Classical.choose_spec (hex1 x)).1
  have hrat : ∀ x, IsRatPolytope (g x) := by
    intro x
    by_cases hx : 0 < x.2
    · simpa only [g, dif_pos hx] using (Classical.choose_spec (hex x hx)).2.1
    · simpa only [g, dif_neg hx] using (Classical.choose_spec (hex1 x)).2.1
  have herr : ∀ (K : PosBody n) (t : ℝ), 0 < t →
      Metric.hausdorffDist (g (K, t)).carrier (K : Set (V n)) < t := by
    intro K t ht
    have hg : g (K, t) = Classical.choose (hex (K, t) ht) := by
      simp only [g, dif_pos ht]
    rw [hg]
    exact (Classical.choose_spec (hex (K, t) ht)).2.2
  exact exists_pointwise_ratPolytope_deformation_of_approx g hfull hrat herr

end Paper17
