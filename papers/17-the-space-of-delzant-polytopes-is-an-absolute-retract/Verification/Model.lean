import Paper17.Delzant
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Defs.Induced
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# Independently reviewable statement model for paper 17

Shared definitions used by `Verification.Challenge` and `Verification.Solution`.
The contract uses actual geometric definitions from `Paper17.Delzant` and
a canonical carrier metric, avoiding nonunique vertex presentations as points
of the metric space. No geometric theorem is assumed in these definitions.

Correspondence with production (`Paper17.*`, see DESIGN.md):

* `P17Contract.IsAbsoluteExtensor` ↔ `Paper17.IsAbsoluteExtensor` / `Paper17.AbsExt`
* `P17Contract.IsAbsoluteRetract`   ↔ `Paper17.IsAbsoluteRetract`
* `P17Contract.DelzantPolytope`     ↔ `Paper17.DelzantPolytope`
* `P17Contract.hausdorffDist_minkowskiComb_le_max` ↔ `Paper17.hausdorffDist_minkowskiComb_le_max`
-/

noncomputable section

open Topology
open scoped Topology BigOperators Pointwise

namespace P17Contract

/-! ## Ambient space and support functions -/

/-- The ambient space `ℝ^n` as a Pi type. -/
abbrev V (n : ℕ) := Fin n → ℝ

/-- Euclidean inner product on `V n`. -/
def dot {n : ℕ} (u x : V n) : ℝ := ∑ i, u i * x i

/-- The support function `h_K(u) = max_{x ∈ K} ⟨u, x⟩`. -/
def supportFunction {n : ℕ} (K : Set (V n)) (u : V n) : ℝ :=
  sSup (Set.image (fun x => dot u x) K)

/-! ## Definition 1.1: absolute extensors and absolute retracts -/

/-- Definition 1.1: `Y` is an absolute extensor for metrizable spaces if every
continuous map from a closed subset of a metric space into `Y` extends
continuously to the whole space. -/
def IsAbsoluteExtensor (Y : Type u) [TopologicalSpace Y] : Prop :=
  ∀ (X : Type u) [MetricSpace X] (A : Set X), IsClosed A →
    ∀ f : A → Y, Continuous f →
      ∃ F : X → Y, Continuous F ∧ ∀ a : A, F a = f a

/-- Definition 1.1: a metrizable space `Y` is an absolute retract if every
realization of `Y` as a closed subspace of a metrizable space admits a
retraction onto `Y`. -/
def IsAbsoluteRetract (Y : Type u) [TopologicalSpace Y] : Prop :=
  ∀ (X : Type u) [MetricSpace X] (e : Y → X), IsClosedEmbedding e →
    ∃ r : X → Y, Continuous r ∧ ∀ y : Y, r (e y) = y

/-! ## Positive convex bodies `𝒞_p(n)` -/

/-- A positive convex body: compact convex, nonempty, with nonempty interior.
This is the paper's `𝒞_p(n)`. -/
structure PosBody (n : ℕ) where
  carrier : Set (V n)
  convex' : Convex ℝ carrier
  isCompact' : IsCompact carrier
  interior_nonempty' : (interior carrier).Nonempty

namespace PosBody

variable {n : ℕ}

theorem isCompact (K : PosBody n) : IsCompact K.carrier := K.isCompact'
theorem convex (K : PosBody n) : Convex ℝ K.carrier := K.convex'
theorem nonempty (K : PosBody n) : K.carrier.Nonempty := by
  obtain ⟨x, hx⟩ := K.interior_nonempty'
  exact ⟨x, interior_subset hx⟩
theorem interior_nonempty (K : PosBody n) : (interior K.carrier).Nonempty :=
  K.interior_nonempty'
theorem isClosed (K : PosBody n) : IsClosed K.carrier := K.isCompact.isClosed

theorem ext {K L : PosBody n} (h : K.carrier = L.carrier) : K = L := by
  cases K; cases L; congr

end PosBody

/-- Finite Hausdorff edistance of two nonempty compact sets. -/
theorem hausdorffEdist_ne_top_of_compact {n : ℕ} {K L : Set (V n)}
    (hK : IsCompact K) (hneK : K.Nonempty) (hL : IsCompact L) (hneL : L.Nonempty) :
    EMetric.hausdorffEdist K L ≠ ⊤ :=
  Metric.hausdorffEdist_ne_top_of_nonempty_of_bounded hneK hneL hK.isBounded hL.isBounded

/-- Hausdorff distance between positive bodies. -/
def hdist {n : ℕ} (K L : PosBody n) : ℝ :=
  Metric.hausdorffDist K.carrier L.carrier

/-- Hausdorff metric on `𝒞_p(n)`. -/
noncomputable instance instMetricSpacePosBody (n : ℕ) : MetricSpace (PosBody n) where
  dist := hdist
  dist_self K := by
    simp only [hdist]
    exact Metric.hausdorffDist_self_zero
  dist_comm K L := by
    simp only [hdist]
    exact Metric.hausdorffDist_comm
  dist_triangle K L M := by
    simp only [hdist]
    refine Metric.hausdorffDist_triangle ?_
    exact hausdorffEdist_ne_top_of_compact
      (PosBody.isCompact K) (PosBody.nonempty K) (PosBody.isCompact L) (PosBody.nonempty L)
  eq_of_dist_eq_zero {K L} h := by
    have h0 : K.carrier = L.carrier :=
      ((PosBody.isCompact K).isClosed.hausdorffDist_zero_iff_eq
        (PosBody.isCompact L).isClosed
        (hausdorffEdist_ne_top_of_compact (PosBody.isCompact K)
          (PosBody.nonempty K) (PosBody.isCompact L)
          (PosBody.nonempty L))).mp (by simpa [hdist] using h)
    exact PosBody.ext h0

/-! ## Polytopes and Delzant polytopes (paper §2) -/

/-- A polytope: convex hull of finitely many points. -/
structure Polytope (n : ℕ) where
  verts : Finset (V n)
  nonempty_verts' : verts.Nonempty

namespace Polytope

variable {n : ℕ}

def carrier (P : Polytope n) : Set (V n) := convexHull ℝ (P.verts : Set (V n))

theorem convex (P : Polytope n) : Convex ℝ P.carrier :=
  convex_convexHull _ _

theorem isCompact (P : Polytope n) : IsCompact P.carrier :=
  Set.Finite.isCompact_convexHull P.verts.finite_toSet

theorem nonempty (P : Polytope n) : P.carrier.Nonempty := by
  obtain ⟨v, hv⟩ := P.nonempty_verts'
  exact ⟨v, subset_convexHull _ _ hv⟩

/-- Full-dimensional polytope: nonempty interior. -/
def IsFullDim (P : Polytope n) : Prop := (interior P.carrier).Nonempty

/-- Minkowski sum of two polytopes. -/
def add (P Q : Polytope n) : Polytope n where
  verts := (P.verts.product Q.verts).image (fun p => p.1 + p.2)
  nonempty_verts' := by
    obtain ⟨a, ha⟩ := P.nonempty_verts'
    obtain ⟨b, hb⟩ := Q.nonempty_verts'
    exact ⟨a + b, Finset.mem_image.mpr ⟨⟨a, b⟩, Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩⟩

end Polytope

/-- A finite family of integer rays is unimodular when the matrix
they form has determinant ±1 (paper §2, multiplicity one). -/
def IsUnimodular {n : ℕ} (rays : Fin n → Fin n → ℤ) : Prop :=
  abs ((Matrix.of fun i j => rays i j).det) = 1

/-- Adjacent normal rays of Example 2.4: `(1,1)` and `(-1,1)`. -/
def AdjacentRays2 (u v : Fin 2 → ℤ) : Prop :=
  u = ![1, 1] ∧ v = ![-1, 1]

/-- Determinant of two planar integer rays. -/
def det2 (u v : Fin 2 → ℤ) : ℤ := u 0 * v 1 - u 1 * v 0

/-- Geometric normal cone of a body at a point. -/
def normalCone {n : ℕ} (K : Set (V n)) (v : V n) : Set (V n) :=
  {u | ∀ x ∈ K, dot u x ≤ dot u v}

/-- A carrier is Delzant precisely when it has a finite polytope presentation
whose actual normal fan is smooth. Smoothness in `Paper17.IsDelzant` requires
integer generators, determinant of absolute value one, and equality of the
positive span with each full-dimensional geometric normal cone. -/
structure IsDelzantData {n : ℕ} (K : PosBody n) : Prop where
  presentation : ∃ P : Paper17.Polytope n,
    Paper17.IsDelzant P ∧ P.carrier = K.carrier

/-- Delzant predicate on positive bodies. -/
def IsDelzant {n : ℕ} (K : PosBody n) : Prop := Nonempty (IsDelzantData K)

/-- Full-dimensional Delzant polytopes `𝒟(n)`. -/
def DelzantPolytope (n : ℕ) := {K : PosBody n // IsDelzant K}

namespace DelzantPolytope

variable {n : ℕ}

def carrier (P : DelzantPolytope n) : Set (V n) := P.1.carrier

/-- Refinement preorder: `P ≼ Q` iff the normal fan of `Q` refines that of `P`. -/
def le (P Q : DelzantPolytope n) : Prop :=
  ∀ v ∈ Q.carrier, ∃ w ∈ P.carrier,
    normalCone Q.carrier v ⊆ normalCone P.carrier w

end DelzantPolytope

abbrev DelzantSpace (n : ℕ) : Type := DelzantPolytope n

def delzantDist {n : ℕ} (P Q : DelzantSpace n) : ℝ :=
  Metric.hausdorffDist P.carrier Q.carrier

noncomputable instance instMetricSpaceDelzant (n : ℕ) : MetricSpace (DelzantSpace n) where
  dist := delzantDist
  dist_self P := by
    simp only [delzantDist]
    exact Metric.hausdorffDist_self_zero
  dist_comm P Q := by
    simp only [delzantDist]
    exact Metric.hausdorffDist_comm
  dist_triangle P Q R := by
    simp only [delzantDist]
    refine Metric.hausdorffDist_triangle ?_
    exact hausdorffEdist_ne_top_of_compact
      (PosBody.isCompact P.1) (PosBody.nonempty P.1)
      (PosBody.isCompact Q.1) (PosBody.nonempty Q.1)
  eq_of_dist_eq_zero {P Q} h := by
    have h0 : P.1.carrier = Q.1.carrier :=
      ((PosBody.isCompact P.1).isClosed.hausdorffDist_zero_iff_eq
        (PosBody.isCompact Q.1).isClosed
        (hausdorffEdist_ne_top_of_compact
          (PosBody.isCompact P.1) (PosBody.nonempty P.1)
          (PosBody.isCompact Q.1) (PosBody.nonempty Q.1))).mp
        (by simpa [delzantDist] using h)
    have h1 : P.1 = Q.1 := PosBody.ext h0
    rcases P with ⟨p, hp⟩
    rcases Q with ⟨q, hq⟩
    subst h1
    rfl

/-! ## Volume of symmetric difference (Proposition 2.5) -/

def vol {n : ℕ} (K : Set (V n)) : ℝ :=
  (MeasureTheory.volume K).toReal

def volSymmDiff {n : ℕ} (K L : Set (V n)) : ℝ :=
  vol ((K \ L) ∪ (L \ K))

/-! ## Spheres and balls (Corollary 4.1) -/

def sphere (k : ℕ) : Set (Fin (k + 1) → ℝ) :=
  {x | ∑ i, x i ^ 2 = 1}

def ball (k : ℕ) : Set (Fin (k + 1) → ℝ) :=
  {x | ∑ i, x i ^ 2 ≤ 1}

/-! ## Refinement chains and extension hypotheses (Theorem 3.1) -/

structure ExtensionHypotheses {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Y : Set E) (preceq : E → E → Prop) : Prop where
  upper_bounds :
    ∀ (m : ℕ) (ys : Fin m → E) (y : E) (η : ℝ),
      (∀ i, ys i ∈ Y) → y ∈ Y → 0 < η →
      ∃ z ∈ Y, (∀ i, preceq (ys i) z) ∧ dist z y < η
  chain_convex :
    ∀ (k : ℕ) (ys : Fin (k + 1) → E),
      (∀ i, ys i ∈ Y) →
      (∀ i j : Fin (k + 1), (i : ℕ) ≤ j → preceq (ys i) (ys j)) →
      convexHull ℝ (Set.range ys) ⊆ Y
  refl : ∀ y ∈ Y, preceq y y
  trans : ∀ y z w, y ∈ Y → z ∈ Y → w ∈ Y →
    preceq y z → preceq z w → preceq y w

/-- Canonical fan, using normal cones at every point of the carrier. -/
def normalFan {n : ℕ} (K : Set (V n)) : Set (Set (V n)) :=
  {C | ∃ v ∈ K, normalCone K v = C}

/-- Only finitely many normal fans occur near each point of the indicated domain. -/
def LocallyFiniteFansOn {X : Type*} [TopologicalSpace X] {n : ℕ}
    (g : X → DelzantSpace n) (D : Set X) : Prop :=
  ∀ x ∈ D, ∃ U ∈ 𝓝 x, (normalFan ∘ DelzantPolytope.carrier ∘ g '' U).Finite

/-- Rational polytopal normal directions, with generators tied to actual cones. -/
def HasRationalNormalFan {n : ℕ} (K : PosBody n) : Prop :=
  ∃ verts : Finset (V n), convexHull ℝ (verts : Set (V n)) = K.carrier ∧
    ∀ v ∈ verts, ∃ (m : ℕ) (rays : Fin m → Fin n → ℤ),
      normalCone K.carrier v = {u | ∃ t : Fin m → ℝ,
        (∀ i, 0 ≤ t i) ∧ u = ∑ i, t i • (fun j => (rays i j : ℝ))}

def bodyRefines {n : ℕ} (L K : PosBody n) : Prop :=
  ∀ v ∈ L.carrier, ∃ w ∈ K.carrier,
    normalCone L.carrier v ⊆ normalCone K.carrier w

/-- Unit directions used by the paper's support-function ambient space. -/
abbrev UnitDirections (n : ℕ) := {u : V n // ∑ i, u i ^ 2 = 1}
abbrev PaperSupportSpace (n : ℕ) := C(UnitDirections n, ℝ)

/-- Delzant carriers whose support function belongs to a specified ambient set. -/
def InSupportSet {n : ℕ} (W : Set (PaperSupportSpace n)) (P : DelzantSpace n) : Prop :=
  ∃ h ∈ W, ∀ u, h u = supportFunction P.carrier u.val

end P17Contract
