import Paper17.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Data.Real.Basic

/-!
# Polytopes (paper §2)
-/

noncomputable section

open scoped BigOperators Pointwise

namespace Paper17

structure Polytope (n : ℕ) where
  verts : Finset (V n)
  nonempty_verts' : verts.Nonempty

namespace Polytope
variable {n : ℕ}
def carrier (P : Polytope n) : Set (V n) := convexHull ℝ (P.verts : Set (V n))
theorem convex (P : Polytope n) : Convex ℝ P.carrier := convex_convexHull _ _
theorem isCompact (P : Polytope n) : IsCompact P.carrier :=
  Set.Finite.isCompact_convexHull (P.verts.finite_toSet)
theorem nonempty (P : Polytope n) : P.carrier.Nonempty := by
  obtain ⟨v, hv⟩ := P.nonempty_verts'
  exact ⟨v, subset_convexHull _ _ hv⟩
def IsFullDim (P : Polytope n) : Prop := (interior P.carrier).Nonempty
def toPosBody (P : Polytope n) (h : P.IsFullDim) : PosBody n where
  carrier := P.carrier
  convex' := P.convex
  isCompact' := P.isCompact
  interior_nonempty' := h
def add (P Q : Polytope n) : Polytope n where
  verts := (P.verts.product Q.verts).image (fun p => p.1 + p.2)
  nonempty_verts' := by
    obtain ⟨a, ha⟩ := P.nonempty_verts'
    obtain ⟨b, hb⟩ := Q.nonempty_verts'
    exact ⟨a + b, Finset.mem_image.mpr ⟨⟨a, b⟩, Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩⟩
def smul (t : ℝ) (P : Polytope n) : Polytope n where
  verts := P.verts.image (fun x => t • x)
  nonempty_verts' := by
    obtain ⟨a, ha⟩ := P.nonempty_verts'
    exact ⟨t • a, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩
theorem carrier_add_subset (P Q : Polytope n) :
    P.carrier + Q.carrier ⊆ (P.add Q).carrier := by
  have h : (↑(P.add Q).verts : Set (V n)) = (↑P.verts : Set (V n)) + ↑Q.verts := by
    ext x
    simp [add, Set.mem_add, Finset.mem_image, Finset.mem_product, Prod.exists]
  change convexHull ℝ (↑P.verts : Set (V n)) + convexHull ℝ ↑Q.verts ⊆ _
  rw [← convexHull_add]
  exact convexHull_mono h.symm.subset
theorem carrier_smul (P : Polytope n) (t : ℝ) :
    (P.smul t).carrier = t • P.carrier := by
  change convexHull ℝ (↑(P.verts.image (fun x => t • x)) : Set (V n)) = _
  rw [Finset.coe_image]
  exact convexHull_smul t _
end Polytope

def minkowskiSet {n : ℕ} {ι : Type*} (s : Finset ι) (w : ι → ℝ) (K : ι → Set (V n)) :
    Set (V n) := ∑ i ∈ s, (w i) • K i

theorem hausdorffDist_comb_le {n : ℕ} {K : Set (V n)}
    (hK : IsCompact K) (hneK : K.Nonempty) (hconvK : Convex ℝ K)
    (ι : Type*) (s : Finset ι) (w : ι → ℝ) (P : ι → Set (V n))
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1)
    (hP : ∀ i ∈ s, IsCompact (P i) ∧ (P i).Nonempty)
    {δ : ℝ} (hδ : ∀ i ∈ s, Metric.hausdorffDist (P i) K ≤ δ) :
    Metric.hausdorffDist (minkowskiSet s w P) K ≤ δ :=
  hausdorffDist_minkowskiComb_le_max hK hneK hconvK ι s w P hw hsum hP hδ

end Paper17
