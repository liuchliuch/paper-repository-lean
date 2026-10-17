import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
The actual center-selection step in Proposition 5.5.  The selected output
is the first batch whose radius-`2u` ball contains a strict majority; when
there is no such batch, it is the first output.  Selection is measurable
and preserves every property shared by all batch outputs.
-/
noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable

namespace Paper26.MetricAmplification
variable {α : Type*} [PseudoMetricSpace α] {l : ℕ}

/-- Indices with the requested individual accuracy. -/
def good (X : Fin l → α) (R : α) (u : ℝ) : Finset (Fin l) :=
  Finset.univ.filter fun i => dist (X i) R ≤ u

/-- The closed ball used in the paper's selection rule. -/
def neighbors (X : Fin l → α) (u : ℝ) (i : Fin l) : Finset (Fin l) :=
  Finset.univ.filter fun j => dist (X i) (X j) ≤ 2 * u

def qualifies (X : Fin l → α) (u : ℝ) (i : Fin l) : Prop :=
  l < 2 * (neighbors X u i).card

@[simp] theorem mem_good (X : Fin l → α) (R : α) (u : ℝ) (i : Fin l) :
    i ∈ good X R u ↔ dist (X i) R ≤ u := by simp [good]

@[simp] theorem mem_neighbors (X : Fin l → α) (u : ℝ) (i j : Fin l) :
    j ∈ neighbors X u i ↔ dist (X i) (X j) ≤ 2 * u := by simp [neighbors]

/-- Any accurate batch is a qualifying center when accurate batches form
 a strict majority. -/
theorem good_qualifies (X : Fin l → α) (R : α) (u : ℝ)
    (hmajority : l < 2 * (good X R u).card) (i : Fin l)
    (hi : i ∈ good X R u) : qualifies X u i := by
  have hsub : good X R u ⊆ neighbors X u i := by
    intro j hj
    simp only [mem_neighbors]
    have h := dist_triangle (X i) R (X j)
    rw [dist_comm R (X j)] at h
    have hi' := (mem_good X R u i).1 hi
    have hj' := (mem_good X R u j).1 hj
    linarith
  have hc := Finset.card_le_card hsub
  unfold qualifies
  omega

/-- Two strict majorities of the same finite batch list intersect. -/
theorem majority_intersects (S T : Finset (Fin l))
    (hS : l < 2 * S.card) (hT : l < 2 * T.card) :
    (S ∩ T).Nonempty := by
  have hc := Finset.card_union_add_card_inter S T
  have hu : (S ∪ T).card ≤ l := by
    simpa using Finset.card_le_card (Finset.subset_univ (S ∪ T))
  apply Finset.card_pos.1
  omega

/-- Every qualifying center is within the promised `3u` error. -/
theorem qualifying_error (X : Fin l → α) (R : α) (u : ℝ)
    (hmajority : l < 2 * (good X R u).card) (i : Fin l)
    (hi : qualifies X u i) : dist (X i) R ≤ 3 * u := by
  obtain ⟨j, hj⟩ := majority_intersects (neighbors X u i) (good X R u) hi hmajority
  obtain ⟨hij, hjR⟩ := Finset.mem_inter.1 hj
  have hij' := (mem_neighbors X u i j).1 hij
  have hjR' := (mem_good X R u j).1 hjR
  have h := dist_triangle (X i) (X j) R
  linarith

/-- The sentinel `l` implements the documented first-output fallback. -/
def search (X : Fin l → α) (u : ℝ) (k : ℕ) : Prop :=
  if h : k < l then qualifies X u ⟨k, h⟩ else k = l

theorem search_exists (X : Fin l → α) (u : ℝ) : ∃ k, search X u k := by
  exact ⟨l, by simp [search]⟩

def selectedIndex [NeZero l] (X : Fin l → α) (u : ℝ) : Fin l :=
  Fin.ofNat l (Nat.find (search_exists X u))

def select [NeZero l] (X : Fin l → α) (u : ℝ) : α := X (selectedIndex X u)

/-- Selection returns an actual batch, retaining PSD, trace, or other
constraints of the original estimators without a new projection. -/
theorem selected_property [NeZero l] (X : Fin l → α) (u : ℝ) (P : α → Prop)
    (hP : ∀ i, P (X i)) : P (select X u) := hP _

theorem selected_qualifies [NeZero l] (X : Fin l → α) (u : ℝ)
    (h : ∃ i, qualifies X u i) : qualifies X u (selectedIndex X u) := by
  obtain ⟨i, hi⟩ := h
  have hisearch : search X u i.val := by simp [search, i.isLt, hi]
  have hle := Nat.find_min' (search_exists X u) hisearch
  have hlt : Nat.find (search_exists X u) < l := lt_of_le_of_lt hle i.isLt
  have hfind := Nat.find_spec (search_exists X u)
  simp only [search, dif_pos hlt] at hfind
  have heq : selectedIndex X u = ⟨Nat.find (search_exists X u), hlt⟩ := by
    apply Fin.ext
    simp [selectedIndex, Nat.mod_eq_of_lt hlt]
  rwa [heq]

theorem selection_error [NeZero l] (X : Fin l → α) (R : α) (u : ℝ)
    (hmajority : l < 2 * (good X R u).card) : dist (select X u) R ≤ 3 * u := by
  have hpos : 0 < (good X R u).card := by omega
  obtain ⟨i, hi⟩ := Finset.card_pos.1 hpos
  exact qualifying_error X R u hmajority _
    (selected_qualifies X u ⟨i, good_qualifies X R u hmajority i hi⟩)

section Measurability
variable [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α]

/-- The number of neighbors is a measurable finite sum of indicator functions. -/
theorem measurable_neighbors_card (u : ℝ) (i : Fin l) :
    Measurable (fun X : Fin l → α => (neighbors X u i).card) := by
  classical
  have heq (X : Fin l → α) : (neighbors X u i).card =
      ∑ j : Fin l, if dist (X i) (X j) ≤ 2 * u then (1 : ℕ) else 0 := by
    simp [neighbors]
  simp_rw [heq]
  apply Finset.measurable_sum Finset.univ
  intro j _
  exact Measurable.ite (measurableSet_le ((measurable_pi_apply i).dist
    (measurable_pi_apply j)) measurable_const) measurable_const measurable_const

theorem measurableSet_qualifies (u : ℝ) (i : Fin l) :
    MeasurableSet {X : Fin l → α | qualifies X u i} := by
  unfold qualifies
  exact measurableSet_lt measurable_const
    (measurable_const.mul (measurable_neighbors_card u i))

theorem measurableSet_search (u : ℝ) (k : ℕ) :
    MeasurableSet {X : Fin l → α | search X u k} := by
  by_cases h : k < l
  · simpa only [search, dif_pos h] using measurableSet_qualifies (α := α) u ⟨k, h⟩
  · simp only [search, dif_neg h]
    exact MeasurableSet.const _

/-- Actual first-qualifier selection is measurable, with the sentinel
wrapped to index zero when no output qualifies. -/
theorem measurable_select [NeZero l] (u : ℝ) :
    Measurable (fun X : Fin l → α => select X u) := by
  have hf (k : ℕ) : Measurable (fun X : Fin l → α => X (Fin.ofNat l k)) :=
    measurable_pi_apply _
  exact Measurable.find (f := fun k (X : Fin l → α) => X (Fin.ofNat l k))
    (p := fun k X => search X u k) hf
    (fun k => measurableSet_search u k) (fun X : Fin l → α => search_exists X u)

/-- Applying the selection to any measurable list of actual batch outputs. -/
theorem measurable_select_comp {Ω : Type*} [MeasurableSpace Ω] [NeZero l]
    (X : Ω → Fin l → α) (hX : Measurable X) (u : ℝ) :
    Measurable (fun ω => select (X ω) u) := (measurable_select u).comp hX

end Measurability
end Paper26.MetricAmplification
