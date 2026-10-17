import Mathlib.Topology.PartitionOfUnity
import Mathlib.Topology.MetricSpace.PartitionOfUnity
import Mathlib.Order.Filter.Finite

/-!
# The barycentric open cover of a locally finite partition

Strict level sets of the partition weights form a locally finite open cover
indexed by nonempty finite faces. At a point, all its active faces are nested.
A partition subordinate to this cover therefore interpolates only face flags.
-/
noncomputable section
open scoped Topology
open Set Filter Function
namespace Paper17
variable {ι X : Type*} [TopologicalSpace X]

/-- The open region where a finite nonempty face is a strict upper level set. -/
def strictFace (φ : ι → X → ℝ) (s : Finset ι) : Set X :=
  {x | s.Nonempty ∧ (∀ i ∈ s, 0 < φ i x) ∧
    ∀ i ∈ s, ∀ j, j ∉ s → φ j x < φ i x}

theorem strictFace_chain {φ : ι → X → ℝ} {s t : Finset ι} {x : X}
    (hs : x ∈ strictFace φ s) (ht : x ∈ strictFace φ t) : s ⊆ t ∨ t ⊆ s := by
  classical
  by_cases hst : s ⊆ t
  · exact Or.inl hst
  · right
    by_contra hts
    obtain ⟨i, hi, hit⟩ := Finset.not_subset.mp hst
    obtain ⟨j, hj, hjs⟩ := Finset.not_subset.mp hts
    exact (hs.2.2 i hi j hjs).not_ge (ht.2.2 j hj i hit).le

theorem isOpen_strictFace {φ : ι → X → ℝ}
    (hc : ∀ i, Continuous (φ i)) (hf : LocallyFinite fun i => Function.support (φ i))
    (s : Finset ι) : IsOpen (strictFace φ s) := by
  classical
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨U, hUx, hUfin⟩ := hf x
  let J := {i | (Function.support (φ i) ∩ U).Nonempty}
  have hpos : ∀ᶠ y in 𝓝 x, ∀ i ∈ s, 0 < φ i y :=
    (eventually_all_finite s.finite_toSet).mpr fun i hi =>
      (isOpen_lt continuous_const (hc i)).mem_nhds (hx.2.1 i hi)
  have hcmp : ∀ᶠ y in 𝓝 x, ∀ i ∈ s, ∀ j ∈ J, j ∉ s → φ j y < φ i y := by
    apply (eventually_all_finite s.finite_toSet).mpr
    intro i hi
    apply (eventually_all_finite hUfin).mpr
    intro j hj
    by_cases hjs : j ∈ s
    · exact Filter.Eventually.of_forall fun _ h => False.elim (h hjs)
    · have hh : ∀ᶠ y in 𝓝 x, φ j y < φ i y :=
        (isOpen_lt (hc j) (hc i)).mem_nhds (hx.2.2 i hi j hjs)
      exact hh.mono fun _ h _ => h
  filter_upwards [hUx, hpos, hcmp] with y hy hpy hcy
  refine ⟨hx.1, hpy, ?_⟩
  intro i hi j hjs
  by_cases hjJ : j ∈ J
  · exact hcy i hi j hjJ hjs
  · have hz : φ j y = 0 := by
      by_contra hn
      exact hjJ ⟨y, hn, hy⟩
    rw [hz]
    exact hpy i hi

theorem locallyFinite_strictFace {φ : ι → X → ℝ}
    (hf : LocallyFinite fun i => Function.support (φ i)) : LocallyFinite (strictFace φ) := by
  classical
  intro x
  obtain ⟨U, hU, hfin⟩ := hf x
  refine ⟨U, hU, ?_⟩
  let J := {i | (Function.support (φ i) ∩ U).Nonempty}
  have hsub : {s | (strictFace φ s ∩ U).Nonempty} ⊆
      (hfin.toFinset.powerset : Set (Finset ι)) := by
    intro s ⟨y, hys, hyU⟩
    apply Finset.mem_powerset.mpr
    intro i hi
    exact hfin.mem_toFinset.mpr ⟨y, (ne_of_gt (hys.2.1 i hi)), hyU⟩
  exact hfin.toFinset.powerset.finite_toSet.subset hsub

/-- Every point has a nonempty finite strict upper level set: take its positive support. -/
theorem strictFace_cover (φ : PartitionOfUnity ι X Set.univ) :
    (⋃ s, strictFace (fun i x => φ i x) s) = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro x
  have hfin := φ.locallyFinite.point_finite x
  let s := hfin.toFinset
  have hs : s.Nonempty := by
    by_contra hn
    have hz : ∀ i, φ i x = 0 := by
      intro i
      by_contra hi
      exact hn ⟨i, hfin.mem_toFinset.mpr hi⟩
    have hh := φ.sum_eq_one (Set.mem_univ x)
    simp [hz] at hh
  refine Set.mem_iUnion.mpr ⟨s, hs, ?_, ?_⟩
  · intro i hi
    have hn : φ i x ≠ 0 := hfin.mem_toFinset.mp hi
    exact lt_of_le_of_ne (φ.nonneg i x) (Ne.symm hn)
  · intro i hi j hj
    have hzero : φ j x = 0 := by
      by_contra hn
      exact hj (hfin.mem_toFinset.mpr hn)
    change φ j x < φ i x
    rw [hzero]
    have hn : φ i x ≠ 0 := hfin.mem_toFinset.mp hi
    exact lt_of_le_of_ne (φ.nonneg i x) (Ne.symm hn)

end Paper17
