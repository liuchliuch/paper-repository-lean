import Paper17.Extension
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin

/-!
# Face-compatible nerve labels

This is the recursive choice in (3.6)-(3.7). It works for arbitrary index
sets and unbounded simplex dimensions. Every step has only the finitely many
proper nonempty faces as constraints. Targets and radii are input geometric
data, not certificates containing the required labels.
-/
noncomputable section
open scoped Topology
namespace Paper17
section
variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Y : Set E} {r : E → E → Prop}

/-- All nonempty proper faces of a finite simplex. -/
def properFaces (s : Finset ι) : Finset (Finset ι) := by
  classical
  exact s.powerset.filter fun t => t.Nonempty ∧ t ⊂ s

@[simp] theorem mem_properFaces {s t : Finset ι} :
    t ∈ properFaces s ↔ t.Nonempty ∧ t ⊂ s := by
  classical
  simp only [properFaces, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun h => h.2, fun h => ⟨h.2.1, h⟩⟩

/-- The choice at a simplex, given the already constructed labels of its proper faces. -/
def nerveLabelStep (h : ExtensionHypotheses Y r)
    (target : Finset ι → ↥Y) (radius : Finset ι → ℝ) (hpos : ∀ s, 0 < radius s)
    (s : Finset ι) (prev : ∀ t, t ⊂ s → ↥Y) : ↥Y := by
  classical
  let e : Fin (properFaces s).card ≃ ↥(properFaces s) := (properFaces s).equivFin.symm
  let ys : Fin (properFaces s).card → E := fun i =>
    (prev (e i).val (mem_properFaces.mp (e i).property).2).val
  have hmem : ∀ i, ys i ∈ Y := fun i =>
    (prev (e i).val (mem_properFaces.mp (e i).property).2).property
  let hex := h.upper_bounds (properFaces s).card ys (target s) (radius s)
    hmem (target s).property (hpos s)
  exact ⟨Classical.choose hex, (Classical.choose_spec hex).1⟩

theorem nerveLabelStep_spec (h : ExtensionHypotheses Y r)
    (target : Finset ι → ↥Y) (radius : Finset ι → ℝ) (hpos : ∀ s, 0 < radius s)
    (s : Finset ι) (prev : ∀ t, t ⊂ s → ↥Y) :
    dist (nerveLabelStep h target radius hpos s prev).val (target s).val < radius s ∧
      ∀ t (ht : t.Nonempty) (hts : t ⊂ s),
        r (prev t hts).val (nerveLabelStep h target radius hpos s prev).val := by
  classical
  let e : Fin (properFaces s).card ≃ ↥(properFaces s) := (properFaces s).equivFin.symm
  let ys : Fin (properFaces s).card → E := fun i =>
    (prev (e i).val (mem_properFaces.mp (e i).property).2).val
  have hmem : ∀ i, ys i ∈ Y := fun i =>
    (prev (e i).val (mem_properFaces.mp (e i).property).2).property
  let hex := h.upper_bounds (properFaces s).card ys (target s) (radius s)
    hmem (target s).property (hpos s)
  change dist (Classical.choose hex) (target s).val < radius s ∧
    ∀ t (ht : t.Nonempty) (hts : t ⊂ s), r (prev t hts).val (Classical.choose hex)
  constructor
  · exact (Classical.choose_spec hex).2.2
  · intro t ht hts
    let tm : ↥(properFaces s) := ⟨t, mem_properFaces.mpr ⟨ht, hts⟩⟩
    have hh := (Classical.choose_spec hex).2.1 ((properFaces s).equivFin tm)
    simpa only [ys, e, Equiv.symm_apply_apply] using hh

/-- Labels chosen recursively over all finite subsets, with no dimension bound. -/
def nerveLabel (h : ExtensionHypotheses Y r)
    (target : Finset ι → ↥Y) (radius : Finset ι → ℝ) (hpos : ∀ s, 0 < radius s) :
    Finset ι → ↥Y :=
  Finset.strongInduction (nerveLabelStep h target radius hpos)

/-- Equations (3.6)-(3.7), including compatibility across every proper-face inclusion. -/
theorem nerveLabel_spec (h : ExtensionHypotheses Y r)
    (target : Finset ι → ↥Y) (radius : Finset ι → ℝ) (hpos : ∀ s, 0 < radius s)
    (s : Finset ι) :
    dist (nerveLabel h target radius hpos s).val (target s).val < radius s ∧
      ∀ t (ht : t.Nonempty), t ⊂ s →
        r (nerveLabel h target radius hpos t).val (nerveLabel h target radius hpos s).val := by
  have heq : nerveLabel h target radius hpos s =
      nerveLabelStep h target radius hpos s
        (fun t _ => nerveLabel h target radius hpos t) :=
    Finset.strongInduction_eq _ s
  rw [heq]
  exact nerveLabelStep_spec h target radius hpos s _

end
end Paper17
