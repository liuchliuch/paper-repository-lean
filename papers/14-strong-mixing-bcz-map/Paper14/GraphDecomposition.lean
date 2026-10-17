import Paper14.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-! The nonnegative telescoping step from (9) to (10).
The hypotheses are the two decompositions in (9); their construction by
subsequential weak limits remains a separate, unproved step. -/
open MeasureTheory Measure Function Set
open scoped ENNReal
namespace Paper14
noncomputable section

def intermediateMeasure {α : Type*} [MeasurableSpace α]
    (W : α → α) (ν : ℕ → Measure α) : Measure α :=
  Measure.sum fun j => ∑ k ∈ Finset.range j, Measure.map (W^[k]) (ν j)

lemma map_finset_sum {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (f : α → β) (hf : Measurable f) (s : Finset ι) (ν : ι → Measure α) :
    Measure.map f (∑ i ∈ s, ν i) = ∑ i ∈ s, Measure.map f (ν i) := by
  simp only [← Measure.mapₗ_apply_of_measurable hf]
  exact map_sum (Measure.mapₗ f) ν s

lemma map_iterate_succ {α : Type*} [MeasurableSpace α]
    (W : α → α) (hW : Measurable W) (ν : Measure α) (k : ℕ) :
    Measure.map W (Measure.map (W^[k]) ν) = Measure.map (W^[k + 1]) ν := by
  rw [Measure.map_map hW (hW.iterate k)]
  congr 1
  ext x
  exact (iterate_succ_apply' W k x).symm

/-- The telescoping identity without subtraction of measures. -/
lemma intermediate_finite_telescope {α : Type*} [MeasurableSpace α]
    (W : α → α) (hW : Measurable W) (ν : Measure α) (j : ℕ) :
    Measure.map W (∑ k ∈ Finset.range j, Measure.map (W^[k]) ν) + ν =
      (∑ k ∈ Finset.range j, Measure.map (W^[k]) ν) + Measure.map (W^[j]) ν := by
  rw [map_finset_sum W hW]
  simp_rw [map_iterate_succ W hW]
  have hs := Finset.sum_range_succ' (fun k => Measure.map (W^[k]) ν) j
  have ht := Finset.sum_range_succ (fun k => Measure.map (W^[k]) ν) j
  simpa only [iterate_zero, Measure.map_id] using hs.symm.trans ht

/-- Equality of the two nonnegative decompositions forces the intermediate
measure to be invariant. Finiteness of the common total measure permits
cancellation; no subtraction of infinite measures is used. -/
theorem intermediateMeasure_invariant {α : Type*} [MeasurableSpace α]
    (W : α → α) (hW : Measurable W) (ν : ℕ → Measure α)
    [IsFiniteMeasure (Measure.sum ν)]
    (hdecomp : Measure.sum ν = Measure.sum (fun j => Measure.map (W^[j]) (ν j))) :
    Measure.map W (intermediateMeasure W ν) = intermediateMeasure W ν := by
  have htel : Measure.map W (intermediateMeasure W ν) + Measure.sum ν =
      intermediateMeasure W ν + Measure.sum (fun j => Measure.map (W^[j]) (ν j)) := by
    simp only [intermediateMeasure, Measure.map_sum hW.aemeasurable, Measure.sum_add_sum]
    congr 1
    funext j
    exact intermediate_finite_telescope W hW (ν j) j
  rw [← hdecomp] at htel
  ext s hs
  have h := congrArg (fun η : Measure α => η s) htel
  simp only [Measure.add_apply] at h
  apply (ENNReal.add_right_inj (measure_ne_top (Measure.sum ν) s)).mp
  simpa only [add_comm] using h

/-- The mass identity in (10), valid before imposing a first-moment bound. -/
theorem intermediateMeasure_mass {α : Type*} [MeasurableSpace α]
    (W : α → α) (hW : Measurable W) (ν : ℕ → Measure α) :
    intermediateMeasure W ν univ = ∑' j : ℕ, (j : ℝ≥0∞) * ν j univ := by
  simp [intermediateMeasure, Measure.sum_apply, Measure.finset_sum_apply,
    Measure.map_apply (hW.iterate _), nsmul_eq_mul]

/-- The intermediate measure also inherits the simultaneous invariance
under any measurable `V` commuting with `W`, as used in (10). -/
theorem intermediateMeasure_invariant_commuting {α : Type*} [MeasurableSpace α]
    (V W : α → α) (hV : Measurable V) (hW : Measurable W)
    (hcomm : Function.Commute V W) (ν : ℕ → Measure α)
    (hinv : ∀ j, Measure.map V (ν j) = ν j) :
    Measure.map V (intermediateMeasure W ν) = intermediateMeasure W ν := by
  simp only [intermediateMeasure, Measure.map_sum hV.aemeasurable,
    map_finset_sum V hV]
  congr 1
  funext j
  apply Finset.sum_congr rfl
  intro k hk
  rw [Measure.map_map hV (hW.iterate k)]
  have heq : V ∘ W^[k] = W^[k] ∘ V := funext (hcomm.iterate_right k)
  rw [heq, ← Measure.map_map (hW.iterate k) hV, hinv j]

end
end Paper14
