import Paper14.BCZSaturatedMeasure
import Paper14.MeasureBCZ

open MeasureTheory Measure Filter Set Topology Function
open scoped ENNReal Matrix
namespace Paper14
noncomputable section
open Background

lemma slLower_mul_slChart (v : ℝ) {x : ℝ × ℝ} (hx : x.1≠0) (s : ℝ) :
    slLower v*slChart ![x.1,x.2,s]=slChart ![x.1,x.2,s-v] := by
  have h := slChart_left (z := ![x.1,x.2,s]) (by simpa using hx) (slLower v) (by simp [slLower])
  have heq : slLeftCoordinates (slLower v) ![x.1,x.2,s]=![x.1,x.2,s-v] := by
    ext i
    fin_cases i <;> simp [slLeftCoordinates,slLower]
  rw [heq] at h
  exact h.symm

/-- Invariance under the actual BCZ return map makes the roof event invariant
under all forward horocycle times. -/
theorem bczSaturatedSet_future {A : Set (ℝ × ℝ)} (hAinv : B ⁻¹' A=A)
    {u : ℝ} (hu : 0≤u) :
    bczSaturatedSet A⊆(fun p : LatticeSpace => slLower (-u) • p) ⁻¹' bczSaturatedSet A := by
  rintro p ⟨g,hg,rfl⟩
  obtain ⟨x,hx,hAx,s,hs,hsτ,hgx⟩ := slBczSuspensionOver_rep hg
  rw [hgx]
  obtain ⟨n,hn,hn1⟩ := bcz_roof_interval hx (add_nonneg hs hu)
  have hAxn : B^[n] x∈A := by
    have heq : B^[n] ⁻¹' A=A := Function.IsFixedPt.preimage_iterate hAinv n
    change x∈B^[n] ⁻¹' A
    rw [heq]
    exact hAx
  have hs' : 0≤s+u-H n x := sub_nonneg.mpr hn
  have hsτ' : s+u-H n x<tau (B^[n] x) := by
    rw [H_succ] at hn1
    linarith
  have hmem : (QuotientGroup.mk (slChart ![(B^[n] x).1,(B^[n] x).2,s+u-H n x]) : LatticeSpace)∈
      bczSaturatedSet A :=
    ⟨_,slChart_mem_bczSuspensionOver (B_iterate_mem hx n) hAxn hs' hsτ',rfl⟩
  change (QuotientGroup.mk (slLower (-u)*slChart ![x.1,x.2,s]) : LatticeSpace)∈bczSaturatedSet A
  rw [slLower_mul_slChart (-u) hx.1.ne',sub_neg_eq_add,sl_quotient_return_shift hx n (s+u)]
  exact hmem

/-- Finite invariant measure turns the forward inclusion into invariance at
all real horocycle times. -/
theorem bczSaturatedSet_horocycle_ae {A : Set (ℝ × ℝ)} (hA : MeasurableSet A)
    (hAinv : B ⁻¹' A=A) :
    ∀ t : ℝ,(fun p : LatticeSpace => slLower t • p) ⁻¹' bczSaturatedSet A =ᵐ[latticeMeasure]
      bczSaturatedSet A := by
  have hE := measurableSet_bczSaturatedSet hA
  have hfuture (u : ℝ) (hu : 0≤u) :
      (fun p : LatticeSpace => slLower (-u) • p) ⁻¹' bczSaturatedSet A =ᵐ[latticeMeasure]
        bczSaturatedSet A := by
    have hmp := measurePreserving_smul (slLower (-u)) latticeMeasure
    exact (ae_eq_of_subset_of_measure_ge (bczSaturatedSet_future hAinv hu)
      (hmp.measure_preimage hE.nullMeasurableSet).le hE.nullMeasurableSet
      (measure_ne_top latticeMeasure _)).symm
  intro t
  by_cases ht : t≤0
  · simpa only [neg_neg] using hfuture (-t) (neg_nonneg.mpr ht)
  · have hneg := hfuture t (le_of_lt (lt_of_not_ge ht))
    have hpre := (measurePreserving_smul (slLower t) latticeMeasure).quasiMeasurePreserving.ae hneg
    filter_upwards [hpre] with p hp
    change ((slLower t) • p∈bczSaturatedSet A)=(p∈bczSaturatedSet A)
    change (slLower (-t) • (slLower t • p)∈bczSaturatedSet A)=(slLower t • p∈bczSaturatedSet A) at hp
    rw [← slLower_inv,inv_smul_smul] at hp
    exact hp.symm

/-- Ergodicity of the actual BCZ map with its normalized Farey-triangle measure.
The proof constructs the finite lattice quotient from the actual roof domain,
applies the proved Mautner phenomenon there, and transfers invariant sets back. -/
theorem ergodic_B : Ergodic B m := by
  refine ⟨measurePreserving_B,⟨?_⟩⟩
  intro A hA hAinv
  exact section_aeconst_of_saturated_aeconst hA
    (lattice_horocycle_aeconst (measurableSet_bczSaturatedSet hA)
      (bczSaturatedSet_horocycle_ae hA hAinv))

end
end Paper14
