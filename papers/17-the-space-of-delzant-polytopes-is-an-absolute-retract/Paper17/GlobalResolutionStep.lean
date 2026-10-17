import Paper17.ConeMultiplicity
import Paper17.ResolutionMeasure

/-!
# A genuine global multiplicity-reducing stellar step

A singular maximal cone supplies a lattice point. Its positive coordinate
support is a shared face. The same new integral ray and the same coefficients
are used in every incident maximal cone. Compatibility and coverage follow
from the geometric cone-complex construction; every affected determinant
strictly decreases and so does the total natural-number weight.
-/
noncomputable section
open scoped BigOperators
namespace Paper17
section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- All simultaneously affected maximal cones have smaller total integral
weight. This is the global descent needed for smooth simplicial resolution. -/
theorem stellar_integral_weight_lt (v : ι → Fin n → ℤ)
    (K : SimplicialConeComplex (realRays v)) (hcard : ∀ s ∈ K.facets, s.card = n)
    (I : Finset ι) (hI : I.Nonempty) (hface : ∃ s ∈ K.facets, I ⊆ s)
    (w : Fin n → ℤ) (b : ι → ℝ)
    (hb0 : ∀ i, 0 ≤ b i) (hbs : ∀ i, i ∉ I → b i = 0)
    (hbp : ∀ i ∈ I, 0 < b i) (hb1 : ∀ i ∈ I, b i < 1)
    (hw : (fun j => (w j : ℝ)) = ∑ i, b i • realRays v i) :
    (∑ s ∈ K.starFacets I, (n + 1) ^ coneMultiplicity (starRays v w) s) <
      ∑ s ∈ K.facets, (n + 1) ^ coneMultiplicity v s := by
  apply K.stellar_weight_lt n I hI hface (fun s hs => (hcard s hs).le)
    (coneMultiplicity v) (coneMultiplicity (starRays v w))
  · intro s hs _
    exact coneMultiplicity_some_image v s (hcard s hs) w
  · intro s hs hIs k hk
    exact star_coneMultiplicity_lt v s (hcard s hs) (K.independent s hs)
      I hIs k hk w b hbs hbp hb1 hw

/-- A singular maximal cone always supplies admissible global stellar data,
with the actual nonzero integral ray and strict global weight descent. -/
theorem exists_global_stellar_lattice_step (v : ι → Fin n → ℤ)
    (K : SimplicialConeComplex (realRays v)) (hcard : ∀ s ∈ K.facets, s.card = n)
    (hsingular : ∃ s ∈ K.facets, 1 < coneMultiplicity v s) :
    ∃ (I : Finset ι) (w : Fin n → ℤ) (b : ι → ℝ),
      I.Nonempty ∧ (∃ s ∈ K.facets, I ⊆ s) ∧ w ≠ 0 ∧
      (∀ i, 0 ≤ b i) ∧ (∀ i, i ∉ I → b i = 0) ∧
      (∀ i ∈ I, 0 < b i ∧ b i < 1) ∧
      (fun j => (w j : ℝ)) = ∑ i, b i • realRays v i ∧
      (∑ s ∈ K.starFacets I, (n + 1) ^ coneMultiplicity (starRays v w) s) <
        ∑ s ∈ K.facets, (n + 1) ^ coneMultiplicity v s := by
  classical
  obtain ⟨s, hs, hmult⟩ := hsingular
  let e := cellEnumeration s (hcard s hs)
  have hdet : 1 < (cellMatrix v s (hcard s hs)).det.natAbs := by
    simpa only [coneMultiplicity_of_card v s (hcard s hs)] using hmult
  obtain ⟨w, hw0, c, hc, hwc⟩ := exists_nonzero_parallelepiped_point _ hdet
  let b : ι → ℝ := fun i => if hi : i ∈ s then c (e.symm ⟨i, hi⟩) else 0
  have hb0 : ∀ i, 0 ≤ b i := by
    intro i
    dsimp [b]
    split_ifs
    · exact (hc _).1
    · exact le_refl 0
  have hbs : ∀ i, i ∉ s → b i = 0 := fun i hi => dif_neg hi
  have hbenum : (fun i => b (e i).val) = c := by
    funext i
    simp [b, (e i).property]
  have hw : (fun j => (w j : ℝ)) = ∑ i, b i • realRays v i := by
    have heq := cellSynthesis_eq_global v s (hcard s hs) b hbs
    change latticeSynthesis _ (fun i => b (e i).val) = _ at heq
    rw [hbenum] at heq
    exact (funext hwc).trans heq
  let I := s.filter (fun i => 0 < b i)
  have hIs : I ⊆ s := Finset.filter_subset _ _
  have hbp : ∀ i ∈ I, 0 < b i := fun i hi => (Finset.mem_filter.mp hi).2
  have hb1 : ∀ i ∈ I, b i < 1 := by
    intro i hi
    have his := (Finset.mem_filter.mp hi).1
    simpa only [b, dif_pos his] using (hc (e.symm ⟨i, his⟩)).2
  have hbsI : ∀ i, i ∉ I → b i = 0 := by
    intro i hi
    by_cases his : i ∈ s
    · have hnot : ¬ 0 < b i := fun hpos => hi (Finset.mem_filter.mpr ⟨his, hpos⟩)
      exact le_antisymm (le_of_not_gt hnot) (hb0 i)
    · exact hbs i his
  have hI : I.Nonempty := by
    by_contra hn
    have hempty : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hbzero : ∀ i, b i = 0 := fun i => hbsI i (by simp [hempty])
    apply hw0
    ext j
    have hj := congrFun hw j
    simp only [hbzero, zero_smul, Finset.sum_const_zero, Pi.zero_apply] at hj
    exact_mod_cast hj
  refine ⟨I, w, b, hI, ⟨s, hs, hIs⟩, hw0, hb0, hbsI,
    fun i hi => ⟨hbp i hi, hb1 i hi⟩, hw, ?_⟩
  exact stellar_integral_weight_lt v K hcard I hI ⟨s, hs, hIs⟩ w b hb0 hbsI hbp hb1 hw

/-- The maximal dimension is retained throughout the global star. -/
theorem starFacets_full_card (v : ι → Fin n → ℤ)
    (K : SimplicialConeComplex (realRays v)) (hcard : ∀ s ∈ K.facets, s.card = n)
    (I : Finset ι) : ∀ s ∈ K.starFacets I, s.card = n := by
  intro s hs
  obtain ⟨t, ht, q, hq, rfl⟩ := (K.mem_starFacets I s).mp hs
  exact (starCell_card I t hq).trans (hcard t ht)

end
end Paper17
