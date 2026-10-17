import Paper15.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# Finite barycentres (Lemma 3)

Paper: *An exact classical threshold in the binary triangle network*.

## Mathematical content

**Lemma 3 (Finite barycentres).** Let `g` be a bounded measurable map from a
probability space to `ℝ^d`. Its mean is a convex combination of at most `d+1`
values of `g`. The same conclusion holds with the values chosen from any
prescribed full-measure subset of the domain.

The convex-geometric core of the lemma is Carathéodory's theorem refined by the
affine dimension bound: every point of the convex hull of a subset of `ℝ^d` is a
convex combination of at most `d+1` points of that subset.  This module proves
that core completely, in several equivalent packaging:

* `finite_barycentre_caratheodory` — the exact statement requested for `ℝ^d`;
* `exists_finset_card_le_of_mem_convexHull` — the finset form;
* `finite_barycentre_of_weights` — barycentres of finitely supported laws;
* `finite_barycentre_finset` — weights supported on a `Finset`;
* `discrete_mean_caratheodory` — discrete probability version (the form used by
  Lemma 4);
* `lemma3_finite_range` / `lemma3_finite_range_fullMeasure` — measure-theoretic
  versions for finite-range maps.

## General Bochner-integral version

The complete arbitrary-range theorem is proved in `Paper15.IntegralConvex`:
`lemma3_integrable_fullMeasure` and `lemma3_bounded_measurable`. The latter
has exactly the bounded measurable hypotheses of the paper and allows an
arbitrary prescribed full-measure subset. This module retains the finite-range
lemmas and convex-geometric tools used in that proof.
-/

noncomputable section

namespace Paper15

open Finset BigOperators Set MeasureTheory Module

/-- Borel structure on `ℝ^d` (needed for the measure-theoretic form of Lemma 3). -/
instance instMeasurableSpaceEuclideanSpace (d : ℕ) :
    MeasurableSpace (EuclideanSpace ℝ (Fin d)) := borel _
instance instBorelSpaceEuclideanSpace (d : ℕ) :
    BorelSpace (EuclideanSpace ℝ (Fin d)) := ⟨rfl⟩

/-! ## Affine independence vs. ambient dimension -/

/-- An affine-independent family in `ℝ^d` has at most `d+1` points. -/
lemma affineIndependent_card_le_succ {d : ℕ} {t : Finset (EuclideanSpace ℝ (Fin d))}
    (hi : AffineIndependent ℝ ((↑) : t → EuclideanSpace ℝ (Fin d))) :
    t.card ≤ d + 1 := by
  have hcard : Fintype.card ↥t = t.card := Fintype.card_coe t
  have hdim : finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  have hspan :
      finrank ℝ (vectorSpan ℝ (Set.range ((↑) : t → EuclideanSpace ℝ (Fin d)))) ≤ d := by
    have hle := Submodule.finrank_le
      (vectorSpan ℝ (Set.range ((↑) : t → EuclideanSpace ℝ (Fin d))))
    rw [hdim] at hle
    exact hle
  have hbound : Fintype.card ↥t ≤
      finrank ℝ (vectorSpan ℝ (Set.range ((↑) : t → EuclideanSpace ℝ (Fin d)))) + 1 :=
    hi.card_le_finrank_succ
  rw [hcard] at hbound
  omega

/-- A finite affine-independent subset of `ℝ^d` has at most `d+1` elements. -/
lemma affineIndependent_finset_card_le {d : ℕ} {t : Finset (EuclideanSpace ℝ (Fin d))}
    (hi : AffineIndependent ℝ ((↑) : t → EuclideanSpace ℝ (Fin d))) :
    #t ≤ d + 1 :=
  affineIndependent_card_le_succ hi

/-! ## Carathéodory in `ℝ^d`: convex hull form -/

/-- **Carathéodory + dimension bound.**  Every point of the convex hull of
`s ⊆ ℝ^d` lies in the convex hull of at most `d+1` points of `s`. -/
theorem exists_finset_card_le_of_mem_convexHull {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} {m : EuclideanSpace ℝ (Fin d)}
    (hm : m ∈ convexHull ℝ s) :
    ∃ t : Finset (EuclideanSpace ℝ (Fin d)),
      t.card ≤ d + 1 ∧ (t : Set _) ⊆ s ∧ m ∈ convexHull ℝ (t : Set _) := by
  have hmem : m ∈ ⋃ (t : Finset (EuclideanSpace ℝ (Fin d))) (_ : ↑t ⊆ s)
      (_ : AffineIndependent ℝ ((↑) : t → EuclideanSpace ℝ (Fin d))), convexHull ℝ ↑t := by
    rw [← convexHull_eq_union]
    exact hm
  simp only [exists_prop, mem_iUnion] at hmem
  obtain ⟨t, ht_sub, ht_ind, ht_mem⟩ := hmem
  exact ⟨t, affineIndependent_finset_card_le ht_ind, ht_sub, ht_mem⟩

/-- Weight form of Carathéodory in `ℝ^d`, as stated for Lemma 3. -/
theorem finite_barycentre_caratheodory {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} {m : EuclideanSpace ℝ (Fin d)}
    (hm : m ∈ convexHull ℝ s) :
    ∃ (t : Finset (EuclideanSpace ℝ (Fin d))) (w : ↥t → ℝ),
      (∀ i : ↥t, 0 ≤ w i) ∧ (∑ i : ↥t, w i = 1) ∧
      (∀ i : ↥t, (i : EuclideanSpace ℝ (Fin d)) ∈ s) ∧
      t.card ≤ d + 1 ∧ (∑ i : ↥t, w i • (i : EuclideanSpace ℝ (Fin d)) = m) := by
  obtain ⟨t, ht_card, ht_sub, ht_mem⟩ := exists_finset_card_le_of_mem_convexHull hm
  obtain ⟨W, hW_nonneg, hW_sum, hW_center⟩ := Finset.mem_convexHull'.1 ht_mem
  let w : ↥t → ℝ := fun i => W (i : EuclideanSpace ℝ (Fin d))
  refine ⟨t, w, ?_, ?_, ?_, ht_card, ?_⟩
  · intro i
    exact hW_nonneg _ i.2
  · have h : ∑ i : ↥t, w i = ∑ y ∈ t, W y := by
      simp only [w]
      exact Finset.sum_coe_sort t (fun y => W y)
    rw [h]
    exact hW_sum
  · intro i
    exact ht_sub i.2
  · have h : ∑ i : ↥t, w i • (i : EuclideanSpace ℝ (Fin d))
        = ∑ y ∈ t, W y • y := by
      simp only [w]
      exact Finset.sum_coe_sort t (fun y => W y • y)
    rw [h]
    exact hW_center

/-- Compact set form: the witnessing points form a subset of `s` of
cardinality at most `d+1`. -/
theorem exists_subset_card_le_of_mem_convexHull {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} {m : EuclideanSpace ℝ (Fin d)}
    (hm : m ∈ convexHull ℝ s) :
    ∃ (u : Set (EuclideanSpace ℝ (Fin d))), u ⊆ s ∧ u.Finite ∧ u.ncard ≤ d + 1 ∧
      m ∈ convexHull ℝ u := by
  obtain ⟨t, ht_card, ht_sub, ht_mem⟩ := exists_finset_card_le_of_mem_convexHull hm
  refine ⟨(t : Set _), ht_sub, t.finite_toSet, ?_, ht_mem⟩
  rw [Set.ncard_coe_finset]
  exact ht_card

/-! ## Finite barycentres of weighted laws -/

/-- **Finite barycentre, `Fin n` form.**  A convex combination of points of
`ℝ^d` over a finite index type is a convex combination of at most `d+1` of those
points.  This is the discrete probability form of Lemma 3, and is the form used
by Lemma 4 (ternary optimizing reduction). -/
theorem finite_barycentre_of_weights {d : ℕ} {ι : Type*} [Fintype ι]
    {g : ι → EuclideanSpace ℝ (Fin d)} {p : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    ∃ (n : ℕ) (_ : n ≤ d + 1) (pts : Fin n → ι) (w : Fin n → ℝ),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
      (∑ i, w i • g (pts i) = ∑ i, p i • g i) := by
  have hm : (∑ i, p i • g i) ∈ convexHull ℝ (g '' (univ : Set ι)) :=
    mem_convexHull_of_exists_fintype p g hp hsum
      (fun i => Set.mem_image_of_mem g (Set.mem_univ i)) rfl
  obtain ⟨t, w0, hw0_nonneg, hw0_sum, hw0_mem, ht_card, hw0_center⟩ :=
    finite_barycentre_caratheodory hm
  have hex : ∀ y : ↥t, ∃ i : ι, g i = (y : EuclideanSpace ℝ (Fin d)) := by
    intro y
    have hy : (y : EuclideanSpace ℝ (Fin d)) ∈ g '' univ := hw0_mem y
    simpa using hy
  choose pts0 hpts0 using hex
  refine ⟨t.card, ht_card,
    fun i => pts0 ((t.equivFin).symm i), fun i => w0 ((t.equivFin).symm i), ?_, ?_, ?_⟩
  · intro i
    exact hw0_nonneg _
  · have h := Equiv.sum_comp (t.equivFin).symm w0
    simpa using h.trans hw0_sum
  · have h := Equiv.sum_comp (t.equivFin).symm
      (fun y : ↥t => w0 y • (y : EuclideanSpace ℝ (Fin d)))
    have h2 : (∑ i : Fin t.card,
        w0 ((t.equivFin).symm i) • g (pts0 ((t.equivFin).symm i)))
        = ∑ i : Fin t.card,
          w0 ((t.equivFin).symm i) • ((t.equivFin).symm i : EuclideanSpace ℝ (Fin d)) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [hpts0]
    have h3 : (∑ i : Fin t.card,
        w0 ((t.equivFin).symm i) • ((t.equivFin).symm i : EuclideanSpace ℝ (Fin d)))
        = ∑ y : ↥t, w0 y • (y : EuclideanSpace ℝ (Fin d)) := by
      simpa using h
    rw [h2, h3, hw0_center]

/-- **Finite barycentre, `Finset` weights.**  The barycentre of a probability
law on a `Finset` is a convex combination of at most `d+1` of its points. -/
theorem finite_barycentre_finset {d : ℕ} {α : Type*} {s : Finset α}
    {g : α → EuclideanSpace ℝ (Fin d)} {p : α → ℝ}
    (hp : ∀ i ∈ s, 0 ≤ p i) (hsum : ∑ i ∈ s, p i = 1) :
    ∃ (n : ℕ) (_ : n ≤ d + 1) (pts : Fin n → α) (w : Fin n → ℝ),
      (∀ i, pts i ∈ s) ∧ (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
      (∑ i, w i • g (pts i) = ∑ i ∈ s, p i • g i) := by
  classical
  have hp' : ∀ i : ↥s, 0 ≤ (p (i : α)) := fun i => hp _ i.2
  have hsum' : ∑ i : ↥s, p (i : α) = 1 := by
    rw [Finset.sum_coe_sort]
    exact hsum
  obtain ⟨n, hn, pts0, w0, hw0_nonneg, hw0_sum, hw0_eq⟩ :=
    finite_barycentre_of_weights (g := fun i : ↥s => g (i : α)) hp' hsum'
  refine ⟨n, hn, fun i => (pts0 i : α), w0, ?_, hw0_nonneg, hw0_sum, ?_⟩
  · intro i
    exact (pts0 i).2
  · -- `hw0_eq : ∑ i, w0 i • g ↑(pts0 i) = ∑ i : ↥s, p ↑i • g ↑i`
    have h2 : (∑ i, w0 i • g ((pts0 i : α)))
        = ∑ i : ↥s, (p (i : α)) • g (i : α) := hw0_eq
    rw [← Finset.sum_coe_sort s (fun i => p i • g i)]
    exact h2

/-- **Discrete mean, `Fin n` form (Lemma 3 for discrete laws).**  The mean of a
discrete `ℝ^d`-valued random variable is a convex combination of at most `d+1`
of its values.  This is exactly the form of Lemma 3 used in Lemma 4. -/
theorem discrete_mean_caratheodory {d : ℕ} {ι : Type*} [Fintype ι]
    {g : ι → EuclideanSpace ℝ (Fin d)} {p : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    ∃ (n : ℕ) (_ : n ≤ d + 1) (pts : Fin n → ι) (w : Fin n → ℝ),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
      (∑ i, w i • g (pts i) = ∑ i, p i • g i) :=
  finite_barycentre_of_weights hp hsum

/-! ## Measure version for finite-range maps -/

/-- Integration of a finite-range map: the mean is the weighted sum of its
values, weighted by the real measure of the level sets. -/
lemma integral_eq_sum_measureReal_finiteRange {α : Type*} [MeasureSpace α]
    [IsFiniteMeasure (volume : Measure α)]
    {d : ℕ} {g : α → EuclideanSpace ℝ (Fin d)}
    (hg : Measurable g) (hfin : (Set.range g).Finite) :
    ∫ x, g x ∂volume = ∑ y ∈ hfin.toFinset, volume.real (g ⁻¹' {y}) • y := by
  borelize (EuclideanSpace ℝ (Fin d))
  classical
  have hdecomp : ∀ x, g x =
      ∑ y ∈ hfin.toFinset, (g ⁻¹' {y}).indicator (fun _ : α => y) x := by
    intro x
    rw [Finset.sum_eq_single (g x)]
    · simp [Set.indicator_of_mem]
    · intro y hy hne
      have hnotin : x ∉ g ⁻¹' {y} := by
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        intro h
        exact hne h.symm
      simp [Set.indicator_of_notMem hnotin]
    · intro h
      exact absurd (hfin.mem_toFinset.2 (Set.mem_range_self x)) h
  calc ∫ x, g x ∂volume
      = ∫ x, ∑ y ∈ hfin.toFinset, (g ⁻¹' {y}).indicator (fun _ : α => y) x ∂volume :=
        integral_congr_ae (ae_of_all _ hdecomp)
    _ = ∑ y ∈ hfin.toFinset,
          ∫ x, (g ⁻¹' {y}).indicator (fun _ : α => y) x ∂volume :=
        integral_finset_sum _ (fun y _ =>
          (integrable_const y).indicator (hg (measurableSet_singleton y)))
    _ = ∑ y ∈ hfin.toFinset, volume.real (g ⁻¹' {y}) • y :=
        Finset.sum_congr rfl (fun y _ => integral_indicator_const y
          (hg (measurableSet_singleton y)))

/-- The level-set weights of a finite-range law sum to one. -/
lemma sum_measureReal_preimage_singleton_finiteRange {α : Type*} [MeasureSpace α]
    [IsProbabilityMeasure (volume : Measure α)]
    {d : ℕ} {g : α → EuclideanSpace ℝ (Fin d)}
    (hg : Measurable g) (hfin : (Set.range g).Finite) :
    ∑ y ∈ hfin.toFinset, volume.real (g ⁻¹' {y}) = 1 := by
  borelize (EuclideanSpace ℝ (Fin d))
  classical
  have hdisj : Set.PairwiseDisjoint ↑hfin.toFinset (g ⁻¹' {·}) := by
    intro y hy z hz hyz
    simp only [Function.onFun, Set.disjoint_left]
    intro a hay haz
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hay haz
    exact hyz (hay.symm.trans haz)
  have hcover : (⋃ y ∈ hfin.toFinset, g ⁻¹' {y} : Set α) = univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact ⟨g x, hfin.mem_toFinset.2 (Set.mem_range_self x), rfl⟩
  have hvol : volume (⋃ y ∈ hfin.toFinset, g ⁻¹' {y}) = 1 := by
    rw [hcover]
    simp
  have hcount : (↑hfin.toFinset : Set (EuclideanSpace ℝ (Fin d))).Countable :=
    hfin.toFinset.countable_toSet
  have hbiUnion : volume (⋃ y ∈ hfin.toFinset, g ⁻¹' {y})
      = ∑' y : ↥hfin.toFinset, volume (g ⁻¹' {(y : EuclideanSpace ℝ (Fin d))}) :=
    measure_biUnion hcount hdisj (fun y _ => hg (measurableSet_singleton y))
  -- Convert the `tsum` into a `Finset.sum`.
  have htsum : (∑' y : ↥hfin.toFinset, volume (g ⁻¹' {(y : EuclideanSpace ℝ (Fin d))}))
      = ∑ y ∈ hfin.toFinset, volume (g ⁻¹' {y}) := by
    rw [tsum_fintype]
    exact Finset.sum_coe_sort hfin.toFinset (fun y => volume (g ⁻¹' {y}))
  -- Level-set measures sum to `volume univ = 1`.
  have hsum_en : ∑ y ∈ hfin.toFinset, volume (g ⁻¹' {y}) = 1 := by
    rw [← htsum, ← hbiUnion, hcover]
    simp
  -- Pass to real measures.
  have hreal : ∑ y ∈ hfin.toFinset, volume.real (g ⁻¹' {y})
      = (∑ y ∈ hfin.toFinset, volume (g ⁻¹' {y})).toReal :=
    (ENNReal.toReal_sum (fun y _ => measure_ne_top _ _)).symm
  rw [hreal, hsum_en]
  simp

/-- **Lemma 3 for finite-range maps.**  If `g : α → ℝ^d` is measurable with
finite range on a probability space, then its mean is a convex combination of at
most `d+1` values of `g`. -/
theorem lemma3_finite_range {α : Type*} [MeasureSpace α]
    [IsProbabilityMeasure (volume : Measure α)]
    {d : ℕ} {g : α → EuclideanSpace ℝ (Fin d)}
    (hg : Measurable g) (hfin : (Set.range g).Finite) :
    ∃ (n : ℕ) (_ : n ≤ d + 1) (pts : Fin n → α) (w : Fin n → ℝ),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
      (∑ i, w i • g (pts i) = ∫ x, g x ∂volume) := by
  borelize (EuclideanSpace ℝ (Fin d))
  classical
  have hsum_p : ∑ y ∈ hfin.toFinset, volume.real (g ⁻¹' {y}) = 1 :=
    sum_measureReal_preimage_singleton_finiteRange hg hfin
  have hint : ∫ x, g x ∂volume
      = ∑ y ∈ hfin.toFinset, volume.real (g ⁻¹' {y}) • y :=
    integral_eq_sum_measureReal_finiteRange hg hfin
  let u := hfin.toFinset
  have hp' : ∀ y : ↥u, 0 ≤ volume.real (g ⁻¹' {(y : EuclideanSpace ℝ (Fin d))}) :=
    fun _ => measureReal_nonneg
  have hsum' : ∑ y : ↥u, volume.real (g ⁻¹' {(y : EuclideanSpace ℝ (Fin d))}) = 1 := by
    have h : ∑ y : ↥u, volume.real (g ⁻¹' {(y : EuclideanSpace ℝ (Fin d))})
        = ∑ y ∈ u, volume.real (g ⁻¹' {y}) :=
      Finset.sum_coe_sort u (fun y => volume.real (g ⁻¹' {y}))
    rw [h]
    exact hsum_p
  obtain ⟨n, hn, idx, w, hw_nonneg, hw_sum, hw_eq⟩ :=
    finite_barycentre_of_weights (g := fun y : ↥u => (y : EuclideanSpace ℝ (Fin d)))
      hp' hsum'
  have hex : ∀ i : Fin n, ∃ x : α, g x = (idx i : EuclideanSpace ℝ (Fin d)) := by
    intro i
    have : (idx i : EuclideanSpace ℝ (Fin d)) ∈ Set.range g :=
      hfin.mem_toFinset.1 (idx i).2
    simpa using this
  choose pts hpts using hex
  refine ⟨n, hn, pts, w, hw_nonneg, hw_sum, ?_⟩
  have h1 : (∑ i, w i • g (pts i))
      = ∑ i, w i • ((idx i : EuclideanSpace ℝ (Fin d))) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [hpts i]
  rw [h1, hw_eq]
  have h2 : (∑ y : ↥u, volume.real (g ⁻¹' {(y : EuclideanSpace ℝ (Fin d))}) •
      (y : EuclideanSpace ℝ (Fin d)))
      = ∑ y ∈ u, volume.real (g ⁻¹' {y}) • y :=
    Finset.sum_coe_sort u (fun y => volume.real (g ⁻¹' {y}) • y)
  rw [h2, hint]

/-- **Lemma 3 for finite-range maps, with values in a prescribed full-measure
set.**  If `g : α → ℝ^d` is measurable with finite range on a probability space
and `volume t = 1` (with `t` measurable), then the mean of `g` is a convex
combination of at most `d+1` values `g (pts i)` with `pts i ∈ t`. -/
theorem lemma3_finite_range_fullMeasure {α : Type*} [MeasureSpace α]
    [IsProbabilityMeasure (volume : Measure α)]
    {d : ℕ} {g : α → EuclideanSpace ℝ (Fin d)}
    (hg : Measurable g) (hfin : (Set.range g).Finite)
    (t : Set α) (htmeas : MeasurableSet t) (ht : volume t = 1) :
    ∃ (n : ℕ) (_ : n ≤ d + 1) (pts : Fin n → α) (w : Fin n → ℝ),
      (∀ i, pts i ∈ t) ∧ (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
      (∑ i, w i • g (pts i) = ∫ x, g x ∂volume) := by
  borelize (EuclideanSpace ℝ (Fin d))
  classical
  -- `t` is co-null.
  have hnull : volume tᶜ = 0 := by
    have h1 : volume t + volume tᶜ = volume (univ : Set α) :=
      measure_add_measure_compl (μ := volume) htmeas
    rw [ht, measure_univ] at h1
    have h2 : (1:ENNReal) + volume tᶜ - 1 = volume tᶜ :=
      ENNReal.add_sub_cancel_left ENNReal.one_ne_top
    rw [h1] at h2
    have h3 : ((1:ENNReal) - 1) = 0 := by simp
    rw [h3] at h2
    exact h2.symm
  -- Work with values of positive level-set measure; their level sets meet `t`.
  set u := hfin.toFinset with hu
  set uPos := u.filter (fun y => (0 : ℝ) < volume.real (g ⁻¹' {y})) with huPos
  have hsub : uPos ⊆ u := filter_subset _ _
  have hzero : ∀ y ∈ u \ uPos, volume.real (g ⁻¹' {y}) = 0 := by
    intro y hy
    have hy1 : y ∈ u := mem_sdiff.1 hy |>.1
    have hy2 : y ∉ uPos := mem_sdiff.1 hy |>.2
    have hy3 : ¬((0 : ℝ) < volume.real (g ⁻¹' {y})) := by
      intro h
      apply hy2
      rw [huPos]
      exact Finset.mem_filter.2 ⟨hy1, h⟩
    have hge : (0 : ℝ) ≤ volume.real (g ⁻¹' {y}) := measureReal_nonneg
    exact le_antisymm (not_lt.1 hy3) hge
  -- The mean only sees positive-measure values.
  have hint : ∫ x, g x ∂volume = ∑ y ∈ uPos, volume.real (g ⁻¹' {y}) • y := by
    have hsplit : ∑ y ∈ u, volume.real (g ⁻¹' {y}) • y
        = ∑ y ∈ uPos, volume.real (g ⁻¹' {y}) • y
            + ∑ y ∈ u \ uPos, volume.real (g ⁻¹' {y}) • y := by
      conv_lhs => rw [← sum_sdiff hsub]
      abel
    have hvan : ∑ y ∈ u \ uPos, volume.real (g ⁻¹' {y}) • y = 0 := by
      apply sum_eq_zero
      intro y hy
      rw [hzero y hy, zero_smul]
    have key : ∑ y ∈ u, volume.real (g ⁻¹' {y}) • y
        = ∑ y ∈ uPos, volume.real (g ⁻¹' {y}) • y := by
      rw [hsplit, hvan, add_zero]
    rw [integral_eq_sum_measureReal_finiteRange hg hfin, ← hu]
    exact key
  -- The positive-measure weights form a probability vector.
  have hsum_p : ∑ y ∈ u, volume.real (g ⁻¹' {y}) = 1 := by
    rw [hu]
    exact sum_measureReal_preimage_singleton_finiteRange hg hfin
  have hsum_pos : ∑ y ∈ uPos, volume.real (g ⁻¹' {y}) = 1 := by
    have hsplit : ∑ y ∈ u, volume.real (g ⁻¹' {y})
        = ∑ y ∈ uPos, volume.real (g ⁻¹' {y})
            + ∑ y ∈ u \ uPos, volume.real (g ⁻¹' {y}) := by
      conv_lhs => rw [← sum_sdiff hsub]
      abel
    have hvan : ∑ y ∈ u \ uPos, volume.real (g ⁻¹' {y}) = 0 := by
      apply sum_eq_zero
      intro y hy
      rw [hzero y hy]
    rw [hsplit, hvan, add_zero] at hsum_p
    exact hsum_p
  -- Discrete mean over `uPos`.
  have hp' : ∀ y : ↥uPos, 0 ≤ volume.real (g ⁻¹' {(y : EuclideanSpace ℝ (Fin d))}) :=
    fun _ => measureReal_nonneg
  have hsum' : ∑ y : ↥uPos, volume.real (g ⁻¹' {(y : EuclideanSpace ℝ (Fin d))}) = 1 := by
    have h : ∑ y : ↥uPos, volume.real (g ⁻¹' {(y : EuclideanSpace ℝ (Fin d))})
        = ∑ y ∈ uPos, volume.real (g ⁻¹' {y}) :=
      sum_coe_sort uPos (fun y => volume.real (g ⁻¹' {y}))
    rw [h]
    exact hsum_pos
  obtain ⟨n, hn, idx, w, hw_nonneg, hw_sum, hw_eq⟩ :=
    finite_barycentre_of_weights (g := fun y : ↥uPos => (y : EuclideanSpace ℝ (Fin d)))
      hp' hsum'
  -- Every selected value has positive level-set measure, so its level set
  -- intersects the full-measure set `t`.
  have hex : ∀ i : Fin n, ∃ x : α, x ∈ t ∧ g x = (idx i : EuclideanSpace ℝ (Fin d)) := by
    intro i
    have hy : (idx i : EuclideanSpace ℝ (Fin d)) ∈ uPos := (idx i).2
    have hy1 : (idx i : EuclideanSpace ℝ (Fin d)) ∈ u := hsub hy
    have hy2 : (0 : ℝ) < volume.real (g ⁻¹' {(idx i : EuclideanSpace ℝ (Fin d))}) :=
      Finset.mem_filter.1 hy |>.2
    have hne : Set.Nonempty (g ⁻¹' {(idx i : EuclideanSpace ℝ (Fin d))} ∩ t) := by
      by_contra h
      have hempty : g ⁻¹' {(idx i : EuclideanSpace ℝ (Fin d))} ∩ t = ∅ :=
        Set.not_nonempty_iff_eq_empty.1 h
      have hss : g ⁻¹' {(idx i : EuclideanSpace ℝ (Fin d))} ⊆ tᶜ := by
        intro x hx
        by_contra hx'
        exact h ⟨x, hx, not_not.1 hx'⟩
      have hnull' : volume (g ⁻¹' {(idx i : EuclideanSpace ℝ (Fin d))}) = 0 :=
        measure_mono_null hss hnull
      have hreal0 : volume.real (g ⁻¹' {(idx i : EuclideanSpace ℝ (Fin d))}) = 0 :=
        measureReal_eq_zero_iff (measure_ne_top _ _) |>.2 hnull'
      exact absurd hreal0 (ne_of_gt hy2)
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, hx.2, by simpa using hx.1⟩
  choose pts hpts using hex
  refine ⟨n, hn, pts, w, ?_, hw_nonneg, hw_sum, ?_⟩
  · intro i
    exact (hpts i).1
  · have h1 : (∑ i, w i • g (pts i))
        = ∑ i, w i • ((idx i : EuclideanSpace ℝ (Fin d))) := by
      refine sum_congr rfl ?_
      intro i _
      rw [(hpts i).2]
    rw [h1, hw_eq]
    have h2 : (∑ y : ↥uPos, volume.real (g ⁻¹' {(y : EuclideanSpace ℝ (Fin d))}) •
        (y : EuclideanSpace ℝ (Fin d)))
        = ∑ y ∈ uPos, volume.real (g ⁻¹' {y}) • y :=
      sum_coe_sort uPos (fun y => volume.real (g ⁻¹' {y}) • y)
    rw [h2, hint]

end Paper15
