import Paper34.MedianWitness
import Mathlib.Data.Finset.Max

/-!
# Total finite-sample medians

The candidate thresholds are observed label values. All side cardinalities are
computed on the original index finset, so equal labels and repeated locations
retain their sample multiplicities. No median oracle is an assumption.
-/

namespace Paper34

/-- Every nonempty finite indexed sample has an observed label satisfying both
weak-side median count inequalities. -/
theorem exists_sampleMedian_mem_image {ι : Type*} (I : Finset ι) (Z : ι → ℝ)
    (hI : I.Nonempty) : ∃ y ∈ I.image Z, IsSampleMedian I Z y := by
  classical
  let V := I.image Z
  have hV : V.Nonempty := hI.image Z
  let H := V.filter (fun y => I.card ≤ 2 * (I.filter (fun i => Z i ≤ y)).card)
  have hmax : I.filter (fun i => Z i ≤ V.max' hV) = I := by
    apply Finset.filter_eq_self.mpr
    intro i hi
    exact V.le_max' (Z i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  have hH : H.Nonempty := by
    refine ⟨V.max' hV, Finset.mem_filter.mpr ⟨V.max'_mem hV, ?_⟩⟩
    rw [hmax]
    omega
  let y := H.min' hH
  have hy : y ∈ H := H.min'_mem hH
  have hyV : y ∈ V := (Finset.mem_filter.mp hy).1
  have hleft : I.card ≤ 2 * (I.filter (fun i => Z i ≤ y)).card :=
    (Finset.mem_filter.mp hy).2
  let L := I.filter (fun i => Z i < y)
  have hstrict : 2 * L.card < I.card := by
    by_contra h
    have hcard : I.card ≤ 2 * L.card := Nat.le_of_not_gt h
    have hIpos : 0 < I.card := Finset.card_pos.mpr hI
    have hLpos : 0 < L.card := by omega
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hLpos
    have hiI : i ∈ I := (Finset.mem_filter.mp hi).1
    have hiy : Z i < y := (Finset.mem_filter.mp hi).2
    obtain ⟨z, hzV, hzy, hzmax⟩ := Finset.exists_next_left
      (s := V) (x := y) ⟨Z i, Finset.mem_image.mpr ⟨i, hiI, rfl⟩, hiy⟩
    have hfilter : I.filter (fun i => Z i ≤ z) = L := by
      ext k
      simp only [L, Finset.mem_filter]
      constructor
      · rintro ⟨hk, hkz⟩
        exact ⟨hk, hkz.trans_lt hzy⟩
      · rintro ⟨hk, hky⟩
        exact ⟨hk, hzmax (Z k) (Finset.mem_image.mpr ⟨k, hk, rfl⟩) hky⟩
    have hzH : z ∈ H := Finset.mem_filter.mpr ⟨hzV, by rw [hfilter]; exact hcard⟩
    have hyz : y ≤ z := H.min'_le z hzH
    exact (not_le.mpr hzy) hyz
  have hpartition : L.card + (I.filter (fun i => y ≤ Z i)).card = I.card := by
    simpa only [L, not_lt] using
      (Finset.filter_card_add_filter_neg_card_eq_card (s := I) (fun i => Z i < y))
  refine ⟨y, hyV, hleft, ?_⟩
  omega

/-- A median exists for every nonempty finite indexed real sample. -/
theorem exists_sampleMedian {ι : Type*} (I : Finset ι) (Z : ι → ℝ)
    (hI : I.Nonempty) : ∃ y, IsSampleMedian I Z y := by
  obtain ⟨y, _, hy⟩ := exists_sampleMedian_mem_image I Z hI
  exact ⟨y, hy⟩

/-- A total chosen median for a nonempty finite sample. Its correctness is
proved below rather than supplied by an oracle. -/
noncomputable def medianFor {ι : Type*} (I : Finset ι) (Z : ι → ℝ)
    (hI : I.Nonempty) : ℝ :=
  Classical.choose (exists_sampleMedian_mem_image I Z hI)

theorem medianFor_spec {ι : Type*} (I : Finset ι) (Z : ι → ℝ)
    (hI : I.Nonempty) : IsSampleMedian I Z (medianFor I Z hI) :=
  (Classical.choose_spec (exists_sampleMedian_mem_image I Z hI)).2

/-- The selected median is one of the sample labels; this is compatible with
arbitrarily many equal labels. -/
theorem medianFor_observed {ι : Type*} (I : Finset ι) (Z : ι → ℝ)
    (hI : I.Nonempty) : ∃ i ∈ I, Z i = medianFor I Z hI := by
  classical
  exact Finset.mem_image.mp (Classical.choose_spec
    (exists_sampleMedian_mem_image I Z hI)).1


/-- The actual unweighted absolute-deviation objective on indexed labels. -/
noncomputable def sampleLADSum {ι : Type*} (I : Finset ι) (Z : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ I, |t - Z i|

@[simp] lemma sampleLADSum_neg {ι : Type*} (I : Finset ι) (Z : ι → ℝ) (t : ℝ) :
    sampleLADSum I (fun i => -Z i) (-t) = sampleLADSum I Z t := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [neg_sub_neg, abs_sub_comm]

/-- Moving right from y cannot decrease LAD if at least half the indexed
observations lie weakly to the left of y. -/
lemma sampleLADSum_right_of_half {ι : Type*} (I : Finset ι) (Z : ι → ℝ)
    {y t : ℝ} (hyt : y ≤ t)
    (hhalf : I.card ≤ 2 * (I.filter (fun i => Z i ≤ y)).card) :
    sampleLADSum I Z y ≤ sampleLADSum I Z t := by
  classical
  have hsum : (∑ i ∈ I, if Z i ≤ y then t-y else -(t-y)) ≤
      ∑ i ∈ I, (|t-Z i| - |y-Z i|) := by
    apply Finset.sum_le_sum
    intro i hi
    by_cases hiz : Z i ≤ y
    · rw [if_pos hiz, abs_of_nonneg (by linarith : 0 ≤ t-Z i),
        abs_of_nonneg (by linarith : 0 ≤ y-Z i)]
      linarith
    · rw [if_neg hiz]
      have h := abs_sub_le y t (Z i)
      rw [abs_sub_comm y t, abs_of_nonneg (sub_nonneg.mpr hyt)] at h
      linarith
  simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, Finset.sum_sub_distrib] at hsum
  have hpart : ((I.filter (fun i => Z i ≤ y)).card : ℝ) +
      ((I.filter (fun i => ¬ Z i ≤ y)).card : ℝ) = I.card := by
    exact_mod_cast (Finset.filter_card_add_filter_neg_card_eq_card
      (s := I) (fun i => Z i ≤ y))
  have hhalf' : (I.card : ℝ) ≤ 2 * ((I.filter (fun i => Z i ≤ y)).card : ℝ) := by
    exact_mod_cast hhalf
  have hcoef : 0 ≤ ((I.filter (fun i => Z i ≤ y)).card : ℝ) -
      ((I.filter (fun i => ¬ Z i ≤ y)).card : ℝ) := by linarith
  have hp := mul_nonneg hcoef (sub_nonneg.mpr hyt)
  dsimp [sampleLADSum]
  nlinarith

/-- Every true sample median minimizes the actual sum of absolute deviations. -/
theorem sampleMedian_minimizes_lad {ι : Type*} (I : Finset ι) (Z : ι → ℝ)
    {y : ℝ} (hmedian : IsSampleMedian I Z y) :
    ∀ t, sampleLADSum I Z y ≤ sampleLADSum I Z t := by
  classical
  intro t
  rcases le_total y t with hyt | hty
  · exact sampleLADSum_right_of_half I Z hyt hmedian.1
  · have hhalf : I.card ≤ 2 * (I.filter (fun i => -Z i ≤ -y)).card := by
      simpa only [neg_le_neg_iff] using hmedian.2
    have h := sampleLADSum_right_of_half I (fun i => -Z i) (neg_le_neg hty) hhalf
    simpa only [sampleLADSum_neg] using h

/-- If there are no label values strictly between y and t, the LAD change is
exactly the finite-count slope times t-y. -/
lemma sampleLADSum_difference_on_empty_interval {ι : Type*} (I : Finset ι) (Z : ι → ℝ)
    {y t : ℝ} (hyt : y ≤ t)
    (hgap : ∀ i ∈ I, Z i ≤ y ∨ t ≤ Z i) :
    sampleLADSum I Z t - sampleLADSum I Z y =
      (((I.filter (fun i => Z i ≤ y)).card : ℝ) -
        ((I.filter (fun i => ¬ Z i ≤ y)).card : ℝ)) * (t-y) := by
  classical
  have hsum : (∑ i ∈ I, (|t-Z i| - |y-Z i|)) =
      ∑ i ∈ I, if Z i ≤ y then t-y else -(t-y) := by
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hiz : Z i ≤ y
    · rw [if_pos hiz, abs_of_nonneg (by linarith : 0 ≤ t-Z i),
        abs_of_nonneg (by linarith : 0 ≤ y-Z i)]
      ring
    · have hti : t ≤ Z i := (hgap i hi).resolve_left hiz
      rw [if_neg hiz, abs_of_nonpos (by linarith : t-Z i ≤ 0),
        abs_of_nonpos (by linarith : y-Z i ≤ 0)]
      ring
  simp only [Finset.sum_sub_distrib, Finset.sum_ite, Finset.sum_const, nsmul_eq_mul] at hsum
  dsimp [sampleLADSum]
  linarith [hsum]

/-- A minimizing point must have at least half the observations on its weak
left side. This follows from an actual neighboring observed label, without
using differentiation or a subgradient oracle. -/
lemma half_le_of_sampleLADSum_min {ι : Type*} (I : Finset ι) (Z : ι → ℝ)
    {y : ℝ} (hmin : ∀ t, sampleLADSum I Z y ≤ sampleLADSum I Z t) :
    I.card ≤ 2 * (I.filter (fun i => Z i ≤ y)).card := by
  classical
  by_contra hhalf
  have hex : ∃ i ∈ I, y < Z i := by
    by_contra h
    have hall : ∀ i ∈ I, Z i ≤ y := by
      intro i hi
      by_contra hiy
      exact h ⟨i, hi, lt_of_not_ge hiy⟩
    have hf : I.filter (fun i => Z i ≤ y) = I := Finset.filter_eq_self.mpr hall
    rw [hf] at hhalf
    omega
  obtain ⟨i, hi, hiy⟩ := hex
  obtain ⟨z, hz, hyz, hnext⟩ := Finset.exists_next_right
    (s := I.image Z) (x := y) ⟨Z i, Finset.mem_image.mpr ⟨i, hi, rfl⟩, hiy⟩
  have hgap : ∀ i ∈ I, Z i ≤ y ∨ z ≤ Z i := by
    intro k hk
    by_cases hky : Z k ≤ y
    · exact Or.inl hky
    · exact Or.inr (hnext (Z k) (Finset.mem_image.mpr ⟨k, hk, rfl⟩) (lt_of_not_ge hky))
  have hdiff := sampleLADSum_difference_on_empty_interval I Z hyz.le hgap
  have hpart : ((I.filter (fun i => Z i ≤ y)).card : ℝ) +
      ((I.filter (fun i => ¬ Z i ≤ y)).card : ℝ) = I.card := by
    exact_mod_cast (Finset.filter_card_add_filter_neg_card_eq_card
      (s := I) (fun i => Z i ≤ y))
  have hhalf' : 2 * ((I.filter (fun i => Z i ≤ y)).card : ℝ) < I.card := by
    exact_mod_cast (Nat.lt_of_not_ge hhalf)
  have hcoef : ((I.filter (fun i => Z i ≤ y)).card : ℝ) -
      ((I.filter (fun i => ¬ Z i ≤ y)).card : ℝ) < 0 := by linarith
  have hp := mul_neg_of_neg_of_pos hcoef (sub_pos.mpr hyz)
  have hm := hmin z
  linarith

/-- The full finite-sample characterization: LAD minimizers are exactly the
medians defined by the paper's two weak-side counting conditions. -/
theorem sampleMedian_iff_minimizes_lad {ι : Type*} (I : Finset ι) (Z : ι → ℝ) (y : ℝ) :
    IsSampleMedian I Z y ↔ ∀ t, sampleLADSum I Z y ≤ sampleLADSum I Z t := by
  classical
  constructor
  · exact sampleMedian_minimizes_lad I Z
  · intro hmin
    constructor
    · exact half_le_of_sampleLADSum_min I Z hmin
    · have hminneg : ∀ t, sampleLADSum I (fun i => -Z i) (-y) ≤
          sampleLADSum I (fun i => -Z i) t := by
        intro t
        calc
          sampleLADSum I (fun i => -Z i) (-y) = sampleLADSum I Z y := sampleLADSum_neg I Z y
          _ ≤ sampleLADSum I Z (-t) := hmin (-t)
          _ = sampleLADSum I (fun i => -Z i) t := by
            simpa only [neg_neg] using (sampleLADSum_neg I Z (-t)).symm
      have h := half_le_of_sampleLADSum_min I (fun i => -Z i) hminneg
      simpa only [neg_le_neg_iff] using h

/-- Multiplying the scalar LAD objective by a positive uniform weight preserves
its exact median minimizers. Appendix A.1's one-cell weighted average is the
special case weight = 1 / sample cardinality. -/
theorem sampleMedian_iff_minimizes_positive_weight_lad
    {ι : Type*} (I : Finset ι) (Z : ι → ℝ) (y : ℝ) {w : ℝ} (hw : 0 < w) :
    IsSampleMedian I Z y ↔
      ∀ t, w * sampleLADSum I Z y ≤ w * sampleLADSum I Z t := by
  rw [sampleMedian_iff_minimizes_lad]
  exact forall_congr' (fun _ => (mul_le_mul_iff_right₀ hw).symm)


/-- The normalized one-cell LAD objective has exactly the finite sample
medians as minimizers, as used for constant regression in Appendix A.1. -/
theorem sampleMedian_iff_minimizes_mean_lad
    {ι : Type*} (I : Finset ι) (Z : ι → ℝ) (y : ℝ) (hI : I.Nonempty) :
    IsSampleMedian I Z y ↔ ∀ t,
      (I.card : ℝ)⁻¹ * sampleLADSum I Z y ≤ (I.card : ℝ)⁻¹ * sampleLADSum I Z t :=
  sampleMedian_iff_minimizes_positive_weight_lad I Z y
    (inv_pos.mpr (Nat.cast_pos.mpr (Finset.card_pos.mpr hI)))

theorem medianFor_minimizes_mean_lad
    {ι : Type*} (I : Finset ι) (Z : ι → ℝ) (hI : I.Nonempty) :
    ∀ t, (I.card : ℝ)⁻¹ * sampleLADSum I Z (medianFor I Z hI) ≤
      (I.card : ℝ)⁻¹ * sampleLADSum I Z t :=
  (sampleMedian_iff_minimizes_mean_lad I Z (medianFor I Z hI) hI).mp
    (medianFor_spec I Z hI)

end Paper34
