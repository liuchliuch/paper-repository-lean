import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Convert

/-!
# Marked multiplicity area formula

The formula is derived from Mathlib's injective Jacobian change of variables by
constructing a countable measurable injective partition of the nonsingular
locus. The singular locus and discarded null sets have null images by the
existing differential null-image and Sard theorems. `fiberMass` sums the mark
over the actual parameter preimages. The null-exception theorem permits its
application to the rectifiable bias map in equation (3.10).
-/

noncomputable section
open Set MeasureTheory MeasureTheory.Measure Filter
open scoped NNReal ENNReal Topology Function

namespace Paper35.AreaFormula

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

private def detEquiv (A : E →L[ℝ] E) (h : A.det ≠ 0) : E ≃L[ℝ] E :=
  (LinearMap.equivOfDetNeZero (A : E →ₗ[ℝ] E) h).toContinuousLinearEquiv

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
private lemma detEquiv_coe (A : E →L[ℝ] E) (h : A.det ≠ 0) :
    (detEquiv A h : E →L[ℝ] E) = A := by
  ext x
  simp [detEquiv]

private def injectivityRadius (A : E →L[ℝ] E) : ℝ≥0 :=
  if h : A.det ≠ 0 then ‖((detEquiv A h).symm : E →L[ℝ] E)‖₊⁻¹ / 2 else 1

omit [MeasurableSpace E] [BorelSpace E] in
private lemma injectivityRadius_pos (A : E →L[ℝ] E) : 0 < injectivityRadius A := by
  unfold injectivityRadius
  split_ifs with h
  · apply div_pos
    · apply inv_pos.mpr
      exact_mod_cast (detEquiv A h).symm.norm_pos
    · norm_num
  · norm_num

/-- Every differentiable map with nonzero Jacobian on a measurable set admits
an actual countable measurable partition on which it is injective. -/
theorem exists_countable_injective_partition {s : Set E} {f : E → E}
    {f' : E → E →L[ℝ] E} (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hdet : ∀ x ∈ s, (f' x).det ≠ 0) :
    ∃ t : ℕ → Set E, Pairwise (Disjoint on t) ∧
      (∀ n, MeasurableSet (t n)) ∧ (⋃ n, t n) = s ∧
      (∀ n, Set.InjOn f (t n)) := by
  rcases eq_empty_or_nonempty s with rfl | hne
  · exact ⟨fun _ => ∅, by simp [Pairwise], by simp, by simp, by simp⟩
  obtain ⟨t, A, hdis, hmeas, hcover, happ, hA⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt
      f s f' hf' injectivityRadius (fun A => (injectivityRadius_pos A).ne')
  refine ⟨fun n => s ∩ t n, ?_, fun n => hs.inter (hmeas n), ?_, ?_⟩
  · exact pairwise_disjoint_mono hdis (fun n => inter_subset_right)
  · rw [← inter_iUnion]
    exact inter_eq_self_of_subset_left hcover
  · intro n
    obtain ⟨y, hy, hAy⟩ := hA hne n
    have hnon : (A n).det ≠ 0 := by rw [hAy]; exact hdet y hy
    have hap : ApproximatesLinearOn f
        (detEquiv (A n) hnon : E →L[ℝ] E) (s ∩ t n) (injectivityRadius (A n)) := by
      rw [detEquiv_coe]
      exact happ n
    apply hap.injOn (Or.inr ?_)
    simp only [injectivityRadius, dif_pos hnon]
    apply half_lt_self
    apply inv_pos.mpr
    exact_mod_cast (detEquiv (A n) hnon).symm.norm_pos


/-- The nonnegative marked mass of all parameter preimages. -/
def fiberMass (f : E → E) (s : Set E) (a : E → ℝ≥0∞) (y : E) : ℝ≥0∞ :=
  ∑' x : {x | x ∈ s ∧ f x = y}, a x

private def imageMark (f : E → E) (s : Set E) (a : E → ℝ≥0∞) : E → ℝ≥0∞ :=
  Function.extend (s.restrict f) (s.restrict a) (fun _ => 0)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
lemma fiberMass_of_not_mem_image (f : E → E) (s : Set E) (a : E → ℝ≥0∞)
    {y : E} (hy : y ∉ f '' s) : fiberMass f s a y = 0 := by
  have hset : {x | x ∈ s ∧ f x = y} = ∅ := by
    ext x
    simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
    intro hx hfx
    exact hy ⟨x, hx, hfx⟩
  rw [fiberMass, hset]
  simp

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
lemma fiberMass_eq_imageMark_of_injOn {f : E → E} {s : Set E}
    (hf : Set.InjOn f s) (a : E → ℝ≥0∞) : fiberMass f s a = imageMark f s a := by
  classical
  funext y
  by_cases hy : y ∈ f '' s
  · rcases hy with ⟨x, hx, rfl⟩
    have hset : {z | z ∈ s ∧ f z = f x} = {x} := by
      ext z
      constructor
      · intro hz
        exact hf hz.1 hx hz.2
      · intro hz
        rw [mem_singleton_iff] at hz
        subst z
        exact ⟨hx, rfl⟩
    rw [fiberMass, hset]
    simp only [tsum_singleton]
    change a x = Function.extend (s.restrict f) (s.restrict a) (fun _ => 0)
      ((s.restrict f) ⟨x, hx⟩)
    exact (hf.injective.extend_apply (s.restrict a) (fun _ => 0) ⟨x, hx⟩).symm
  · rw [fiberMass_of_not_mem_image f s a hy]
    symm
    apply Function.extend_apply'
    rintro ⟨x, hx⟩
    exact hy ⟨x, x.2, hx⟩

variable (μ : Measure E) [IsAddHaarMeasure μ]

omit [Nontrivial E] in
lemma measurable_fiberMass_of_injOn {f : E → E} {s : Set E}
    {f' : E → E →L[ℝ] E} (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : Set.InjOn f s)
    {a : E → ℝ≥0∞} (ha : Measurable a) : Measurable (fiberMass f s a) := by
  rw [fiberMass_eq_imageMark_of_injOn hf]
  exact (measurableEmbedding_of_fderivWithin hs hf' hf).measurable_extend
    (ha.comp measurable_subtype_coe) measurable_const

omit [Nontrivial E] in
/-- Arbitrary nonnegative marks in the injective change of variables
formula, with the target written as the genuine preimage mass. -/
theorem lintegral_fiberMass_of_injOn {f : E → E} {s : Set E}
    {f' : E → E →L[ℝ] E} (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : Set.InjOn f s)
    (a : E → ℝ≥0∞) :
    (∫⁻ y, fiberMass f s a y ∂μ) =
      ∫⁻ x in s, ENNReal.ofReal |(f' x).det| * a x ∂μ := by
  have himage := measurable_image_of_fderivWithin hs hf' hf
  calc
    (∫⁻ y, fiberMass f s a y ∂μ) = ∫⁻ y in f '' s, fiberMass f s a y ∂μ := by
      rw [← lintegral_indicator himage]
      apply lintegral_congr
      intro y
      by_cases hy : y ∈ f '' s
      · simp [hy]
      · simp [hy, fiberMass_of_not_mem_image f s a hy]
    _ = ∫⁻ x in s, ENNReal.ofReal |(f' x).det| * fiberMass f s a (f x) ∂μ :=
      lintegral_image_eq_lintegral_abs_det_fderiv_mul μ hs hf' hf _
    _ = ∫⁻ x in s, ENNReal.ofReal |(f' x).det| * a x ∂μ := by
      apply setLIntegral_congr_fun hs
      intro x hx
      rw [fiberMass_eq_imageMark_of_injOn hf]
      change ENNReal.ofReal |(f' x).det| * imageMark f s a (f x) =
        ENNReal.ofReal |(f' x).det| * a x
      exact congrArg (fun b => ENNReal.ofReal |(f' x).det| * b)
        (hf.injective.extend_apply (s.restrict a) (fun _ => 0) ⟨x, hx⟩)


omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
lemma fiberMass_iUnion {f : E → E} {t : ℕ → Set E}
    (hdis : Pairwise (Disjoint on t)) (a : E → ℝ≥0∞) (y : E) :
    fiberMass f (⋃ n, t n) a y = ∑' n, fiberMass f (t n) a y := by
  unfold fiberMass
  have hset : {x | x ∈ (⋃ n, t n) ∧ f x = y} = ⋃ n, {x | x ∈ t n ∧ f x = y} := by
    ext x
    simp only [mem_setOf_eq, mem_iUnion, exists_and_right]
  rw [hset]
  apply ENNReal.tsum_biUnion
  intro i _ j _ hij
  exact (hdis hij).mono (fun x hx => hx.1) (fun x hx => hx.1)

/-- The multiplicity area formula on the nonsingular locus of a differentiable
map. Its right side sums arbitrary nonnegative measurable marks over every
parameter preimage, without an injectivity assumption on the original map. -/
theorem lintegral_fiberMass_of_det_ne_zero {f : E → E} {s : Set E}
    {f' : E → E →L[ℝ] E} (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hdet : ∀ x ∈ s, (f' x).det ≠ 0)
    {a : E → ℝ≥0∞} (ha : Measurable a) :
    (∫⁻ y, fiberMass f s a y ∂μ) =
      ∫⁻ x in s, ENNReal.ofReal |(f' x).det| * a x ∂μ := by
  obtain ⟨t, hdis, hmeas, hcover, hinj⟩ :=
    exists_countable_injective_partition hs hf' hdet
  have hsub (n : ℕ) : t n ⊆ s := by rw [← hcover]; exact subset_iUnion t n
  have hder (n : ℕ) : ∀ x ∈ t n, HasFDerivWithinAt f (f' x) (t n) x :=
    fun x hx => (hf' x (hsub n hx)).mono (hsub n)
  have hmass : fiberMass f s a = fun y => ∑' n, fiberMass f (t n) a y := by
    funext y
    rw [← hcover]
    exact fiberMass_iUnion hdis a y
  rw [hmass, lintegral_tsum]
  · simp_rw [lintegral_fiberMass_of_injOn μ (hmeas _) (hder _) (hinj _) a]
    rw [← lintegral_iUnion hmeas hdis, hcover]
  · intro n
    exact (measurable_fiberMass_of_injOn (hmeas n) (hder n) (hinj n) ha).aemeasurable

omit [Nontrivial E] in
/-- Singular points have an image of zero ambient measure, without injectivity
or measurability assumptions on the singular set. -/
theorem image_zeroJacobian_null {f : E → E} {s : Set E}
    {f' : E → E →L[ℝ] E}
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) :
    μ (f '' {x | x ∈ s ∧ (f' x).det = 0}) = 0 := by
  apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
  · intro x hx
    exact (hf' x hx.1).mono (fun z hz => hz.1)
  · intro x hx
    exact hx.2


/-- The marked multiplicity area formula for a map differentiable on a
measurable set. Singular points are discarded by Sard's null-image theorem;
no nonsingularity or injectivity assumption is imposed on the map. -/
theorem lintegral_fiberMass {f : E → E} {s : Set E}
    {f' : E → E →L[ℝ] E} (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    {a : E → ℝ≥0∞} (ha : Measurable a) :
    (∫⁻ y, fiberMass f s a y ∂μ) =
      ∫⁻ x in s, ENNReal.ofReal |(f' x).det| * a x ∂μ := by
  let nz : Set E := {x | x ∈ s ∧ (f' x).det ≠ 0}
  have hdetAE : AEMeasurable (fun x => (f' x).det) (μ.restrict s) :=
    ContinuousLinearMap.continuous_det.measurable.comp_aemeasurable
      (aemeasurable_fderivWithin μ hs hf')
  have hnz : NullMeasurableSet nz μ := by
    have hpre := hdetAE.nullMeasurableSet_preimage (measurableSet_singleton (0 : ℝ)).compl
    have hglob := (nullMeasurableSet_restrict hs.nullMeasurableSet).mp hpre
    change NullMeasurableSet ({x | (f' x).det ≠ 0} ∩ s) μ at hglob
    convert hglob using 1
    ext x
    simp only [nz, mem_setOf_eq, mem_inter_iff, and_comm]
  obtain ⟨t, htnz, htm, htae⟩ := hnz.exists_measurable_subset_ae_eq
  have hts : t ⊆ s := fun x hx => (htnz hx).1
  have hnnull : μ (nz \ t) = 0 := (ae_eq_set.mp htae).2
  have hnimage : μ (f '' (nz \ t)) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero μ
      (fun x hx => (hf' x hx.1.1).differentiableWithinAt.mono
        (fun z hz => hz.1.1)) hnnull
  have hzimage := image_zeroJacobian_null μ hf'
  have hres : μ (f '' (s \ t)) = 0 := by
    apply measure_mono_null ?_ (measure_union_null hnimage hzimage)
    rintro y ⟨x, hx, rfl⟩
    by_cases hdet : (f' x).det = 0
    · exact Or.inr ⟨x, ⟨hx.1, hdet⟩, rfl⟩
    · exact Or.inl ⟨x, ⟨⟨hx.1, hdet⟩, hx.2⟩, rfl⟩
  have hmass : fiberMass f s a =ᵐ[μ] fiberMass f t a := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hres] with y hy
    have hset : {x | x ∈ s ∧ f x = y} = {x | x ∈ t ∧ f x = y} := by
      ext x
      constructor
      · intro hx
        refine ⟨?_, hx.2⟩
        by_contra hxt
        exact hy ⟨x, ⟨hx.1, hxt⟩, hx.2⟩
      · exact fun hx => ⟨hts hx.1, hx.2⟩
    unfold fiberMass
    rw [hset]
  have hind : s.indicator (fun x => ENNReal.ofReal |(f' x).det| * a x) =ᵐ[μ]
      t.indicator (fun x => ENNReal.ofReal |(f' x).det| * a x) := by
    filter_upwards [htae] with x hx
    by_cases hxt : x ∈ t
    · simp [hxt, hts hxt]
    · by_cases hxs : x ∈ s
      · have hd : (f' x).det = 0 := by
          by_contra hne
          exact hxt ((iff_of_eq hx).mpr ⟨hxs, hne⟩)
        simp [hxt, hxs, hd]
      · simp [hxt, hxs]
  calc
    (∫⁻ y, fiberMass f s a y ∂μ) = ∫⁻ y, fiberMass f t a y ∂μ :=
      lintegral_congr_ae hmass
    _ = ∫⁻ x in t, ENNReal.ofReal |(f' x).det| * a x ∂μ :=
      lintegral_fiberMass_of_det_ne_zero μ htm
        (fun x hx => (hf' x (hts hx)).mono hts)
        (fun x hx => (htnz hx).2) ha
    _ = ∫⁻ x in s, ENNReal.ofReal |(f' x).det| * a x ∂μ := by
      rw [← lintegral_indicator htm, ← lintegral_indicator hs]
      exact lintegral_congr_ae hind.symm


/-- A null exceptional domain may be removed whenever its image is null.
In the rectifiable crossing application, Lipschitz continuity supplies the
null-image hypothesis even where the path has no derivative. -/
theorem lintegral_fiberMass_of_null_exception {f : E → E} {s N : Set E}
    {f' : E → E →L[ℝ] E} (hs : MeasurableSet s) (hN : MeasurableSet N)
    (hNnull : μ N = 0) (himage : μ (f '' (s ∩ N)) = 0)
    (hf' : ∀ x ∈ s \ N, HasFDerivWithinAt f (f' x) (s \ N) x)
    {a : E → ℝ≥0∞} (ha : Measurable a) :
    (∫⁻ y, fiberMass f s a y ∂μ) =
      ∫⁻ x in s, ENNReal.ofReal |(f' x).det| * a x ∂μ := by
  classical
  have hmass : fiberMass f s a =ᵐ[μ] fiberMass f (s \ N) a := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp himage] with y hy
    have hset : {x | x ∈ s ∧ f x = y} = {x | x ∈ s \ N ∧ f x = y} := by
      ext x
      constructor
      · intro hx
        refine ⟨⟨hx.1, ?_⟩, hx.2⟩
        intro hxN
        exact hy ⟨x, ⟨hx.1, hxN⟩, hx.2⟩
      · exact fun hx => ⟨hx.1.1, hx.2⟩
    unfold fiberMass
    rw [hset]
  calc
    (∫⁻ y, fiberMass f s a y ∂μ) = ∫⁻ y, fiberMass f (s \ N) a y ∂μ :=
      lintegral_congr_ae hmass
    _ = ∫⁻ x in s \ N, ENNReal.ofReal |(f' x).det| * a x ∂μ :=
      lintegral_fiberMass μ (hs.diff hN) hf' ha
    _ = ∫⁻ x in s, ENNReal.ofReal |(f' x).det| * a x ∂μ := by
      rw [← lintegral_indicator (hs.diff hN), ← lintegral_indicator hs]
      apply lintegral_congr_ae
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hNnull] with x hx
      by_cases hxs : x ∈ s
      · have hxD : x ∈ s \ N := ⟨hxs, hx⟩
        rw [Set.indicator_of_mem hxD, Set.indicator_of_mem hxs]
      · have hxD : x ∉ s \ N := fun h => hxs h.1
        rw [Set.indicator_of_notMem hxD, Set.indicator_of_notMem hxs]

end Paper35.AreaFormula
