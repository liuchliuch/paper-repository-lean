import Mathlib.MeasureTheory.Integral.Marginal

/-! Two selected coordinates of a finite product law are integrated against
their actual product measure, while all other coordinates remain fixed. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace Paper35.PairMarginal

variable {I X : Type*} [DecidableEq I] [MeasurableSpace X]

/-- Replace exactly two distinct coordinates of a parameter tuple. -/
def replaceTwo (θ : I → X) (i j : I) (a b : X) : I → X := fun k =>
  if k = i then a else if k = j then b else θ k

omit [MeasurableSpace X] in
@[simp] lemma replaceTwo_left (θ : I → X) (i j : I) (a b : X) :
    replaceTwo θ i j a b i = a := by simp [replaceTwo]

omit [MeasurableSpace X] in
@[simp] lemma replaceTwo_right (θ : I → X) (i j : I) (hij : i ≠ j) (a b : X) :
    replaceTwo θ i j a b j = b := by simp [replaceTwo, hij.symm]

omit [MeasurableSpace X] in
lemma replaceTwo_other (θ : I → X) (i j : I) (a b : X) {k : I}
    (hki : k ≠ i) (hkj : k ≠ j) : replaceTwo θ i j a b k = θ k := by
  simp [replaceTwo, hki, hkj]

omit [MeasurableSpace X] in
lemma replaceTwo_eq_update (θ : I → X) (i j : I) (hij : i ≠ j) (a b : X) :
    replaceTwo θ i j a b = Function.update (Function.update θ i a) j b := by
  funext k
  by_cases hki : k = i
  · subst k
    simp [replaceTwo, hij]
  by_cases hkj : k = j
  · subst k
    simp [replaceTwo, hij.symm]
  simp [replaceTwo, hki, hkj]

lemma measurable_replaceTwo_pair (θ : I → X) (i j : I) :
    Measurable (fun ab : X × X => replaceTwo θ i j ab.1 ab.2) := by
  apply measurable_pi_iff.mpr
  intro k
  by_cases hki : k = i
  · simpa [replaceTwo, hki] using (measurable_fst : Measurable (Prod.fst : X × X → X))
  by_cases hkj : k = j
  · have hji : j ≠ i := fun h => hki (hkj.trans h)
    simpa [replaceTwo, hkj, hji] using (measurable_snd : Measurable (Prod.snd : X × X → X))
  simp only [replaceTwo, if_neg hki, if_neg hkj]
  exact measurable_const

variable (μ : I → Measure X) [∀ i, SigmaFinite (μ i)]

/-- The two-coordinate marginal in the original independent product law. -/
theorem lmarginal_pair_eq_iterated (i j : I) (hij : i ≠ j)
    (f : (I → X) → ℝ≥0∞) (hf : Measurable f) (θ : I → X) :
    lmarginal μ {i, j} f θ =
      ∫⁻ a, ∫⁻ b, f (replaceTwo θ i j a b) ∂μ j ∂μ i := by
  rw [lmarginal_insert (μ := μ) (s := {j}) (i := i) f hf (by simp [hij]) θ]
  simp_rw [lmarginal_singleton]
  apply lintegral_congr
  intro a
  apply lintegral_congr
  intro b
  exact congrArg f (replaceTwo_eq_update θ i j hij a b).symm

/-- The selected pair carries `μᵢ.prod μⱼ`; the factors need not agree. -/
theorem lmarginal_pair_eq_product (i j : I) (hij : i ≠ j)
    (f : (I → X) → ℝ≥0∞) (hf : Measurable f) (θ : I → X) :
    lmarginal μ {i, j} f θ =
      ∫⁻ ab, f (replaceTwo θ i j ab.1 ab.2) ∂(μ i).prod (μ j) := by
  rw [lmarginal_pair_eq_iterated μ i j hij f hf θ]
  symm
  exact lintegral_prod _ (hf.comp (measurable_replaceTwo_pair θ i j)).aemeasurable

/-- Full finite-product integration with the selected two coordinates peeled
off. This is ordinary Tonelli marginalization, independent of any crossing law. -/
theorem lintegral_pi_eq_remaining_pair [Fintype I] (i j : I) (hij : i ≠ j)
    (f : (I → X) → ℝ≥0∞) (hf : Measurable f) (θ : I → X) :
    (∫⁻ x, f x ∂Measure.pi μ) =
      lmarginal μ (Finset.univ \ {i, j})
        (fun x => ∫⁻ ab, f (replaceTwo x i j ab.1 ab.2) ∂(μ i).prod (μ j)) θ := by
  have hsplit : Finset.univ \ ({i, j} : Finset I) ∪ {i, j} = Finset.univ :=
    Finset.sdiff_union_of_subset (Finset.subset_univ _)
  have hpair : lmarginal μ {i, j} f =
      fun x => ∫⁻ ab, f (replaceTwo x i j ab.1 ab.2) ∂(μ i).prod (μ j) :=
    funext (lmarginal_pair_eq_product μ i j hij f hf)
  rw [lintegral_eq_lmarginal_univ θ, ← hsplit,
    lmarginal_union μ f hf Finset.sdiff_disjoint, hpair]
  rw [hsplit]


/-- Resampling the selected coordinates from their original probability laws
preserves the full product expectation. Dummy selected coordinates in the
outer tuple integrate to mass one, simplifying the crossing Fubini assembly. -/
theorem lintegral_pi_eq_resample_pair [Fintype I] [∀ i, IsProbabilityMeasure (μ i)]
    (i j : I) (hij : i ≠ j) (f : (I → X) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂Measure.pi μ) =
      ∫⁻ x, ∫⁻ ab, f (replaceTwo x i j ab.1 ab.2) ∂(μ i).prod (μ j) ∂Measure.pi μ := by
  let g := lmarginal μ {i,j} f
  have hg : Measurable g := hf.lmarginal μ
  have hconst (x : I → X) (a b : X) : g (replaceTwo x i j a b) = g x := by
    change lmarginal μ {i,j} f (replaceTwo x i j a b) = lmarginal μ {i,j} f x
    rw [replaceTwo_eq_update x i j hij a b]
    rw [lmarginal_update_of_mem μ (by simp : j ∈ ({i,j} : Finset I)) f,
      lmarginal_update_of_mem μ (by simp : i ∈ ({i,j} : Finset I)) f]
  have hgg : lmarginal μ {i,j} g = g := by
    funext x
    rw [lmarginal_pair_eq_iterated μ i j hij g hg x]
    simp_rw [hconst x]
    simp
  have htotal : (∫⁻ x, f x ∂Measure.pi μ) = ∫⁻ x, g x ∂Measure.pi μ := by
    apply lintegral_eq_of_lmarginal_eq {i,j} hf hg
    rw [hgg]
  rw [htotal]
  apply lintegral_congr
  intro x
  exact lmarginal_pair_eq_product μ i j hij f hf x

end Paper35.PairMarginal
