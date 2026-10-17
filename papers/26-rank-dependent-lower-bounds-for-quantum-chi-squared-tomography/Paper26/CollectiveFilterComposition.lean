import Paper26.CollectiveFiltering
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Continuous retained collective measurements after projective filtering

The rectangular retained-effect embedding equals the actual filter sector
on the identity. Every retained POVM has a finite reference; we normalize
that reference without changing its actual Born measure, then compose all
branches into a genuine normalized full N-copy POVM. Its nonnegative
measurable-loss integral is the exact finite mixture of the original
retained experiments. No filtering law or statistical risk is an input.
-/
noncomputable section
open scoped BigOperators Matrix ComplexOrder Kronecker ENNReal

namespace Paper26.CollectiveFilterComposition
open QuantumModel CollectiveFiltering
open MeasureTheory ContinuousPOVM

section ReferenceNormalization
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [MeasurableSpace Ω]

theorem reference_univ_ne_zero (M : DominatedPOVM ι Ω) : M.reference Set.univ ≠ 0 := by
  intro hz
  have hm : M.reference = 0 := Measure.measure_univ_eq_zero.mp hz
  let i : ι := Classical.choice inferInstance
  have hi := M.total i i
  simp [hm] at hi

def probabilityReference (M : DominatedPOVM ι Ω) : Measure Ω :=
  (M.reference Set.univ)⁻¹ • M.reference

instance probabilityReference_isProbabilityMeasure (M : DominatedPOVM ι Ω) :
    IsProbabilityMeasure (probabilityReference M) where
  measure_univ := by
    rw [probabilityReference, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (reference_univ_ne_zero M) (measure_ne_top _ _)

/-- Every finite-reference actual POVM is natively represented with a
probability reference, by a constant scalar rescaling of its effects. -/
def probabilityVersion (M : DominatedPOVM ι Ω) : DominatedPOVM ι Ω where
  reference := probabilityReference M
  reference_finite := inferInstance
  effect y := ((M.reference Set.univ).toReal : ℂ) • M.effect y
  entry_measurable i j := by
    change Measurable (fun y => ((M.reference Set.univ).toReal : ℂ) * M.effect y i j)
    exact (M.entry_measurable i j).const_mul _
  positive_ae := by
    filter_upwards [Measure.ae_smul_measure M.positive_ae (M.reference Set.univ)⁻¹] with y hy
    exact hy.smul (RCLike.ofReal_nonneg.mpr ENNReal.toReal_nonneg)
  entry_integrable i j := by
    change Integrable (fun y => ((M.reference Set.univ).toReal : ℂ) * M.effect y i j)
      ((M.reference Set.univ)⁻¹ • M.reference)
    exact ((M.entry_integrable i j).const_mul ((M.reference Set.univ).toReal : ℂ)).smul_measure
      (ENNReal.inv_ne_top.mpr (reference_univ_ne_zero M))
  total i j := by
    change (∫ y, ((M.reference Set.univ).toReal : ℂ) • M.effect y i j
      ∂((M.reference Set.univ)⁻¹ • M.reference)) = _
    rw [integral_smul_measure, integral_smul, M.total]
    simp only [ENNReal.toReal_inv, smul_eq_mul, Complex.real_smul, ← mul_assoc]
    have hc : (M.reference Set.univ).toReal ≠ 0 :=
      (ENNReal.toReal_pos (reference_univ_ne_zero M) (measure_ne_top _ _)).ne'
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ hc, Complex.ofReal_one, one_mul]

instance probabilityVersion_reference_probability (M : DominatedPOVM ι Ω) :
    IsProbabilityMeasure (probabilityVersion M).reference := probabilityReference_isProbabilityMeasure M

/-- Constant reference rescaling preserves the entire actual Born measure. -/
theorem probabilityVersion_outcomeMeasure (M : DominatedPOVM ι Ω) (ρ : Density ι) :
    (probabilityVersion M).outcomeMeasure ρ = M.outcomeMeasure ρ := by
  have hb : (probabilityVersion M).born ρ = fun y => (M.reference Set.univ).toReal * M.born ρ y := by
    funext y
    simp [DominatedPOVM.born, DominatedPOVM.complexBorn, probabilityVersion,
      Matrix.mul_smul, Matrix.trace_smul, Complex.mul_re]
  unfold DominatedPOVM.outcomeMeasure
  rw [hb]
  change ((M.reference Set.univ)⁻¹ • M.reference).withDensity
    (fun y => ENNReal.ofReal ((M.reference Set.univ).toReal * M.born ρ y)) = _
  simp_rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (measure_ne_top M.reference Set.univ)]
  rw [withDensity_smul_measure]
  change (M.reference Set.univ)⁻¹ • M.reference.withDensity
    ((M.reference Set.univ) • (fun y => ENNReal.ofReal (M.born ρ y))) = _
  rw [withDensity_smul' _ _ (measure_ne_top _ _), smul_smul,
    ENNReal.inv_mul_cancel (reference_univ_ne_zero M) (measure_ne_top _ _), one_smul]

end ReferenceNormalization

section Selector
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

omit [Fintype α] in
theorem selector_projector (f : β → α) (hf : Function.Injective f) (x y : α) :
    (selector f * (selector f)ᴴ) x y =
      if x = y ∧ ∃ z, x = f z then (1 : ℂ) else 0 := by
  by_cases hx : ∃ z, x = f z
  · obtain ⟨z, rfl⟩ := hx
    by_cases hy : y = f z
    · subst y
      simp [selector, Matrix.mul_apply, Matrix.conjTranspose_apply, hf.eq_iff]
    · have hterm : ∀ b : β, selector f (f z) b * star (selector f y b) = 0 := by
        intro b
        by_cases hb : b = z
        · subst b
          simp [selector, hy]
        · have hz : f z ≠ f b := fun h => hb (hf h).symm
          simp [selector, hz]
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hterm, Finset.sum_const_zero]
      simp [Ne.symm hy]
  · have hnone : ∀ z, x ≠ f z := fun z hz => hx ⟨z, hz⟩
    simp [selector, Matrix.mul_apply, Matrix.conjTranspose_apply, hnone]

end Selector

section Subset
variable {N : ℕ} {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

/-- A basis vector belongs to the precise head/tail sector selected by S. -/
def compatible (S : Finset (Fin N)) (x : Fin N → (α ⊕ β)) : Prop :=
  ∀ j, match x j with
    | Sum.inl _ => j ∈ S
    | Sum.inr _ => j ∉ S

instance compatibleDecidable (S : Finset (Fin N)) (x : Fin N → (α ⊕ β)) :
    Decidable (compatible S x) := Classical.propDecidable _

theorem compatible_iff_range (S : Finset (Fin N)) (x : Fin N → (α ⊕ β)) :
    compatible S x ↔ ∃ z, x = subsetMap S z := by
  constructor
  · intro hx
    have hl : ∀ j : {j : Fin N // j ∈ S}, ∃ a : α, x j.val = Sum.inl a := by
      intro j
      have h := hx j.val
      cases he : x j.val with
      | inl a => exact ⟨a, rfl⟩
      | inr b => simp only [he] at h; exact False.elim (h j.property)
    have hr : ∀ j : {j : Fin N // j ∉ S}, ∃ b : β, x j.val = Sum.inr b := by
      intro j
      have h := hx j.val
      cases he : x j.val with
      | inl a => simp only [he] at h; exact False.elim (j.property h)
      | inr b => exact ⟨b, rfl⟩
    choose a ha using hl
    choose b hb using hr
    refine ⟨(a,b), ?_⟩
    funext j
    by_cases hj : j ∈ S
    · simpa only [subsetMap, Function.comp_apply, siteEquiv,
        Equiv.sumCompl_apply_symm_of_pos _ _ hj, sectorMap, Sum.elim_inl] using ha ⟨j,hj⟩
    · simpa only [subsetMap, Function.comp_apply, siteEquiv,
        Equiv.sumCompl_apply_symm_of_neg _ _ hj, sectorMap, Sum.elim_inr] using hb ⟨j,hj⟩
  · rintro ⟨z, rfl⟩ j
    by_cases hj : j ∈ S
    · simp [subsetMap, siteEquiv, Equiv.sumCompl_apply_symm_of_pos _ _ hj,
        sectorMap, hj]
    · simp [subsetMap, siteEquiv, Equiv.sumCompl_apply_symm_of_neg _ _ hj,
        sectorMap, hj]

theorem patternEffect_entry (S : Finset (Fin N)) (x y : Fin N → (α ⊕ β)) :
    patternEffect (fun j => decide (j ∈ S)) x y =
      if x = y ∧ compatible S x then (1 : ℂ) else 0 := by
  classical
  by_cases hxy : x = y
  · subst y
    have he : ∀ j : Fin N,
        oneFilter (α := α) (β := β) (decide (j ∈ S)) (x j) (x j) =
          if (match x j with | Sum.inl _ => j ∈ S | Sum.inr _ => j ∉ S) then (1 : ℂ) else 0 := by
      intro j
      cases hx : x j <;> by_cases hj : j ∈ S <;> simp [oneFilter, hx, hj]
    change (∏ j : Fin N, oneFilter (decide (j ∈ S)) (x j) (x j)) = _
    simp_rw [he]
    simp only [true_and]
    by_cases hc : compatible S x
    · rw [if_pos hc]
      apply Finset.prod_eq_one
      intro j _
      exact if_pos (hc j)
    · obtain ⟨j, hj⟩ := not_forall.mp hc
      rw [if_neg hc]
      exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)
  · rw [if_neg (fun h => hxy h.1)]
    obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := by
      by_contra h
      exact hxy (funext fun j => not_ne_iff.mp (not_exists.mp h j))
    change (∏ j : Fin N, oneFilter (decide (j ∈ S)) (x j) (y j)) = 0
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [oneFilter, hj]

/-- The identity retained effect is exactly the actual projective filter
sector. This is a native matrix equality, not an instrument assumption. -/
theorem subsetEffect_one (S : Finset (Fin N)) :
    subsetEffect (α := α) (β := β) S
      (1 : Matrix ({j : Fin N // j ∈ S} → α) ({j : Fin N // j ∈ S} → α) ℂ) =
        patternEffect (fun j => decide (j ∈ S)) := by
  unfold subsetEffect
  rw [Matrix.one_kronecker_one, Matrix.mul_one]
  ext x y
  rw [patternEffect_entry]
  change (selector (subsetMap (α := α) (β := β) S) *
    (selector (subsetMap (α := α) (β := β) S))ᴴ) x y = _
  rw [selector_projector _ (subsetMap_injective S)]
  simp only [compatible_iff_range]

end Subset

section EntryIntegration
variable {N : ℕ} {α β Y : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β] [MeasurableSpace Y]

theorem subsetEffect_entry_measurable (S : Finset (Fin N))
    (E : Y → Matrix ({j : Fin N // j ∈ S} → α) ({j : Fin N // j ∈ S} → α) ℂ)
    (hE : ∀ a b, Measurable (fun y => E y a b))
    (x z : Fin N → (α ⊕ β)) : Measurable (fun y => subsetEffect S (E y) x z) := by
  simp only [subsetEffect, Matrix.mul_apply, Matrix.kronecker_apply]
  apply Finset.measurable_sum Finset.univ
  intro j _
  apply Measurable.mul_const
  apply Finset.measurable_sum Finset.univ
  intro k _
  exact ((hE k.1 j.1).mul_const _).const_mul _

theorem subsetEffect_entry_integrable (S : Finset (Fin N))
    (E : Y → Matrix ({j : Fin N // j ∈ S} → α) ({j : Fin N // j ∈ S} → α) ℂ)
    (ν : Measure Y) (hE : ∀ a b, Integrable (fun y => E y a b) ν)
    (x z : Fin N → (α ⊕ β)) : Integrable (fun y => subsetEffect S (E y) x z) ν := by
  simp only [subsetEffect, Matrix.mul_apply, Matrix.kronecker_apply]
  apply integrable_finset_sum Finset.univ
  intro j _
  apply Integrable.mul_const
  apply integrable_finset_sum Finset.univ
  intro k _
  exact ((hE k.1 j.1).mul_const _).const_mul _

/-- Entrywise Bochner integration commutes with the actual rectangular
retained-effect embedding; all entries are individually integrable. -/
theorem subsetEffect_entry_integral (S : Finset (Fin N))
    (E : Y → Matrix ({j : Fin N // j ∈ S} → α) ({j : Fin N // j ∈ S} → α) ℂ)
    (ν : Measure Y) (hE : ∀ a b, Integrable (fun y => E y a b) ν)
    (x z : Fin N → (α ⊕ β)) :
    (∫ y, subsetEffect S (E y) x z ∂ν) =
      subsetEffect S (fun a b => ∫ y, E y a b ∂ν) x z := by
  simp only [subsetEffect, Matrix.mul_apply, Matrix.kronecker_apply]
  rw [integral_finset_sum Finset.univ (fun j _ =>
    (integrable_finset_sum Finset.univ (fun k _ =>
      ((hE k.1 j.1).mul_const _).const_mul _)).mul_const _)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_mul_const, integral_finset_sum Finset.univ (fun k _ =>
    ((hE k.1 j.1).mul_const _).const_mul _)]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_const_mul]
  change subsetIsometry S x k * (∫ y, E y k.1 j.1 *
    (1 : Matrix ({j : Fin N // j ∉ S} → β) ({j : Fin N // j ∉ S} → β) ℂ) k.2 j.2 ∂ν) = _
  rw [integral_mul_const]
  rfl

theorem subsetPOVM_total (S : Finset (Fin N))
    (M : DominatedPOVM ({j : Fin N // j ∈ S} → α) Y) (x z : Fin N → (α ⊕ β)) :
    (∫ y, subsetEffect S (M.effect y) x z ∂M.reference) =
      patternEffect (fun j => decide (j ∈ S)) x z := by
  rw [subsetEffect_entry_integral S M.effect M.reference M.entry_integrable]
  have ht : (fun a b => ∫ y, M.effect y a b ∂M.reference) =
      (1 : Matrix ({j : Fin N // j ∈ S} → α) ({j : Fin N // j ∈ S} → α) ℂ) := by
    ext a b
    exact M.total a b
  rw [ht, subsetEffect_one]

end EntryIntegration

section ConditionalPOVM
variable {N : ℕ} {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β] [Nonempty α]
variable {Y : Finset (Fin N) → Type*} [∀ S, MeasurableSpace (Y S)]

local instance labelMeasurableSpace : MeasurableSpace (Finset (Fin N)) := ⊤

variable (M : ∀ S : Finset (Fin N),
  DominatedPOVM ({j : Fin N // j ∈ S} → α) (Y S))

/-- Parameter-independent probability references for every possible
conditional experiment, all sampled as unused auxiliary outcomes. -/
def auxiliaryMeasure : Measure (∀ S, Y S) :=
  Measure.pi (fun S => (probabilityVersion (M S)).reference)

instance auxiliaryMeasure_probability : IsProbabilityMeasure (auxiliaryMeasure M) := by
  unfold auxiliaryMeasure
  infer_instance

def jointReference : Measure (Finset (Fin N) × (∀ S, Y S)) :=
  Measure.count.prod (auxiliaryMeasure M)

def jointEffect (z : Finset (Fin N) × (∀ S, Y S)) :
    Matrix (Fin N → (α ⊕ β)) (Fin N → (α ⊕ β)) ℂ :=
  subsetEffect z.1 ((probabilityVersion (M z.1)).effect (z.2 z.1))

theorem jointEffect_entry_measurable (x z : Fin N → (α ⊕ β)) :
    Measurable (fun y => jointEffect (β := β) M y x z) := by
  apply measurable_from_prod_countable_right
  intro S
  exact subsetEffect_entry_measurable S _
    (fun a b => ((probabilityVersion (M S)).entry_measurable a b).comp (measurable_pi_apply S)) x z

theorem jointEffect_slice_integrable (S : Finset (Fin N)) (x z : Fin N → (α ⊕ β)) :
    Integrable (fun y : ∀ S, Y S => jointEffect (β := β) M (S,y) x z) (auxiliaryMeasure M) := by
  apply subsetEffect_entry_integrable S _ _
  intro a b
  exact integrable_comp_eval (μ := fun T => (probabilityVersion (M T)).reference) (i := S)
    ((probabilityVersion (M S)).entry_integrable a b)

theorem jointEffect_entry_integrable (x z : Fin N → (α ⊕ β)) :
    Integrable (fun y => jointEffect (β := β) M y x z) (jointReference M) := by
  apply (integrable_prod_iff (jointEffect_entry_measurable (β := β) M x z).aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ fun S => jointEffect_slice_integrable (β := β) M S x z
  · exact Integrable.of_finite

theorem jointEffect_positive_ae :
    ∀ᵐ z ∂jointReference M, (jointEffect (β := β) M z).PosSemidef := by
  have hsingle : ∀ S, ∀ᵐ y ∂auxiliaryMeasure M,
      ((probabilityVersion (M S)).effect (y S)).PosSemidef := by
    intro S
    apply ae_of_ae_map (μ := auxiliaryMeasure M) (f := Function.eval S)
      (p := fun y : Y S => ((probabilityVersion (M S)).effect y).PosSemidef)
      (measurable_pi_apply S).aemeasurable
    unfold auxiliaryMeasure
    rw [(measurePreserving_eval (fun S => (probabilityVersion (M S)).reference) S).map_eq]
    exact (probabilityVersion (M S)).positive_ae
  have hall : ∀ᵐ y ∂auxiliaryMeasure M, ∀ S,
      ((probabilityVersion (M S)).effect (y S)).PosSemidef := ae_all_iff.mpr hsingle
  have hprod : ∀ᵐ z ∂jointReference M, ∀ S,
      ((probabilityVersion (M S)).effect (z.2 S)).PosSemidef := by
    apply ae_of_ae_map (μ := jointReference M) (f := Prod.snd)
      (p := fun y : ∀ S, Y S => ∀ S, ((probabilityVersion (M S)).effect (y S)).PosSemidef)
      measurable_snd.aemeasurable
    change ∀ᵐ y ∂(Measure.count.prod (auxiliaryMeasure M)).map Prod.snd, _
    rw [Measure.map_snd_prod]
    exact Measure.ae_smul_measure hall _
  filter_upwards [hprod] with z hz
  exact subsetEffect_posSemidef z.1 _ (hz z.1)

theorem jointEffect_slice_total (S : Finset (Fin N)) (x z : Fin N → (α ⊕ β)) :
    (∫ y : ∀ S, Y S, jointEffect (β := β) M (S,y) x z ∂auxiliaryMeasure M) =
      patternEffect (fun j => decide (j ∈ S)) x z := by
  change (∫ y, (fun u : Y S => subsetEffect S ((probabilityVersion (M S)).effect u) x z) (y S)
    ∂Measure.pi (fun T => (probabilityVersion (M T)).reference)) = _
  rw [integral_comp_eval (μ := fun T => (probabilityVersion (M T)).reference) (i := S)
    (subsetEffect_entry_integrable S _ _ (probabilityVersion (M S)).entry_integrable x z).aestronglyMeasurable]
  exact subsetPOVM_total S (probabilityVersion (M S)) x z

theorem jointEffect_total (x z : Fin N → (α ⊕ β)) :
    (∫ y, jointEffect (β := β) M y x z ∂jointReference M) =
      (1 : Matrix (Fin N → (α ⊕ β)) (Fin N → (α ⊕ β)) ℂ) x z := by
  change (∫ y, jointEffect (β := β) M y x z ∂Measure.count.prod (auxiliaryMeasure M)) = _
  rw [integral_prod (μ := (Measure.count : Measure (Finset (Fin N))))
    (ν := auxiliaryMeasure M) (f := fun y => jointEffect (β := β) M y x z)
    (jointEffect_entry_integrable (β := β) M x z), integral_count]
  simp_rw [jointEffect_slice_total]
  simpa only [Matrix.sum_apply, finitePatternEquiv, Equiv.coe_fn_mk] using
    congrArg (fun A : Matrix (Fin N → (α ⊕ β)) (Fin N → (α ⊕ β)) ℂ => A x z)
      (finsetEffect_total (α := α) (β := β) N)

/-- A normalized actual full N-copy POVM: filter all copies, retain any
subset S, then apply its arbitrary continuous collective POVM. Auxiliary
outcomes from all unchosen branches are harmless parameter-free randomness. -/
def jointMeasurement : DominatedPOVM (Fin N → (α ⊕ β))
    (Finset (Fin N) × (∀ S, Y S)) where
  reference := jointReference M
  reference_finite := by unfold jointReference; infer_instance
  effect := jointEffect (β := β) M
  entry_measurable := jointEffect_entry_measurable (β := β) M
  positive_ae := jointEffect_positive_ae (β := β) M
  entry_integrable := jointEffect_entry_integrable (β := β) M
  total := jointEffect_total (β := β) M

theorem jointMeasurement_born (ρ : Density (α ⊕ β)) (hw : 0 < headMass ρ)
    (z : Finset (Fin N) × (∀ S, Y S)) :
    (jointMeasurement (β := β) M).born (TensorCopies.density ρ N) z =
      headMass ρ ^ z.1.card * (1 - headMass ρ) ^ (N - z.1.card) *
        (probabilityVersion (M z.1)).born
          (indexedDensity (J := {j : Fin N // j ∈ z.1}) (retainedState ρ hw)) (z.2 z.1) := by
  exact subset_born_factorization z.1 ρ hw _

/-- The actual continuous filtered output law is the exact finite mixture of
the original retained collective experiments. This applies to every
nonnegative measurable loss or event indicator, with infinite integrals
allowed. There is no risk assumption in this theorem. -/
theorem joint_lintegral (ρ : Density (α ⊕ β)) (hw : 0 < headMass ρ)
    (g : ∀ S, Y S → ℝ≥0∞) (hg : ∀ S, Measurable (g S)) :
    (∫⁻ z, g z.1 (z.2 z.1)
      ∂(jointMeasurement (β := β) M).outcomeMeasure (TensorCopies.density ρ N)) =
      ∑ S : Finset (Fin N),
        ENNReal.ofReal (headMass ρ ^ S.card * (1 - headMass ρ) ^ (N - S.card)) *
          ∫⁻ u, g S u ∂(M S).outcomeMeasure
            (indexedDensity (J := {j : Fin N // j ∈ S}) (retainedState ρ hw)) := by
  have hgj : Measurable (fun z : Finset (Fin N) × (∀ S, Y S) => g z.1 (z.2 z.1)) :=
    measurable_from_prod_countable_right fun S => (hg S).comp (measurable_pi_apply S)
  have hbj := ((jointMeasurement (β := β) M).born_measurable
    (TensorCopies.density ρ N)).ennreal_ofReal
  rw [DominatedPOVM.outcomeMeasure,
    lintegral_withDensity_eq_lintegral_mul _ hbj hgj]
  change (∫⁻ z, ENNReal.ofReal ((jointMeasurement (β := β) M).born
    (TensorCopies.density ρ N) z) * g z.1 (z.2 z.1)
      ∂Measure.count.prod (auxiliaryMeasure M)) = _
  rw [lintegral_prod _ (hbj.mul hgj).aemeasurable, lintegral_count, tsum_fintype]
  apply Finset.sum_congr rfl
  intro S _
  let τ : Density ({j : Fin N // j ∈ S} → α) :=
    indexedDensity (J := {j : Fin N // j ∈ S}) (retainedState ρ hw)
  let P := probabilityVersion (M S)
  let c : ℝ≥0∞ := ENNReal.ofReal
    (headMass ρ ^ S.card * (1 - headMass ρ) ^ (N - S.card))
  let f : Y S → ℝ≥0∞ := fun u => ENNReal.ofReal (P.born τ u) * g S u
  have hf : Measurable f := (P.born_measurable τ).ennreal_ofReal.mul (hg S)
  have hc : 0 ≤ headMass ρ ^ S.card * (1 - headMass ρ) ^ (N - S.card) :=
    mul_nonneg (pow_nonneg (headMass_nonneg ρ) _)
      (pow_nonneg (sub_nonneg.mpr (headMass_le_one ρ)) _)
  have he : (fun y : ∀ S, Y S => ENNReal.ofReal
      ((jointMeasurement (β := β) M).born (TensorCopies.density ρ N) (S,y)) * g S (y S)) =
      fun y => c * f (y S) := by
    funext y
    rw [jointMeasurement_born M ρ hw]
    change ENNReal.ofReal
      ((headMass ρ ^ S.card * (1 - headMass ρ) ^ (N - S.card)) * P.born τ (y S)) *
        g S (y S) = c * f (y S)
    rw [ENNReal.ofReal_mul hc]
    exact mul_assoc _ _ _
  rw [he]
  rw [lintegral_const_mul c (show Measurable (fun y : ∀ S, Y S => f (y S)) from
    hf.comp (measurable_pi_apply S))]
  change c * (∫⁻ y, f (y S) ∂auxiliaryMeasure M) = c * _
  congr 1
  calc
    _ = ∫⁻ u, f u ∂P.reference := by
      rw [← lintegral_map hf (measurable_pi_apply S)]
      exact congrArg (fun ν : Measure (Y S) => ∫⁻ u, f u ∂ν)
        (measurePreserving_eval (fun T => (probabilityVersion (M T)).reference) S).map_eq
    _ = ∫⁻ u, g S u ∂P.outcomeMeasure τ := by
      rw [DominatedPOVM.outcomeMeasure,
        lintegral_withDensity_eq_lintegral_mul _ (P.born_measurable τ).ennreal_ofReal (hg S)]
      rfl
    _ = _ := by rw [probabilityVersion_outcomeMeasure]

end ConditionalPOVM
end Paper26.CollectiveFilterComposition
