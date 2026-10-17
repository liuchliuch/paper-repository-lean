import Paper26.OneCopySubmatrix
import Paper26.AdaptiveModel

/-!
# A fixed-budget one-copy routine in a history-selected subspace

The outcome space is a finite disjoint union of the actual covariant block
outcomes, including the projection-failure atom.  Its reference measure does not
depend on the current unitary, the active subset, or the unknown density.
-/
noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal
open MeasureTheory
namespace Paper26.OneCopyStageRoutine
open QuantumModel

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

local instance matrixMeasurableSpace (m n : Type*) : MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))

instance finiteSubsetMeasurableSpace : MeasurableSpace (Finset ι) := ⊤
instance finiteSubsetMeasurableSingleton : MeasurableSingletonClass (Finset ι) := ⟨fun _ => trivial⟩

abbrev BlockIndex (S : Finset ι) := {i // i ∈ S}
abbrev LocalOutcome (S : Finset ι) := OneCopyObservation.Outcome (BlockIndex S)
abbrev Outcome (ι : Type u) [Fintype ι] [DecidableEq ι] := Σ S : Finset ι, LocalOutcome S
abbrev State (ι : Type u) [Fintype ι] [DecidableEq ι] := Finset ι × Matrix.unitaryGroup ι ℂ

/-- The actual columns of the current ambient unitary indexed by the active set. -/
def activeColumns (U : Matrix.unitaryGroup ι ℂ) (S : Finset ι) : Matrix ι (BlockIndex S) ℂ :=
  fun i j => (U : Matrix ι ι ℂ) i j.val

lemma activeColumns_isometry (U : Matrix.unitaryGroup ι ℂ) (S : Finset ι) :
    (activeColumns U S)ᴴ * activeColumns U S = 1 := by
  ext i j
  have h := congrArg (fun M : Matrix ι ι ℂ => M i.val j.val) (PositiveLossBridge.unitary_left U)
  simpa [activeColumns, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    Subtype.ext_iff] using h

lemma activeColumns_entry_measurable (S : Finset ι) (i : ι) (j : BlockIndex S) :
    Measurable (fun U : Matrix.unitaryGroup ι ℂ => activeColumns U S i j) :=
  (measurable_pi_apply j.val).comp ((measurable_pi_apply i).comp measurable_subtype_coe)

/-- Measurability into/out of the standard disjoint-union sigma algebra. -/
lemma measurable_sigma_mk {α : Type*} {β : α → Type*} [∀ a, MeasurableSpace (β a)] (a : α) :
    Measurable (Sigma.mk a : β a → Sigma β) :=
  Measurable.of_le_map (iInf_le _ a)

lemma measurable_from_sigma {α : Type*} {β : α → Type*} {γ : Type*}
    [∀ a, MeasurableSpace (β a)] [MeasurableSpace γ] (f : Sigma β → γ)
    (hf : ∀ a, Measurable (fun x : β a => f ⟨a,x⟩)) : Measurable f := by
  intro t ht
  exact MeasurableSpace.measurableSet_iInf.mpr (fun a => hf a ht)

lemma measurableEmbedding_sigma_mk {α : Type*} {β : α → Type*}
    [∀ a, MeasurableSpace (β a)] (a : α) :
    MeasurableEmbedding (Sigma.mk a : β a → Sigma β) where
  injective := by intro x y h; exact eq_of_heq (Sigma.mk.inj h).2
  measurable := measurable_sigma_mk a
  measurableSet_image' := by
    intro t ht
    apply MeasurableSpace.measurableSet_iInf.mpr
    intro b
    change MeasurableSet ((Sigma.mk b) ⁻¹' (Sigma.mk a '' t))
    by_cases h : b = a
    · subst b
      have hi : Function.Injective (Sigma.mk a : β a → Sigma β) := by
        intro x y h; exact eq_of_heq (Sigma.mk.inj h).2
      simpa only [hi.preimage_image] using ht
    · have he : (Sigma.mk b) ⁻¹' (Sigma.mk a '' t) = ∅ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_image, Set.mem_empty_iff_false, iff_false]
        rintro ⟨y, hy, he⟩
        exact h (congrArg (fun z : Sigma β => z.1) he).symm
      rw [he]
      exact MeasurableSet.empty

/-- Products commute measurably with a countable disjoint union. -/
lemma measurable_prod_sigma {α : Type*} {β : α → Type*} {X γ : Type*}
    [Countable α] [MeasurableSpace X] [∀ a, MeasurableSpace (β a)] [MeasurableSpace γ]
    (f : X × Sigma β → γ)
    (hf : ∀ a, Measurable (fun p : X × β a => f (p.1,⟨a,p.2⟩))) :
    Measurable f := by
  intro t ht
  have he : f ⁻¹' t = ⋃ a, (Prod.map id (Sigma.mk a)) ''
      ((fun p : X × β a => f (p.1,⟨a,p.2⟩)) ⁻¹' t) := by
    ext ⟨x,⟨a,y⟩⟩
    constructor
    · intro h
      exact Set.mem_iUnion.mpr ⟨a, ⟨(x,y),h,rfl⟩⟩
    · intro h
      rcases Set.mem_iUnion.mp h with ⟨b,p,hp,he⟩
      simpa only [← he, Prod.map_apply, id_eq] using hp
  rw [he]
  exact MeasurableSet.iUnion (fun a =>
    (MeasurableEmbedding.id.prodMap (measurableEmbedding_sigma_mk a)).measurableSet_image' (hf a ht))

/-- Effects vary measurably with both the ambient basis and the actual outcome. -/
lemma projectionEffect_joint_measurable (S : Finset ι) (i j : ι) :
    Measurable (fun p : Matrix.unitaryGroup ι ℂ × LocalOutcome S =>
      OneCopySubmatrix.projectionEffect (activeColumns p.1 S) p.2 i j) := by
  have hs : Measurable (fun p : Matrix.unitaryGroup ι ℂ × OneCopyObservation.PureFrame (BlockIndex S) =>
      OneCopySubmatrix.projectionEffect (activeColumns p.1 S) (Sum.inl p.2) i j) := by
    change Measurable (fun p : Matrix.unitaryGroup ι ℂ × OneCopyObservation.PureFrame (BlockIndex S) =>
      (Fintype.card (BlockIndex S) : ℂ) *
        ((activeColumns p.1 S * OneCopyObservation.projector p.2 * (activeColumns p.1 S)ᴴ) i j))
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    apply Measurable.const_mul
    apply Finset.measurable_sum Finset.univ
    intro a _
    apply Measurable.mul
    · apply Finset.measurable_sum Finset.univ
      intro b _
      exact ((activeColumns_entry_measurable S i b).comp measurable_fst).mul
        (((measurable_pi_apply a).comp ((measurable_pi_apply b).comp
          HaarFrames.Frame.measurable_projector_matrix)).comp measurable_snd)
    · simpa only [Complex.star_def] using Complex.continuous_conj.measurable.comp
        ((activeColumns_entry_measurable S j a).comp measurable_fst)
  have hf : Measurable (fun p : Matrix.unitaryGroup ι ℂ × Unit =>
      OneCopySubmatrix.projectionEffect (activeColumns p.1 S) (Sum.inr p.2) i j) := by
    change Measurable (fun p : Matrix.unitaryGroup ι ℂ × Unit =>
      (1 : Matrix ι ι ℂ) i j - ∑ a, activeColumns p.1 S i a * star (activeColumns p.1 S j a))
    apply Measurable.const_sub
    apply Finset.measurable_sum Finset.univ
    intro a _
    exact ((activeColumns_entry_measurable S i a).comp measurable_fst).mul
      (by
        simpa only [Complex.star_def] using
          (Complex.continuous_conj.measurable.comp
            ((activeColumns_entry_measurable S j a).comp measurable_fst)))
  have hsum : Measurable (fun p :
      (Matrix.unitaryGroup ι ℂ × OneCopyObservation.PureFrame (BlockIndex S)) ⊕
      (Matrix.unitaryGroup ι ℂ × Unit) => match p with
        | Sum.inl q => OneCopySubmatrix.projectionEffect (activeColumns q.1 S) (Sum.inl q.2) i j
        | Sum.inr q => OneCopySubmatrix.projectionEffect (activeColumns q.1 S) (Sum.inr q.2) i j) :=
    measurable_fun_sum hs hf
  have h := hsum.comp
    (MeasurableEquiv.prodSumDistrib (Matrix.unitaryGroup ι ℂ)
      (OneCopyObservation.PureFrame (BlockIndex S)) Unit).measurable
  convert h using 1
  ext ⟨U,z⟩
  cases z <;> rfl

section Coproduct
variable {α : Type*} [Fintype α] [DecidableEq α] {β : α → Type*}
  [∀ a, MeasurableSpace (β a)]

/-- A selected measurement occupies just its own tagged component. -/
def taggedEffect (E : ∀ a, β a → Matrix ι ι ℂ) (a : α) (p : Sigma β) : Matrix ι ι ℂ :=
  if h : p.1 = a then E a (h ▸ p.2) else 0

@[simp] lemma taggedEffect_same (E : ∀ a, β a → Matrix ι ι ℂ) (a : α) (z : β a) :
    taggedEffect E a ⟨a,z⟩ = E a z := by simp [taggedEffect]

@[simp] lemma taggedEffect_other (E : ∀ a, β a → Matrix ι ι ℂ) (a b : α)
    (h : b ≠ a) (z : β b) : taggedEffect E a ⟨b,z⟩ = 0 := by simp [taggedEffect, h]

lemma taggedEffect_measurable (E : ∀ a, β a → Matrix ι ι ℂ)
    (hE : ∀ a i j, Measurable (fun z => E a z i j)) (a : α) (i j : ι) :
    Measurable (fun z => taggedEffect E a z i j) := by
  apply measurable_from_sigma
  intro b
  by_cases h : b = a
  · subst b
    simpa only [taggedEffect_same] using hE a i j
  · simpa only [taggedEffect_other E a b h, Matrix.zero_apply] using
      (measurable_const : Measurable (fun _ : β b => (0 : ℂ)))

/-- The finite common reference contains every tagged local reference. -/
def coproductReference (M : ∀ a, ContinuousPOVM.DominatedPOVM ι (β a)) : Measure (Sigma β) :=
  ∑ a, (M a).reference.map (Sigma.mk a)

instance coproductReference_finite (M : ∀ a, ContinuousPOVM.DominatedPOVM ι (β a)) :
    IsFiniteMeasure (coproductReference M) := by unfold coproductReference; infer_instance

lemma taggedEffect_integrable (M : ∀ a, ContinuousPOVM.DominatedPOVM ι (β a))
    (a : α) (i j : ι) :
    Integrable (fun z => taggedEffect (fun b => (M b).effect) a z i j) (coproductReference M) := by
  apply integrable_finset_sum_measure.mpr
  intro b hb
  apply (integrable_map_measure
    (taggedEffect_measurable _ (fun b => (M b).entry_measurable) a i j).aestronglyMeasurable
    (measurable_sigma_mk b).aemeasurable).mpr
  by_cases h : b = a
  · subst b
    simpa only [Function.comp_def, taggedEffect_same] using (M a).entry_integrable i j
  · simpa only [Function.comp_def, taggedEffect_other _ a b h, Matrix.zero_apply] using
      (integrable_zero (β b) ℂ (M b).reference)

lemma taggedEffect_total (M : ∀ a, ContinuousPOVM.DominatedPOVM ι (β a))
    (a : α) (i j : ι) :
    (∫ z, taggedEffect (fun b => (M b).effect) a z i j ∂coproductReference M) =
      (1 : Matrix ι ι ℂ) i j := by
  have hi := taggedEffect_integrable M a i j
  rw [coproductReference] at hi ⊢
  rw [integral_finset_sum_measure (integrable_finset_sum_measure.mp hi)]
  have he : ∀ b, (∫ z, taggedEffect (fun c => (M c).effect) a z i j
      ∂(M b).reference.map (Sigma.mk b)) =
      if b = a then (1 : Matrix ι ι ℂ) i j else 0 := by
    intro b
    rw [integral_map (measurable_sigma_mk b).aemeasurable
      (taggedEffect_measurable _ (fun b => (M b).entry_measurable) a i j).aestronglyMeasurable]
    by_cases h : b = a
    · subst b
      simp only [taggedEffect_same, if_true, (M a).total]
    · simp only [taggedEffect_other _ a b h, Matrix.zero_apply, integral_zero, if_neg h]
  simp_rw [he]
  simp

/-- A genuine POVM with one fixed reference across the finite choice of block. -/
def coproductPOVM (M : ∀ a, ContinuousPOVM.DominatedPOVM ι (β a))
    (hpos : ∀ a z, ((M a).effect z).PosSemidef) (a : α) :
    ContinuousPOVM.DominatedPOVM ι (Sigma β) where
  reference := coproductReference M
  reference_finite := inferInstance
  effect := taggedEffect (fun b => (M b).effect) a
  entry_measurable := taggedEffect_measurable _ (fun b => (M b).entry_measurable) a
  positive_ae := ae_of_all _ (by
    intro z
    unfold taggedEffect
    split_ifs
    · exact hpos _ _
    · exact Matrix.PosSemidef.zero)
  entry_integrable := taggedEffect_integrable M a
  total := taggedEffect_total M a

/-- The tagged POVM has exactly the pushforward of the selected local Born law. -/
theorem coproductPOVM_outcomeMeasure (M : ∀ a, ContinuousPOVM.DominatedPOVM ι (β a))
    (hpos : ∀ a z, ((M a).effect z).PosSemidef) (a : α) (ρ : Density ι) :
    (coproductPOVM M hpos a).outcomeMeasure ρ = ((M a).outcomeMeasure ρ).map (Sigma.mk a) := by
  classical
  let C := coproductPOVM M hpos a
  have hb := (C.born_measurable ρ).ennreal_ofReal
  ext t ht
  rw [C.outcomeMeasure_apply ρ ht, ← lintegral_indicator ht]
  change (∫⁻ z, t.indicator (fun z => ENNReal.ofReal (C.born ρ z)) z
      ∂coproductReference M) = _
  rw [coproductReference, lintegral_finset_sum_measure]
  have he : ∀ b, (∫⁻ z, t.indicator (fun z => ENNReal.ofReal (C.born ρ z)) z
      ∂(M b).reference.map (Sigma.mk b)) =
      if b = a then (M a).outcomeMeasure ρ ((Sigma.mk a) ⁻¹' t) else 0 := by
    intro b
    rw [lintegral_map (hb.indicator ht) (measurable_sigma_mk b)]
    by_cases h : b = a
    · subst b
      rw [if_pos rfl, (M a).outcomeMeasure_apply ρ ((measurable_sigma_mk a) ht), ← lintegral_indicator]
      · congr 1
        funext z
        by_cases hzt : (⟨a,z⟩ : Sigma β) ∈ t
        · rw [Set.indicator_of_mem hzt,
            Set.indicator_of_mem (show z ∈ (Sigma.mk a) ⁻¹' t from hzt)]
          congr 1
          change (Matrix.trace (ρ.matrix * taggedEffect (fun b => (M b).effect) a ⟨a,z⟩)).re = _
          rw [taggedEffect_same]
          rfl
        · rw [Set.indicator_of_notMem hzt,
            Set.indicator_of_notMem (show z ∉ (Sigma.mk a) ⁻¹' t from hzt)]
      · exact (measurable_sigma_mk a) ht
    · rw [if_neg h]
      have hz : ∀ z : β b, C.born ρ ⟨b,z⟩ = 0 := by
        intro z
        change (Matrix.trace (ρ.matrix * taggedEffect (fun c => (M c).effect) a ⟨b,z⟩)).re = 0
        rw [taggedEffect_other _ a b h]
        simp
      change (∫⁻ z : β b, if (⟨b,z⟩ : Sigma β) ∈ t then
        ENNReal.ofReal (C.born ρ ⟨b,z⟩) else 0 ∂(M b).reference) = 0
      simp_rw [hz]
      simp
  simp_rw [he]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  exact (Measure.map_apply (measurable_sigma_mk a) ht).symm

end Coproduct

/-- Only raw first and second coordinate Haar moments are supplied.  Empty
blocks do not require a probability measure on their empty frame space. -/
structure HaarFamily (ι : Type u) [Fintype ι] [DecidableEq ι] where
  measure : ∀ S : Finset ι, Measure (OneCopyObservation.PureFrame (BlockIndex S))
  probability : ∀ S, S.Nonempty → IsProbabilityMeasure (measure S)
  moments : ∀ S, S.Nonempty → OneCopyObservation.HaarCoordinateMoments (measure S)

lemma blockIndex_nonempty (S : Finset ι) (hS : S.Nonempty) : Nonempty (BlockIndex S) := by
  rcases hS with ⟨i,hi⟩
  exact ⟨⟨i,hi⟩⟩

/-- The empty active block has a physical identity-effect failure atom. -/
def emptyPOVM (S : Finset ι) : ContinuousPOVM.DominatedPOVM ι (LocalOutcome S) where
  reference := Measure.dirac (Sum.inr ())
  reference_finite := inferInstance
  effect := fun _ => 1
  entry_measurable := fun _ _ => measurable_const
  positive_ae := ae_of_all _ (fun _ => Matrix.PosSemidef.one)
  entry_integrable := fun _ _ => integrable_const _
  total := fun i j => by simp

/-- The actual local measurement uses the current unitary columns as isometry. -/
def localPOVM (H : HaarFamily ι) (S : Finset ι) (U : Matrix.unitaryGroup ι ℂ) :
    ContinuousPOVM.DominatedPOVM ι (LocalOutcome S) :=
  if hS : S.Nonempty then
    letI : Nonempty (BlockIndex S) := blockIndex_nonempty S hS
    letI : IsProbabilityMeasure (H.measure S) := H.probability S hS
    OneCopySubmatrix.projectionPOVM (H.measure S) (H.moments S hS)
      (activeColumns U S) (activeColumns_isometry U S)
  else emptyPOVM S

lemma localPOVM_reference (H : HaarFamily ι) (S : Finset ι) (U V : Matrix.unitaryGroup ι ℂ) :
    (localPOVM H S U).reference = (localPOVM H S V).reference := by
  unfold localPOVM
  split_ifs <;> rfl

lemma localPOVM_positive (H : HaarFamily ι) (S : Finset ι) (U : Matrix.unitaryGroup ι ℂ)
    (z : LocalOutcome S) : ((localPOVM H S U).effect z).PosSemidef := by
  unfold localPOVM
  split_ifs with hS
  · letI : Nonempty (BlockIndex S) := blockIndex_nonempty S hS
    exact OneCopySubmatrix.projectionEffect_positive _ (activeColumns_isometry U S) z
  · exact (Matrix.PosSemidef.one : (1 : Matrix ι ι ℂ).PosSemidef)

lemma localPOVM_joint_measurable (H : HaarFamily ι) (S : Finset ι) (i j : ι) :
    Measurable (fun p : Matrix.unitaryGroup ι ℂ × LocalOutcome S =>
      (localPOVM H S p.1).effect p.2 i j) := by
  unfold localPOVM
  split_ifs
  · exact projectionEffect_joint_measurable S i j
  · change Measurable (fun _ : Matrix.unitaryGroup ι ℂ × LocalOutcome S => (1 : Matrix ι ι ℂ) i j)
    exact measurable_const

/-- A reference that is fixed across all active subsets and ambient bases. -/
def reference (H : HaarFamily ι) : Measure (Outcome ι) :=
  coproductReference (fun S => localPOVM H S 1)

instance reference_finite (H : HaarFamily ι) : IsFiniteMeasure (reference H) :=
  coproductReference_finite _

lemma reference_eq (H : HaarFamily ι) (U : Matrix.unitaryGroup ι ℂ) :
    reference H = coproductReference (fun S => localPOVM H S U) := by
  unfold reference coproductReference
  apply Finset.sum_congr rfl
  intro S _
  rw [localPOVM_reference H S 1 U]

/-- Genuine common-outcome POVM selected by the finite active subset and U. -/
def measurement (H : HaarFamily ι) (S : Finset ι) (U : Matrix.unitaryGroup ι ℂ) :
    ContinuousPOVM.DominatedPOVM ι (Outcome ι) :=
  coproductPOVM (fun T => localPOVM H T U) (fun T => localPOVM_positive H T U) S

lemma measurement_reference (H : HaarFamily ι) (S : Finset ι) (U : Matrix.unitaryGroup ι ℂ) :
    (measurement H S U).reference = reference H := (reference_eq H U).symm

/-- Joint measurability includes the finite subset, its current unitary, and
an arbitrary tagged outcome.  Unmatched tags have the actual zero effect. -/
lemma measurement_joint_measurable (H : HaarFamily ι) (i j : ι) :
    Measurable (fun p : State ι × Outcome ι =>
      (measurement H p.1.1 p.1.2).effect p.2 i j) := by
  change Measurable (fun p : State ι × Outcome ι =>
    taggedEffect (fun T => (localPOVM H T p.1.2).effect) p.1.1 p.2 i j)
  apply measurable_prod_sigma
  intro T
  have h : Measurable (fun p : Finset ι × (Matrix.unitaryGroup ι ℂ × LocalOutcome T) =>
      taggedEffect (fun V => (localPOVM H V p.2.1).effect) p.1 ⟨T,p.2.2⟩ i j) := by
    apply measurable_from_prod_countable_right
    intro S
    by_cases he : T = S
    · subst S
      simpa only [taggedEffect_same] using localPOVM_joint_measurable H T i j
    · simpa only [taggedEffect_other _ S T he, Matrix.zero_apply] using
        (measurable_const : Measurable (fun _ : Matrix.unitaryGroup ι ℂ × LocalOutcome T => (0 : ℂ)))
  exact h.comp ((measurable_fst.comp measurable_fst).prodMk
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

/-- A directly usable history-dependent physical one-copy step. -/
def step (H : HaarFamily ι) : AdaptiveModel.OneCopyStep ι (State ι) (Outcome ι) where
  reference := ProbabilityTheory.Kernel.const _ (reference H)
  reference_sfinite := inferInstance
  effect := fun h => (measurement H h.1 h.2).effect
  entry_measurable := measurement_joint_measurable H
  positive_ae := fun h => by
    change ∀ᵐ z ∂reference H, ((measurement H h.1 h.2).effect z).PosSemidef
    rw [← measurement_reference H h.1 h.2]
    exact (measurement H h.1 h.2).positive_ae
  entry_integrable := fun h i j => by
    change Integrable _ (reference H)
    rw [← measurement_reference H h.1 h.2]
    exact (measurement H h.1 h.2).entry_integrable i j
  total := fun h i j => by
    change (∫ z, (measurement H h.1 h.2).effect z i j ∂reference H) = _
    rw [← measurement_reference H h.1 h.2]
    exact (measurement H h.1 h.2).total i j

/-- The adaptive step's constructed Born transition is the actual selected
common-outcome POVM law, with no additional statistical-kernel assumption. -/
theorem step_bornKernel (H : HaarFamily ι) (S : Finset ι)
    (U : Matrix.unitaryGroup ι ℂ) (ρ : Density ι) :
    (step H).bornKernel ρ (S,U) = (measurement H S U).outcomeMeasure ρ := by
  rw [(step H).bornKernel_apply ρ (S,U)]
  change (reference H).withDensity
    (fun y => ENNReal.ofReal ((measurement H S U).born ρ y)) = _
  rw [← measurement_reference H S U]
  rfl

/-- Read a selected tagged outcome; wrong tags are filled by the failure atom. -/
def decode (S : Finset ι) (p : Outcome ι) : LocalOutcome S :=
  if h : p.1 = S then h ▸ p.2 else Sum.inr ()

@[simp] lemma decode_same (S : Finset ι) (z : LocalOutcome S) : decode S ⟨S,z⟩ = z := by
  simp [decode]

lemma decode_measurable (S : Finset ι) : Measurable (decode S) := by
  apply measurable_from_sigma
  intro T
  by_cases h : T = S
  · subst T
    simpa only [decode_same] using (measurable_id : Measurable (id : LocalOutcome S → LocalOutcome S))
  · simpa only [decode, dif_neg h] using
      (measurable_const : Measurable (fun _ : LocalOutcome T => (Sum.inr () : LocalOutcome S)))

theorem measurement_outcomeMeasure (H : HaarFamily ι) (S : Finset ι)
    (U : Matrix.unitaryGroup ι ℂ) (ρ : Density ι) :
    (measurement H S U).outcomeMeasure ρ =
      ((localPOVM H S U).outcomeMeasure ρ).map (Sigma.mk S) :=
  coproductPOVM_outcomeMeasure (fun T => localPOVM H T U)
    (fun T => localPOVM_positive H T U) S ρ

theorem decode_outcomeMeasure (H : HaarFamily ι) (S : Finset ι)
    (U : Matrix.unitaryGroup ι ℂ) (ρ : Density ι) :
    ((measurement H S U).outcomeMeasure ρ).map (decode S) =
      (localPOVM H S U).outcomeMeasure ρ := by
  rw [measurement_outcomeMeasure, Measure.map_map (decode_measurable S) (measurable_sigma_mk S)]
  have he : decode S ∘ Sigma.mk S = id := by funext z; exact decode_same S z
  rw [he, Measure.map_id]

/-- Decoding N fresh actual outcomes yields exactly the local N-fold Born law. -/
theorem decode_productMeasure (H : HaarFamily ι) (S : Finset ι)
    (U : Matrix.unitaryGroup ι ℂ) (ρ : Density ι) (N : ℕ) :
    (Measure.pi (fun _ : Fin N => (measurement H S U).outcomeMeasure ρ)).map
      (fun z i => decode S (z i)) =
      Measure.pi (fun _ : Fin N => (localPOVM H S U).outcomeMeasure ρ) := by
  rw [Measure.pi_map_pi (fun _ => (decode_measurable S).aemeasurable)]
  simp only [decode_outcomeMeasure]

/-- Exact statistical block law from the full ambient Born experiment. -/
theorem localPOVM_outcomeMeasure (H : HaarFamily ι) (S : Finset ι) (hS : S.Nonempty)
    (U : Matrix.unitaryGroup ι ℂ) (ρ : Density ι) :
    (localPOVM H S U).outcomeMeasure ρ =
      OneCopyObservation.outcomeMeasure (H.measure S)
        (OneCopySubmatrix.trueBlock (activeColumns U S) ρ) := by
  letI : Nonempty (BlockIndex S) := blockIndex_nonempty S hS
  letI : IsProbabilityMeasure (H.measure S) := H.probability S hS
  unfold localPOVM
  rw [dif_pos hS]
  exact OneCopySubmatrix.projectionPOVM_outcomeMeasure _ _ _ _ _

/-- The actual PSD reconstruction is independent of the unknown state and U.
Only the supplied observations and active coordinate labels enter it. -/
def estimate (F : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (S : Finset ι) (N r : ℕ) (z : Fin N → Outcome ι) : Matrix (BlockIndex S) (BlockIndex S) ℂ :=
  if hS : S.Nonempty then
    letI : Nonempty (BlockIndex S) := blockIndex_nonempty S hS
    OneCopySubmatrix.borelEstimate F N r (fun i => decode S (z i))
  else 0

lemma decode_tuple_measurable (S : Finset ι) (N : ℕ) :
    Measurable (fun z : Fin N → Outcome ι => fun i => decode S (z i)) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (decode_measurable S).comp (measurable_pi_apply i)

lemma estimate_measurable (F : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (S : Finset ι) (N r : ℕ) : Measurable (estimate F S N r) := by
  unfold estimate
  split_ifs with hS
  · letI : Nonempty (BlockIndex S) := blockIndex_nonempty S hS
    exact (OneCopySubmatrix.borelEstimate_measurable F N r).comp (decode_tuple_measurable S N)
  · exact measurable_const

lemma estimate_posSemidef (F : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (S : Finset ι) (N r : ℕ) (z : Fin N → Outcome ι) : (estimate F S N r z).PosSemidef := by
  unfold estimate
  split_ifs with hS
  · letI : Nonempty (BlockIndex S) := blockIndex_nonempty S hS
    exact OneCopySubmatrix.borelEstimate_posSemidef F N r _
  · exact Matrix.PosSemidef.zero

lemma estimate_rank (F : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (S : Finset ι) (N r : ℕ) (z : Fin N → Outcome ι) : (estimate F S N r z).rank ≤ r := by
  unfold estimate
  split_ifs with hS
  · letI : Nonempty (BlockIndex S) := blockIndex_nonempty S hS
    exact OneCopySubmatrix.borelEstimate_rank F N r _
  · simp

abbrev PositiveBlock (S : Finset ι) :=
  {C : Matrix (BlockIndex S) (BlockIndex S) ℂ // C.PosSemidef}

/-- Direct interface for the measurable multiscale spectral update. -/
def positiveEstimate (F : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (S : Finset ι) (N r : ℕ) (z : Fin N → Outcome ι) : PositiveBlock S :=
  ⟨estimate F S N r z, estimate_posSemidef F S N r z⟩

lemma positiveEstimate_measurable (F : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (S : Finset ι) (N r : ℕ) : Measurable (positiveEstimate F S N r) :=
  (estimate_measurable F S N r).subtype_mk

/-- The active subset may itself be a measurable output of the past. -/
lemma positiveEstimate_sigma_measurable
    (F : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u}) (N r : ℕ) :
    Measurable (fun p : Finset ι × (Fin N → Outcome ι) =>
      (⟨p.1,positiveEstimate F p.1 N r p.2⟩ : Σ S : Finset ι, PositiveBlock S)) := by
  apply measurable_from_prod_countable_right
  intro S
  exact (measurable_sigma_mk S).comp (positiveEstimate_measurable F S N r)

section FixedBudget
variable [Nonempty ι]
open OneCopyObservation OneCopySubmatrix

/-- The native statistical guarantee holds at every larger fixed integer budget. -/
theorem borelEstimate_success_of_budget (B : MatrixBernsteinInput ι)
    (Weyl : WeylEigenvalueInput ι)
    (F : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (μ : Measure (PureFrame ι)) [IsProbabilityMeasure μ] (H : HaarCoordinateMoments μ)
    (R : Matrix ι ι ℂ) (hR : R.PosSemidef) (hw : (Matrix.trace R).re ≤ 1)
    (r N : ℕ) (hr : 0 < r) (hrank : R.rank ≤ r) (hN : 0 < N)
    (W η β : ℝ) (hW : (Matrix.trace R).re ≤ W) (hη : 0 < η)
    (hβ : 0 < β) (hbudget : copyBudget (ι:=ι) r W η β ≤ (N:ℝ)) :
    ENNReal.ofReal (1-β) ≤ sampleMeasure μ R N
      {z | ShellAccounting.frobeniusSq (borelEstimate F N r z-R) ≤ η} := by
  letI : IsProbabilityMeasure (outcomeMeasure μ R) := ⟨outcomeMeasure_univ μ H R hR hw⟩
  letI : IsProbabilityMeasure (sampleMeasure μ R N) := by unfold sampleMeasure; infer_instance
  apply success_lower_from_failure _ _ η β (le_of_lt hβ)
  apply (estimateUsing_error_tail B Weyl (MeasurableSpectralSelection.basis F)
    (MeasurableSpectralSelection.basis_reconstruct F) μ H R hR hw r hrank N hN W hW
    _ (deviation_pos r hr η hη) η (deviation_error r hr η hη)).trans
  apply ENNReal.ofReal_le_ofReal
  apply bernstein_factor_le N _ W β (deviation_pos r hr η hη)
    (((hR.trace_nonneg).1).trans hW) hβ
  simpa only [← copyBudget_eq_bernstein (ι:=ι) r hr W η β hη] using hbudget

/-- Enlarging the ambient dimension gives a single common copy budget. -/
theorem copyBudget_mono_dimension {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (r : ℕ) (W η β : ℝ) (hW : 0 ≤ W) (hη : 0 < η)
    (hβ : 0 < β) (hβ₁ : β < 1/2) (hcard : Fintype.card κ ≤ Fintype.card ι) :
    copyBudget (ι:=κ) r W η β ≤ copyBudget (ι:=ι) r W η β := by
  have hk : (0:ℝ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos (α:=κ)
  have hd : (Fintype.card κ : ℝ) ≤ Fintype.card ι := by exact_mod_cast hcard
  have hlog : Real.log (2*(Fintype.card κ:ℝ)/β) ≤ Real.log (2*(Fintype.card ι:ℝ)/β) := by
    apply Real.log_le_log (by positivity)
    exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hβ)
  have hlog₀ : 0 ≤ Real.log (2*(Fintype.card κ:ℝ)/β) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hβ).mpr
    have hk₁ : (1:ℝ) ≤ Fintype.card κ := by exact_mod_cast Fintype.card_pos (α:=κ)
    linarith
  have hc : 0 ≤ 36*(r:ℝ)*W/η + 4*Real.sqrt ((r:ℝ)/η) := by positivity
  have he (d : ℝ) : 36*(r:ℝ)*d*W/η + 4*d*Real.sqrt ((r:ℝ)/η) =
      d*(36*(r:ℝ)*W/η+4*Real.sqrt ((r:ℝ)/η)) := by ring
  unfold copyBudget
  rw [he,he]
  exact mul_le_mul (mul_le_mul_of_nonneg_right hd hc) hlog hlog₀ (by positivity)

/-- Uniform success for the actual common-outcome physical measurement at any
fixed budget above the ambient-dimensional upper bound. -/
theorem estimate_success_of_global_budget
    (H : HaarFamily ι) (F : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (S : Finset ι) (hS : S.Nonempty)
    (B : @OneCopySubmatrix.MatrixBernsteinInput (BlockIndex S) inferInstance inferInstance
      (blockIndex_nonempty S hS))
    (Weyl : OneCopySubmatrix.WeylEigenvalueInput (BlockIndex S))
    (U : Matrix.unitaryGroup ι ℂ) (ρ : Density ι)
    (r N : ℕ) (hr : 0 < r) (hrank : ρ.matrix.rank ≤ r) (hN : 0 < N)
    (W η β : ℝ)
    (hW : (Matrix.trace (OneCopySubmatrix.trueBlock (activeColumns U S) ρ)).re ≤ W)
    (hη : 0 < η) (hβ : 0 < β) (hβ₁ : β < 1/2)
    (hbudget : copyBudget (ι:=ι) r W η β ≤ (N:ℝ)) :
    ENNReal.ofReal (1-β) ≤
      Measure.pi (fun _ : Fin N => (measurement H S U).outcomeMeasure ρ)
      {z | ShellAccounting.frobeniusSq
        (estimate F S N r z-OneCopySubmatrix.trueBlock (activeColumns U S) ρ) ≤ η} := by
  letI : Nonempty (BlockIndex S) := blockIndex_nonempty S hS
  letI : IsProbabilityMeasure (H.measure S) := H.probability S hS
  let R := OneCopySubmatrix.trueBlock (activeColumns U S) ρ
  have hR : R.PosSemidef := OneCopySubmatrix.trueBlock_posSemidef _ _
  have hm : (Matrix.trace R).re ≤ 1 :=
    OneCopySubmatrix.trueBlock_mass_le_one _ (activeColumns_isometry U S) ρ
  have hrankR : R.rank ≤ r := by
    apply le_trans _ hrank
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  have hW₀ : 0 ≤ W := ((hR.trace_nonneg).1).trans hW
  have hbudgetS : copyBudget (ι:=BlockIndex S) r W η β ≤ (N:ℝ) :=
    (copyBudget_mono_dimension (ι:=ι) (κ:=BlockIndex S) r W η β hW₀ hη hβ hβ₁
      (Fintype.card_subtype_le _)).trans hbudget
  have hg := borelEstimate_success_of_budget B Weyl F (H.measure S) (H.moments S hS)
    R hR hm r N hr hrankR hN W η β hW hη hβ hbudgetS
  let good := {z : Fin N → OneCopyObservation.Outcome (BlockIndex S) |
    ShellAccounting.frobeniusSq (OneCopySubmatrix.borelEstimate F N r z-R) ≤ η}
  have hgood : MeasurableSet good := OneCopySubmatrix.borelEstimate_success_measurable F N r R η
  have he : {z | ShellAccounting.frobeniusSq (estimate F S N r z-R) ≤ η} =
      (fun z i => decode S (z i)) ⁻¹' good := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage, good, estimate, dif_pos hS]
  change ENNReal.ofReal (1-β) ≤
    Measure.pi (fun _ : Fin N => (measurement H S U).outcomeMeasure ρ)
      {z | ShellAccounting.frobeniusSq (estimate F S N r z-R) ≤ η}
  rw [he, ← Measure.map_apply (decode_tuple_measurable S N) hgood, decode_productMeasure,
    localPOVM_outcomeMeasure H S hS U ρ]
  exact hg

/-- A single preselected integer N works in every nonempty active block. -/
theorem estimate_success_of_copies_le
    (H : HaarFamily ι) (F : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (S : Finset ι) (hS : S.Nonempty)
    (B : @OneCopySubmatrix.MatrixBernsteinInput (BlockIndex S) inferInstance inferInstance
      (blockIndex_nonempty S hS))
    (Weyl : OneCopySubmatrix.WeylEigenvalueInput (BlockIndex S))
    (U : Matrix.unitaryGroup ι ℂ) (ρ : Density ι)
    (r N : ℕ) (hr : 0 < r) (hrank : ρ.matrix.rank ≤ r)
    (W η β : ℝ)
    (hW : (Matrix.trace (OneCopySubmatrix.trueBlock (activeColumns U S) ρ)).re ≤ W)
    (hη : 0 < η) (hβ : 0 < β) (hβ₁ : β < 1/2)
    (hcopies : copies (ι:=ι) r W η β ≤ N) :
    ENNReal.ofReal (1-β) ≤
      Measure.pi (fun _ : Fin N => (measurement H S U).outcomeMeasure ρ)
      {z | ShellAccounting.frobeniusSq
        (estimate F S N r z-OneCopySubmatrix.trueBlock (activeColumns U S) ρ) ≤ η} := by
  letI : Nonempty (BlockIndex S) := blockIndex_nonempty S hS
  have hR := OneCopySubmatrix.trueBlock_posSemidef (activeColumns U S) ρ
  have hW₀ : 0 ≤ W := ((hR.trace_nonneg).1).trans hW
  apply estimate_success_of_global_budget H F S hS B Weyl U ρ r N hr hrank
    ((copies_pos r hr W η β hW₀ hη hβ hβ₁).trans_le hcopies) W η β hW hη hβ hβ₁
  exact (Nat.le_ceil _).trans (by exact_mod_cast hcopies)

/-- The empty active block is handled with the same fixed sample budget. -/
theorem estimate_success_empty
    (H : HaarFamily ι) (F : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (S : Finset ι) (hS : ¬ S.Nonempty) (U : Matrix.unitaryGroup ι ℂ) (ρ : Density ι)
    (N r : ℕ) (η β : ℝ) (hη : 0 ≤ η) (hβ : 0 ≤ β) :
    ENNReal.ofReal (1-β) ≤
      Measure.pi (fun _ : Fin N => (measurement H S U).outcomeMeasure ρ)
      {z | ShellAccounting.frobeniusSq
        (estimate F S N r z-OneCopySubmatrix.trueBlock (activeColumns U S) ρ) ≤ η} := by
  letI : IsEmpty (BlockIndex S) := ⟨by rintro ⟨i,hi⟩; exact hS ⟨i,hi⟩⟩
  have he : {z : Fin N → Outcome ι | ShellAccounting.frobeniusSq
      (estimate F S N r z-OneCopySubmatrix.trueBlock (activeColumns U S) ρ) ≤ η} = Set.univ := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    simpa [ShellAccounting.frobeniusSq] using hη
  rw [he, measure_univ]
  exact ENNReal.ofReal_le_one.mpr (by linarith)

/-- One fixed integer budget and one state-independent measurable routine work
simultaneously for every active subset, every current basis, and every input
of rank at most r satisfying the current mass bound. -/
theorem uniform_fixed_routine
    (H : HaarFamily ι) (F : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (B : ∀ (S : Finset ι) (hS : S.Nonempty),
      @OneCopySubmatrix.MatrixBernsteinInput (BlockIndex S) inferInstance inferInstance
        (blockIndex_nonempty S hS))
    (Weyl : ∀ S : Finset ι, OneCopySubmatrix.WeylEigenvalueInput (BlockIndex S))
    (r : ℕ) (hr : 0 < r) (W η β : ℝ) (hW : 0 ≤ W) (hη : 0 < η)
    (hβ : 0 < β) (hβ₁ : β < 1/2) :
    ∃ (N : ℕ) (T : ∀ S : Finset ι, (Fin N → Outcome ι) → PositiveBlock S),
      0 < N ∧ (N:ℝ) < copyBudget (ι:=ι) r W η β + 1 ∧
      (∀ S, Measurable (T S) ∧ ∀ z, (T S z).val.rank ≤ r) ∧
      ∀ (S : Finset ι) (U : Matrix.unitaryGroup ι ℂ) (ρ : Density ι),
        ρ.matrix.rank ≤ r →
        (Matrix.trace (OneCopySubmatrix.trueBlock (activeColumns U S) ρ)).re ≤ W →
        ENNReal.ofReal (1-β) ≤
          Measure.pi (fun _ : Fin N => (measurement H S U).outcomeMeasure ρ)
          {z | ShellAccounting.frobeniusSq
            ((T S z).val-OneCopySubmatrix.trueBlock (activeColumns U S) ρ) ≤ η} := by
  let N := copies (ι:=ι) r W η β
  refine ⟨N, fun S => positiveEstimate F S N r,
    copies_pos r hr W η β hW hη hβ hβ₁,
    copies_bound r hr W η β hW hη hβ hβ₁, ?_, ?_⟩
  · intro S
    exact ⟨positiveEstimate_measurable F S N r, estimate_rank F S N r⟩
  · intro S U ρ hrank hmass
    by_cases hS : S.Nonempty
    · exact estimate_success_of_copies_le H F S hS (B S hS) (Weyl S) U ρ r N hr hrank
        W η β hmass hη hβ hβ₁ (le_refl _)
    · exact estimate_success_empty H F S hS U ρ N r η β (le_of_lt hη) (le_of_lt hβ)

end FixedBudget
end Paper26.OneCopyStageRoutine
