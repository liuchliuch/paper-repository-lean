import Paper18.Category.DrinfeldSemisimpleRotation

/-! # Actual reciprocal summands for the weighted sliding calculation -/
noncomputable section
universe v u w
namespace Paper18.Category.Drinfeld
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
open Classical
attribute [local instance 2000] RightRigidCategory.rightDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι) (J : PivotalStructure C)

include S in
lemma simple_leftDim_ne_zero (A : C) [Simple A] : J.leftDim A ≠ 0 := by
  letI := S.simple_rightDual A
  rw [← J.rightDim_dual]
  exact J.rightDim_ne_zero S (dual C A)

/-- Actual occurrences of `Si` in the fixed decomposition of `U ⊗ Sj`. -/
abbrev averagingSlots (U : C) (i j : ι) :=
  {a : Fin (S.length (U ⊗ S.simpleObject j)) // S.label (U ⊗ S.simpleObject j) a = i}

def averagingSlotIso (U : C) (i j : ι) (a : averagingSlots S U i j) :
    S.simpleObject (S.label (U ⊗ S.simpleObject j) a.1) ≅ S.simpleObject i :=
  eqToIso (congrArg S.simpleObject a.2)

def averagingOriginalProjection (U : C) (i j : ι) (a : averagingSlots S U i j) :
    U ⊗ S.simpleObject j ⟶ S.simpleObject i :=
  S.coendProjection (U ⊗ S.simpleObject j) a.1 ≫ (averagingSlotIso S U i j a).hom

def averagingOriginalInclusion (U : C) (i j : ι) (a : averagingSlots S U i j) :
    S.simpleObject i ⟶ U ⊗ S.simpleObject j :=
  (averagingSlotIso S U i j a).inv ≫ S.coendInclusion (U ⊗ S.simpleObject j) a.1

omit [Linear ℂ C] [RightRigidCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [Simple (𝟙_ C)] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] in
lemma averagingOriginalInclusion_projection (U : C) (i j : ι)
    (a b : averagingSlots S U i j) :
    averagingOriginalInclusion S U i j a ≫ averagingOriginalProjection S U i j b =
      if a = b then 𝟙 (S.simpleObject i) else 0 := by
  by_cases hab : a = b
  · subst b
    simp only [averagingOriginalInclusion, averagingOriginalProjection,
      FiniteSemisimpleSkeleton.coendInclusion, FiniteSemisimpleSkeleton.coendProjection,
      assoc, Iso.inv_hom_id_assoc, biproduct.ι_π_self_assoc, Iso.inv_hom_id,
      ite_true]
  · have hval : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
    simp only [averagingOriginalInclusion, averagingOriginalProjection,
      FiniteSemisimpleSkeleton.coendInclusion, FiniteSemisimpleSkeleton.coendProjection,
      assoc, Iso.inv_hom_id_assoc, biproduct.ι_π_ne_assoc _ hval,
      zero_comp, comp_zero, if_neg hab]

/-- Rotate the actual projection onto a simple occurrence. -/
def averagingReciprocalInclusion (U : C) (i j : ι) (a : averagingSlots S U i j) :
    S.simpleObject j ⟶ dual C U ⊗ S.simpleObject i :=
  (averagingRotationDownEquiv J U (S.simpleObject i) (S.simpleObject j)).symm
    (averagingOriginalProjection S U i j a)

/-- Rotate its actual inclusion back, before the dimension normalization. -/
def averagingReciprocalProjection (U : C) (i j : ι) (a : averagingSlots S U i j) :
    dual C U ⊗ S.simpleObject i ⟶ S.simpleObject j :=
  (averagingRotationUpEquiv U (S.simpleObject i) (S.simpleObject j)).symm
    (averagingOriginalInclusion S U i j a)

omit [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C] [HasKernels C]
  [Simple (𝟙_ C)] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] in
@[simp] lemma averagingRotationDown_reciprocal (U : C) (i j : ι)
    (a : averagingSlots S U i j) :
    averagingRotationDown J U (S.simpleObject i) (S.simpleObject j)
      (averagingReciprocalInclusion S J U i j a) =
      averagingOriginalProjection S U i j a := by
  rw [averagingRotationDown_eq]
  exact (averagingRotationDownEquiv J U (S.simpleObject i) (S.simpleObject j)).apply_symm_apply _

omit [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C] [HasKernels C]
  [Simple (𝟙_ C)] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] in
@[simp] lemma averagingRotationUp_reciprocal (U : C) (i j : ι)
    (a : averagingSlots S U i j) :
    averagingRotationUp U (S.simpleObject i) (S.simpleObject j)
      (averagingReciprocalProjection S U i j a) =
      averagingOriginalInclusion S U i j a := by
  rw [averagingRotationUp_eq]
  exact (averagingRotationUpEquiv U (S.simpleObject i) (S.simpleObject j)).apply_symm_apply _

/-- Orthogonality of reciprocal summands includes the actual pivotal
dimension ratio. It is derived from the proved trace rotation. -/
lemma averagingReciprocalInclusion_projection (U : C) (i j : ι)
    (a b : averagingSlots S U i j) :
    averagingReciprocalInclusion S J U i j a ≫ averagingReciprocalProjection S U i j b =
      if a = b then (J.leftDim (S.simpleObject i) / J.leftDim (S.simpleObject j)) •
        𝟙 (S.simpleObject j) else 0 := by
  have ht := averagingRotation_trace J U (S.simpleObject i) (S.simpleObject j)
    (averagingReciprocalInclusion S J U i j a) (averagingReciprocalProjection S U i j b)
  rw [averagingRotationDown_reciprocal, averagingRotationUp_reciprocal,
    averagingOriginalInclusion_projection] at ht
  have hw := leftDim_smul_end J (S.simpleObject j)
    (averagingReciprocalInclusion S J U i j a ≫ averagingReciprocalProjection S U i j b)
  rw [← ht] at hw
  have hh := congrArg (fun k : S.simpleObject j ⟶ S.simpleObject j =>
    (J.leftDim (S.simpleObject j))⁻¹ • k) hw
  simp only [smul_smul, inv_mul_cancel₀ (simple_leftDim_ne_zero S J (S.simpleObject j)),
    one_smul] at hh
  rw [hh]
  by_cases hab : a = b
  · simp only [hab, ite_true]
    change ((J.leftDim (S.simpleObject j))⁻¹ * J.leftDim (S.simpleObject i)) • _ = _
    congr 1
    exact mul_comm _ _
  · simp only [if_neg hab, if_neg (Ne.symm hab), J.leftTrace_zero, map_zero,
      mul_zero, zero_smul]

include J in
omit [Simple (𝟙_ C)] in
lemma averagingSlots_card (U : C) (i j : ι) :
    Fintype.card (averagingSlots S U i j) =
      S.multiplicity (dual C U ⊗ S.simpleObject i) j := by
  calc
    _ = ∑ a : Fin (S.length (U ⊗ S.simpleObject j)),
        if S.label (U ⊗ S.simpleObject j) a = i then 1 else 0 := by
      simp only [averagingSlots, Fintype.card_subtype, Finset.card_eq_sum_ones,
        Finset.sum_filter]
    _ = S.multiplicity (U ⊗ S.simpleObject j) i := by
      rw [S.multiplicity_eq_sum]
      simp only [eq_comm]
    _ = Module.finrank ℂ (U ⊗ S.simpleObject j ⟶ S.simpleObject i) := by
      rw [S.finrank_hom_eq_sum]
      simp only [S.multiplicity_simple, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
    _ = S.multiplicity (dual C U ⊗ S.simpleObject i) j :=
      (@tensorLeftHomLinearEquiv C _ _ _ _ _ _ (S.simpleObject j) (dual C U) U
        (S.simpleObject i) (J.leftExactPairing U)).finrank_eq

/-- All reciprocal occurrences, grouped by their actual simple source. -/
abbrev averagingReciprocalIndex (U : C) (i : ι) := Σ j : ι, averagingSlots S U i j

def averagingReciprocalObject (U : C) (i : ι) : C :=
  ⨁ fun a : averagingReciprocalIndex S U i => S.simpleObject a.1

include J in
lemma averagingReciprocalObject_multiplicity (U : C) (i j : ι) :
    S.multiplicity (averagingReciprocalObject S U i) j =
      S.multiplicity (dual C U ⊗ S.simpleObject i) j := by
  rw [averagingReciprocalObject, S.multiplicity_biproduct]
  simp only [S.multiplicity_simple]
  rw [Fintype.sum_sigma]
  change (∑ k : ι, ∑ _a : averagingSlots S U i k, if j = k then 1 else 0) = _
  have hc (k : ι) : (∑ _a : averagingSlots S U i k, if j = k then 1 else 0) =
      if j = k then Fintype.card (averagingSlots S U i k) else 0 := by
    by_cases h : j = k <;> simp [h]
  simp_rw [hc]
  simpa only [Finset.sum_ite_eq, Finset.mem_univ, if_true] using averagingSlots_card S J U i j

def averagingReciprocalTo (U : C) (i : ι) :
    averagingReciprocalObject S U i ⟶ dual C U ⊗ S.simpleObject i :=
  biproduct.desc (fun a => averagingReciprocalInclusion S J U i a.1 a.2)

def averagingReciprocalFrom (U : C) (i : ι) :
    dual C U ⊗ S.simpleObject i ⟶ averagingReciprocalObject S U i :=
  biproduct.lift (fun a =>
    (J.leftDim (S.simpleObject a.1) / J.leftDim (S.simpleObject i)) •
      averagingReciprocalProjection S U i a.1 a.2)

lemma averagingReciprocalTo_from (U : C) (i : ι) :
    averagingReciprocalTo S J U i ≫ averagingReciprocalFrom S J U i =
      𝟙 (averagingReciprocalObject S U i) := by
  dsimp only [averagingReciprocalObject]
  apply biproduct.hom_ext'
  intro a
  apply biproduct.hom_ext
  intro b
  simp only [averagingReciprocalTo, averagingReciprocalFrom, assoc,
    biproduct.ι_desc_assoc, biproduct.lift_π, Linear.comp_smul,
    comp_id]
  rcases a with ⟨j, a⟩
  rcases b with ⟨k, b⟩
  by_cases hjk : j = k
  · subst k
    rw [averagingReciprocalInclusion_projection]
    by_cases hab : a = b
    · subst b
      simp only [if_true, smul_smul, div_mul_div_cancel₀
        (simple_leftDim_ne_zero S J (S.simpleObject i)),
        div_self (simple_leftDim_ne_zero S J (S.simpleObject j)), one_smul,
        biproduct.ι_π_self]
    · rw [if_neg hab, smul_zero, biproduct.ι_π_ne]
      exact fun h => hab (eq_of_heq (Sigma.mk.inj h).2)
  · have hz : averagingReciprocalInclusion S J U i j a ≫
        averagingReciprocalProjection S U i k b = 0 := by
      by_contra hn
      letI := CategoryTheory.isIso_of_hom_simple hn
      exact hjk (S.iso_injective j k ⟨asIso (averagingReciprocalInclusion S J U i j a ≫
        averagingReciprocalProjection S U i k b)⟩)
    rw [hz, smul_zero, biproduct.ι_π_ne]
    exact fun h => hjk (congrArg Sigma.fst h)

omit [MonoidalCategory C] [RightRigidCategory C] [MonoidalPreadditive C]
  [MonoidalLinear ℂ C] [HasKernels C] [Simple (𝟙_ C)] in
/-- In the actual finite semisimple category, a split inclusion with the
same simple Hom dimensions is an isomorphism. -/
lemma reverse_inverse_of_multiplicity_eq {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X)
    (hfg : f ≫ g = 𝟙 X) (hd : ∀ j, S.multiplicity X j = S.multiplicity Y j) :
    g ≫ f = 𝟙 Y := by
  apply S.hom_ext_simples
  intro j a
  let L := CategoryTheory.Linear.rightComp ℂ (S.simpleObject j) f
  have hinj : Function.Injective L := by
    intro b c hbc
    have h := congrArg (fun k => k ≫ g) hbc
    change (b ≫ f) ≫ g = (c ≫ f) ≫ g at h
    simpa only [assoc, hfg, comp_id] using h
  have hsurj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hd j)).mp hinj
  obtain ⟨b, hb⟩ := hsurj a
  change b ≫ f = a at hb
  rw [← hb]
  simp only [assoc, comp_id]
  rw [← assoc f g f, hfg, id_comp]

lemma averagingReciprocalFrom_to (U : C) (i : ι) :
    averagingReciprocalFrom S J U i ≫ averagingReciprocalTo S J U i =
      𝟙 (dual C U ⊗ S.simpleObject i) :=
  reverse_inverse_of_multiplicity_eq S (averagingReciprocalTo S J U i)
    (averagingReciprocalFrom S J U i) (averagingReciprocalTo_from S J U i)
      (averagingReciprocalObject_multiplicity S J U i)

/-- Actual reciprocal biproduct decomposition, constructed from the chosen
simple decompositions and the proved trace-weighted duality. -/
def averagingReciprocalIso (U : C) (i : ι) :
    averagingReciprocalObject S U i ≅ dual C U ⊗ S.simpleObject i where
  hom := averagingReciprocalTo S J U i
  inv := averagingReciprocalFrom S J U i
  hom_inv_id := averagingReciprocalTo_from S J U i
  inv_hom_id := averagingReciprocalFrom_to S J U i

end Paper18.Category.Drinfeld
