import Paper18.Category.Semisimple
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Actual complements of split monomorphisms

A split monomorphism has a complement given by the kernel of its chosen
retraction. The resulting categorical biproduct decomposition proves strict
decrease of the dimension of the endomorphism space on both nonzero proper
summands.
-/

noncomputable section
open Classical CategoryTheory CategoryTheory.Limits
universe v u
namespace Paper18.Category
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasKernels C] [HasFiniteBiproducts C]
  {X Y : C} (f : X ⟶ Y) (s : SplitMono f)

/-- The projection onto the kernel of the chosen retraction. -/
def splitMonoComplementProjection : Y ⟶ kernel s.retraction :=
  kernel.lift s.retraction (𝟙 Y - s.retraction ≫ f) (by
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, s.id,
      Category.comp_id, sub_self])

omit [HasFiniteBiproducts C] in
@[reassoc (attr := simp)]
theorem splitMonoComplementProjection_ι :
    splitMonoComplementProjection f s ≫ kernel.ι s.retraction =
      𝟙 Y - s.retraction ≫ f := kernel.lift_ι _ _ _

omit [HasFiniteBiproducts C] in
@[reassoc (attr := simp)]
theorem comp_splitMonoComplementProjection :
    f ≫ splitMonoComplementProjection f s = 0 := by
  apply (cancel_mono (kernel.ι s.retraction)).mp
  simp only [Category.assoc, splitMonoComplementProjection_ι, zero_comp,
    Preadditive.comp_sub, Category.comp_id]
  rw [← Category.assoc, s.id, Category.id_comp, sub_self]

omit [HasFiniteBiproducts C] in
@[reassoc (attr := simp)]
theorem ι_splitMonoComplementProjection :
    kernel.ι s.retraction ≫ splitMonoComplementProjection f s = 𝟙 _ := by
  apply (cancel_mono (kernel.ι s.retraction)).mp
  simp only [Category.assoc, splitMonoComplementProjection_ι, Category.id_comp,
    Preadditive.comp_sub, Category.comp_id, kernel.condition_assoc,
    zero_comp, sub_zero]

/-- The actual complement isomorphism of a split monomorphism. -/
def splitMonoComplementIso : Y ≅ X ⊞ kernel s.retraction where
  hom := biprod.lift s.retraction (splitMonoComplementProjection f s)
  inv := biprod.desc f (kernel.ι s.retraction)
  hom_inv_id := by
    rw [biprod.lift_desc, splitMonoComplementProjection_ι]
    abel
  inv_hom_id := by
    apply biprod.hom_ext'
    · apply biprod.hom_ext
      · simp [s.id]
      · simp
    · apply biprod.hom_ext
      · simp
      · simp

omit [HasKernels C] [HasFiniteBiproducts C] in
/-- A nonzero split monomorphism has nonzero source. -/
theorem splitMono_source_not_isZero (hf : f ≠ 0) : ¬ IsZero X := by
  intro h
  exact hf (h.eq_zero_of_src f)

omit [HasFiniteBiproducts C] in
/-- If the complement vanishes, the chosen splitting is already an inverse. -/
theorem splitMono_isIso_of_isZero_complement (h : IsZero (kernel s.retraction)) : IsIso f := by
  have hp : splitMonoComplementProjection f s = 0 := h.eq_zero_of_tgt _
  have hid : s.retraction ≫ f = 𝟙 Y := by
    have hh := splitMonoComplementProjection_ι f s
    rw [hp, zero_comp] at hh
    exact (sub_eq_zero.mp hh.symm).symm
  exact ⟨⟨s.retraction, s.id, hid⟩⟩

omit [HasFiniteBiproducts C] in
/-- A proper split monomorphism has a nonzero actual complement. -/
theorem splitMono_complement_not_isZero (hni : ¬ IsIso f) :
    ¬ IsZero (kernel s.retraction) :=
  fun h => hni (splitMono_isIso_of_isZero_complement f s h)

section Dimensions
variable [Linear ℂ C] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]

/-- A binary biproduct represents the direct product of the two actual Hom
spaces, compatibly with their complex vector-space structures. -/
def homBiprodLinearEquiv (Z U V : C) :
    (Z ⟶ U ⊞ V) ≃ₗ[ℂ] ((Z ⟶ U) × (Z ⟶ V)) where
  toFun g := (g ≫ biprod.fst, g ≫ biprod.snd)
  invFun g := biprod.lift g.1 g.2
  left_inv g := by apply biprod.hom_ext <;> simp
  right_inv g := by cases g; simp
  map_add' g h := by simp [Preadditive.add_comp]
  map_smul' c g := by simp

/-- The dual binary biproduct universal property as a linear equivalence. -/
def biprodHomLinearEquiv (U V Z : C) :
    (U ⊞ V ⟶ Z) ≃ₗ[ℂ] ((U ⟶ Z) × (V ⟶ Z)) where
  toFun g := (biprod.inl ≫ g, biprod.inr ≫ g)
  invFun g := biprod.desc g.1 g.2
  left_inv g := by apply biprod.hom_ext' <;> simp
  right_inv g := by cases g; simp
  map_add' g h := by simp [Preadditive.comp_add]
  map_smul' c g := by simp

omit [HasKernels C] in
/-- Additivity of Hom dimension in a binary biproduct target. -/
theorem finrank_hom_biprod (Z U V : C) :
    Module.finrank ℂ (Z ⟶ U ⊞ V) =
      Module.finrank ℂ (Z ⟶ U) + Module.finrank ℂ (Z ⟶ V) := by
  rw [(homBiprodLinearEquiv Z U V).finrank_eq, Module.finrank_prod]

omit [HasKernels C] in
/-- Additivity of Hom dimension in a binary biproduct source. -/
theorem finrank_biprod_hom (U V Z : C) :
    Module.finrank ℂ (U ⊞ V ⟶ Z) =
      Module.finrank ℂ (U ⟶ Z) + Module.finrank ℂ (V ⟶ Z) := by
  rw [(biprodHomLinearEquiv U V Z).finrank_eq, Module.finrank_prod]

omit [HasKernels C] [HasFiniteBiproducts C] in
/-- A nonzero actual object has a positive-dimensional endomorphism space,
because its identity morphism is nonzero. -/
theorem end_finrank_pos_of_not_isZero (Z : C) (hZ : ¬ IsZero Z) :
    0 < Module.finrank ℂ (Z ⟶ Z) := by
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  refine ⟨𝟙 Z, ?_⟩
  exact fun h => hZ ((IsZero.iff_id_eq_zero Z).mpr h)

/-- Endomorphism dimension of the actual complement decomposition. -/
theorem end_finrank_splitMono (f : X ⟶ Y) (s : SplitMono f) :
    Module.finrank ℂ (Y ⟶ Y) =
      (Module.finrank ℂ (X ⟶ X) + Module.finrank ℂ (X ⟶ kernel s.retraction)) +
      (Module.finrank ℂ (kernel s.retraction ⟶ X) +
        Module.finrank ℂ (kernel s.retraction ⟶ kernel s.retraction)) := by
  rw [finrank_hom_iso (splitMonoComplementIso f s) (splitMonoComplementIso f s),
    finrank_biprod_hom, finrank_hom_biprod, finrank_hom_biprod]

include s in
/-- Endomorphism dimension strictly decreases on the source of a nonzero
proper split monomorphism. -/
theorem end_finrank_lt_of_splitMono (_hf : f ≠ 0) (hni : ¬ IsIso f) :
    Module.finrank ℂ (X ⟶ X) < Module.finrank ℂ (Y ⟶ Y) := by
  have hp := end_finrank_pos_of_not_isZero (kernel s.retraction)
    (splitMono_complement_not_isZero f s hni)
  have hd := end_finrank_splitMono f s
  omega

/-- Endomorphism dimension also strictly decreases on its actual complement. -/
theorem complement_end_finrank_lt_of_splitMono (hf : f ≠ 0) (_hni : ¬ IsIso f) :
    Module.finrank ℂ (kernel s.retraction ⟶ kernel s.retraction) <
      Module.finrank ℂ (Y ⟶ Y) := by
  have hp := end_finrank_pos_of_not_isZero X (splitMono_source_not_isZero f hf)
  have hd := end_finrank_splitMono f s
  omega

end Dimensions
end Paper18.Category
