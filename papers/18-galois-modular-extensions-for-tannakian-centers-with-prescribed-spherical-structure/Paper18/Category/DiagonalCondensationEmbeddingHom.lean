import Paper18.Category.DiagonalCondensationEmbeddingBasic
import Paper18.Category.RigidMultiplicity
import Paper18.Category.FunctorImage
import Paper18.Category.PivotalFunctor

/-! # Unit detection in actual diagonal free-module Hom spaces -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators TensorProduct MonObj
universe v u v' u' vE uE w
namespace Paper18.Category.DiagonalCondensation
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  {E : Type uE} [Category.{vE} E] [Preadditive E] [Linear ℂ E]
  [MonoidalCategory E] [MonoidalPreadditive E] [MonoidalLinear ℂ E]
  [RightRigidCategory E] [HasKernels E] [HasFiniteBiproducts E]
  [∀ X Y : E, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ E)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton E ι)
  (F : E ⥤ C) [F.Monoidal] [F.Full] [F.Faithful] [F.Additive] [F.Linear ℂ]
  (G : E ⥤ D) [G.Monoidal] [G.Full] [G.Faithful] [G.Additive] [G.Linear ℂ]

/-- Full faithfulness identifies actual maps out of the target tensor unit
with maps out of the source tensor unit. -/
lemma finrank_unit_map_simple (i : ι) :
    Module.finrank ℂ (𝟙_ C ⟶ F.obj (S.simpleObject i)) =
      if i = S.unitLabel then 1 else 0 := by
  rw [finrank_hom_iso (Functor.Monoidal.εIso F) (Iso.refl _),
    ← (fullyFaithfulHomLinearEquiv F (𝟙_ E) (S.simpleObject i)).finrank_eq,
    finrank_hom_iso S.unitIso.symm (Iso.refl _), S.finrank_simple_hom_simple]
  simp only [eq_comm]

/-- The dual second diagonal factor contributes to maps from the unit
exactly at the actual unit label. -/
lemma finrank_unit_map_dual_simple (i : ι) :
    Module.finrank ℂ (𝟙_ D ⟶ G.obj (dual E (S.simpleObject i))) =
      if i = S.unitLabel then 1 else 0 := by
  rw [finrank_hom_iso (Iso.refl _) (G.mapIso (S.dualIso i).symm),
    finrank_unit_map_simple S G]
  have hi : S.dualLabel i = S.unitLabel ↔ i = S.unitLabel := by
    constructor
    · intro h
      simpa only [S.dualLabel_involutive, S.dualLabel_unit] using congrArg S.dualLabel h
    · rintro rfl
      exact S.dualLabel_unit
  simp only [hi]

variable {A : DeligneProduct C D} [MonObj A]
  (e : A ≅ ⨁ fun i => pair (F.obj (S.simpleObject i))
    (G.obj (dual E (S.simpleObject i))))

include e in
/-- In the first-factor free Hom, only the unit diagonal summand survives.
The result is the actual factor Hom dimension. -/
lemma finrank_freeLeftHom (X Y : C) :
    Module.finrank ℂ (InternalModule.free A (pair X (𝟙_ D)) ⟶
      InternalModule.free A (pair Y (𝟙_ D))) = Module.finrank ℂ (X ⟶ Y) := by
  rw [finrank_freePairHom _ _ e]
  have h (i : ι) : Module.finrank ℂ
      (𝟙_ D ⟶ G.obj (dual E (S.simpleObject i)) ⊗ 𝟙_ D) =
        if i = S.unitLabel then 1 else 0 := by
    rw [finrank_hom_iso (Iso.refl _) (ρ_ _), finrank_unit_map_dual_simple S G]
  simp_rw [h]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact finrank_hom_iso (Iso.refl X)
    (((F.mapIso S.unitIso ≪≫ (Functor.Monoidal.εIso F).symm) ⊗ᵢ Iso.refl Y) ≪≫ λ_ Y)

include e in
/-- The second-factor free Hom has the corresponding actual Hom dimension. -/
lemma finrank_freeRightHom (U V : D) :
    Module.finrank ℂ (InternalModule.free A (pair (𝟙_ C) U) ⟶
      InternalModule.free A (pair (𝟙_ C) V)) = Module.finrank ℂ (U ⟶ V) := by
  rw [finrank_freePairHom _ _ e]
  have h (i : ι) : Module.finrank ℂ
      (𝟙_ C ⟶ F.obj (S.simpleObject i) ⊗ 𝟙_ C) =
        if i = S.unitLabel then 1 else 0 := by
    rw [finrank_hom_iso (Iso.refl _) (ρ_ _), finrank_unit_map_simple S F]
  simp_rw [h]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  let d : dual E (S.simpleObject S.unitLabel) ≅ 𝟙_ E :=
    (S.dualIso S.unitLabel).symm ≪≫ eqToIso (congrArg S.simpleObject S.dualLabel_unit) ≪≫ S.unitIso
  exact finrank_hom_iso (Iso.refl U)
    (((G.mapIso d ≪≫ (Functor.Monoidal.εIso G).symm) ⊗ᵢ Iso.refl V) ≪≫ λ_ V)

include e in
/-- The genuine mixed free Hom formula used to recognize the intersection
of the two free images. -/
lemma finrank_freeMixedHom (X : C) (V : D) :
    Module.finrank ℂ (InternalModule.free A (pair X (𝟙_ D)) ⟶
      InternalModule.free A (pair (𝟙_ C) V)) =
      ∑ i, Module.finrank ℂ (X ⟶ F.obj (S.simpleObject i)) *
        Module.finrank ℂ (𝟙_ D ⟶ G.obj (dual E (S.simpleObject i)) ⊗ V) := by
  rw [finrank_freePairHom _ _ e]
  apply Finset.sum_congr rfl
  intro i hi
  rw [finrank_hom_iso (Iso.refl X) (ρ_ _)]

end Paper18.Category.DiagonalCondensation
