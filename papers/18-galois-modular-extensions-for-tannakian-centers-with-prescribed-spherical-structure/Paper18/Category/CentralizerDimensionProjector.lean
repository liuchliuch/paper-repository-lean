import Paper18.Category.ENOPseudounitaryScalarLift
import Paper18.Category.CentralizerFusion

/-!
# Actual semisimple support projectors for categorical centralizers

The natural idempotent is constructed from actual biproduct decompositions.
Its fixed objects are exactly those in the given summand-closed full
subcategory; centralization itself is still the equality of actual
monodromy morphisms.
-/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category.FiniteSemisimpleSkeleton
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- The actual natural projection selecting the simple constituents with
property `P`. -/
def supportProjector (P : ObjectProperty C) : 𝟭 C ⟶ 𝟭 C where
  app := S.scalarAction (fun i => if P (S.simpleObject i) then 1 else 0)
  naturality := fun {X Y} f => S.scalarAction_naturality _ f

@[simp] lemma supportProjector_simple (P : ObjectProperty C) (i : ι) :
    (S.supportProjector P).app (S.simpleObject i) =
      if P (S.simpleObject i) then 𝟙 _ else 0 := by
  simp only [supportProjector, S.scalarAction_simple]
  split_ifs <;> simp

@[reassoc] lemma supportProjector_naturality (P : ObjectProperty C) {X Y : C} (f : X ⟶ Y) :
    f ≫ (S.supportProjector P).app Y = (S.supportProjector P).app X ≫ f :=
  (S.supportProjector P).naturality f

/-- This is a genuine natural idempotent in the actual category. -/
lemma supportProjector_idempotent (P : ObjectProperty C) :
    S.supportProjector P ≫ S.supportProjector P = S.supportProjector P := by
  ext X
  apply S.hom_ext_simples
  intro i f
  have hn := (S.supportProjector P).naturality f
  change f ≫ (S.supportProjector P).app X =
    (S.supportProjector P).app (S.simpleObject i) ≫ f at hn
  change f ≫ ((S.supportProjector P).app X ≫ (S.supportProjector P).app X) = _
  rw [← assoc, hn, assoc, hn, ← assoc]
  rw [S.supportProjector_simple]
  split_ifs <;> simp

include S in
/-- A natural endomorphism on a semisimple category is determined by its
components on a complete actual simple family. -/
lemma natEnd_ext_simples (a b : 𝟭 C ⟶ 𝟭 C)
    (h : ∀ i, a.app (S.simpleObject i) = b.app (S.simpleObject i)) : a = b := by
  ext X
  apply S.hom_ext_simples
  intro i f
  exact (a.naturality f).trans ((congrArg (fun q => q ≫ f) (h i)).trans
    (b.naturality f).symm)

lemma supportProjector_add_not (P : ObjectProperty C) :
    S.supportProjector P + S.supportProjector (fun X => ¬ P X) = 𝟙 (𝟭 C) := by
  apply S.natEnd_ext_simples
  intro i
  change (S.supportProjector P).app _ + (S.supportProjector (fun X => ¬ P X)).app _ = 𝟙 _
  rw [S.supportProjector_simple, S.supportProjector_simple]
  split_ifs <;> simp_all

lemma supportProjector_inter (P Q : ObjectProperty C) :
    S.supportProjector (fun X => P X ∧ Q X) = S.supportProjector P ≫ S.supportProjector Q := by
  apply S.natEnd_ext_simples
  intro i
  change _ = (S.supportProjector P).app _ ≫ (S.supportProjector Q).app _
  simp only [S.supportProjector_simple]
  split_ifs <;> simp_all

/-- Membership in a summand-closed additive full subcategory can be checked
on the labels in any actual simple decomposition. -/
lemma property_iff_labels (P : ObjectProperty C) [IsAdditiveFullProperty P] (X : C) :
    P X ↔ ∀ a : Fin (S.length X), P (S.simpleObject (S.label X a)) := by
  constructor
  · intro h a
    exact S.property_label P ⟨X, h⟩ a
  · intro h
    exact IsAdditiveFullProperty.of_iso P (S.decomposition X)
      (IsAdditiveFullProperty.biproduct (fun a => S.simpleObject (S.label X a)) h)

/-- The fixed-object condition for the genuine natural projector is exactly
membership in the actual full subcategory. -/
lemma supportProjector_eq_id_iff (P : ObjectProperty C) [IsAdditiveFullProperty P] (X : C) :
    (S.supportProjector P).app X = 𝟙 X ↔ P X := by
  constructor
  · intro h
    apply (S.property_iff_labels P X).mpr
    intro a
    have hn := S.scalarInclusion_action
      (fun i => if P (S.simpleObject i) then (1 : ℂ) else 0) X a
    change S.scalarInclusion X a ≫ (S.supportProjector P).app X = _ at hn
    rw [h, comp_id] at hn
    by_contra hp
    simp only [if_neg hp, zero_smul] at hn
    have hr : S.scalarInclusion X a ≫ S.scalarProjection X a = 𝟙 _ := by
      simp [scalarInclusion, scalarProjection, assoc]
    rw [hn, zero_comp] at hr
    exact CategoryTheory.id_nonzero _ hr.symm
  · intro h
    apply S.hom_ext_simples
    intro i f
    have hn := (S.supportProjector P).naturality f
    change f ≫ (S.supportProjector P).app X =
      (S.supportProjector P).app (S.simpleObject i) ≫ f at hn
    rw [hn, S.supportProjector_simple]
    by_cases hp : P (S.simpleObject i)
    · simp [hp]
    · have hf : f = 0 := by
        by_contra hf
        have hm : 0 < S.multiplicity X i :=
          Module.finrank_pos_iff_exists_ne_zero.mpr ⟨f, hf⟩
        exact hp (IsAdditiveFullProperty.of_retract (S.retractOfMultiplicityPos X i hm) h)
      simp [hf]

variable [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C]

/-- The actual categorical centralizer projector. -/
abbrev centralizerProjector (T : Set C) : 𝟭 C ⟶ 𝟭 C :=
  S.supportProjector (centralizerProperty T)

lemma centralizerProjector_eq_id_iff (T : Set C) (X : C) :
    (S.centralizerProjector T).app X = 𝟙 X ↔ X ∈ centralizer T :=
  S.supportProjector_eq_id_iff (centralizerProperty T) X

end Paper18.Category.FiniteSemisimpleSkeleton
