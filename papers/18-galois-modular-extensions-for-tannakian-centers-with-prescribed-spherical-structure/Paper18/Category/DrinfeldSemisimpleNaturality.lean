import Paper18.Category.DrinfeldSemisimpleSummation

/-! # Naturality of the actual weighted section and averaging expression -/
noncomputable section
universe v u w
namespace Paper18.Category.Drinfeld
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

@[reassoc]
lemma inductionSectionComponent_naturality {Z W : Center C} (f : Z ⟶ W) (T : C) :
    f.f ≫ inductionSectionComponent W T =
      inductionSectionComponent Z T ≫ ((T ◁ f.f) ▷ dual C T) := by
  calc
    _ = 𝟙 Z.1 ⊗≫ ((f.f ▷ (𝟙_ C)) ≫ W.1 ◁ η_ T (dual C T)) ⊗≫
        (W.2.β T).hom ▷ dual C T ⊗≫ 𝟙 ((T ⊗ W.1) ⊗ dual C T) := by
      rw [inductionSectionComponent_transpose]
      monoidal
    _ = 𝟙 Z.1 ⊗≫ Z.1 ◁ η_ T (dual C T) ⊗≫
        ((f.f ▷ T) ≫ (W.2.β T).hom) ▷ dual C T ⊗≫
          𝟙 ((T ⊗ W.1) ⊗ dual C T) := by
      rw [← whisker_exchange]
      monoidal
    _ = _ := by
      rw [f.comm, inductionSectionComponent_transpose]
      monoidal

section Coend
variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι) (J : PivotalStructure C)

@[reassoc]
lemma inductionWeightedSection_naturality {Z W : Center C} (f : Z ⟶ W) :
    f.f ≫ inductionWeightedSection S J W =
      inductionWeightedSection S J Z ≫ inductionUnderlyingMap S f.f := by
  simp only [inductionWeightedSection, Preadditive.comp_sum, Linear.comp_smul,
    Preadditive.sum_comp, Linear.smul_comp, assoc, inductionSectionComponent_naturality_assoc,
    inductionUnderlyingMap_ι]

@[reassoc]
lemma inductionNormalizedSection_naturality {Z W : Center C} (f : Z ⟶ W) :
    f.f ≫ inductionNormalizedSection S J W =
      inductionNormalizedSection S J Z ≫ inductionUnderlyingMap S f.f := by
  simp only [inductionNormalizedSection, Linear.comp_smul, Linear.smul_comp,
    inductionWeightedSection_naturality]

/-- The actual underlying averaging expression. Its centrality is to be
proved by the separate weighted sliding calculation. -/
def centerAverageUnderlying {Z W : Center C} (f : Z.1 ⟶ W.1) : Z.1 ⟶ W.1 :=
  inductionNormalizedSection S J Z ≫ inductionUnderlyingMap S f ≫ (inductionCounit S J W).f

lemma centerAverageUnderlying_add {Z W : Center C} (f g : Z.1 ⟶ W.1) :
    centerAverageUnderlying S J (f + g) =
      centerAverageUnderlying S J f + centerAverageUnderlying S J g := by
  simp only [centerAverageUnderlying, inductionUnderlyingMap_add,
    Preadditive.add_comp, Preadditive.comp_add]

lemma centerAverageUnderlying_smul {Z W : Center C} (c : ℂ) (f : Z.1 ⟶ W.1) :
    centerAverageUnderlying S J (c • f) = c • centerAverageUnderlying S J f := by
  simp only [centerAverageUnderlying, inductionUnderlyingMap_smul, Linear.smul_comp, Linear.comp_smul]

/-- The averaging expression fixes every actual central morphism. -/
lemma centerAverageUnderlying_central_map {Z W : Center C} (f : Z ⟶ W) :
    centerAverageUnderlying S J f.f = f.f := by
  have hn := (inductionAdjunction S J).counit.naturality f
  have h : inductionUnderlyingMap S f.f ≫ (inductionCounit S J W).f =
      (inductionCounit S J Z).f ≫ f.f := congrArg Center.Hom.f hn
  rw [centerAverageUnderlying, h, ← assoc, inductionNormalizedSection_counit, id_comp]

end Coend
end Paper18.Category.Drinfeld
