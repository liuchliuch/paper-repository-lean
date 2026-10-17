import Paper18.Category.DrinfeldCoendModulesInverseCrossing

/-! # Converting the recovered holonomy tensor word into a crossing hexagon -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory
universe v u
namespace Paper18.Category.DrinfeldCoendModules
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]

/-- The ambient braid hexagon cancels the normalization crossings in
the actual annular tensor word. No relation on the two endomorphisms is assumed. -/
lemma inverseCrossing_tensor_word (M U V : D) (hU : U ⊗ M ⟶ U ⊗ M)
    (hV : V ⊗ M ⟶ V ⊗ M) :
    ((α_ U V M).hom ≫ U ◁ hV ≫ U ◁ (β_ V M).hom ≫
      (α_ U M V).inv ≫ hU ▷ V ≫ (α_ U M V).hom ≫
        U ◁ (β_ V M).inv ≫ (α_ U V M).inv) ≫ (β_ (U ⊗ V) M).hom =
      (α_ U V M).hom ≫ U ◁ (hV ≫ (β_ V M).hom) ≫
        (α_ U M V).inv ≫ (hU ≫ (β_ U M).hom) ▷ V ≫ (α_ M U V).hom := by
  rw [braiding_tensor_left_hom]
  simp only [assoc, Iso.inv_hom_id_assoc, whiskerLeft_comp, comp_whiskerRight]
  have hc : U ◁ (β_ V M).inv ≫ U ◁ (β_ V M).hom = 𝟙 _ := by
    rw [← whiskerLeft_comp, Iso.inv_hom_id, whiskerLeft_id]
  simp only [reassoc_of% hc, Iso.hom_inv_id_assoc]

end Paper18.Category.DrinfeldCoendModules
