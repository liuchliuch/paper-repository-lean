import Paper18.Category.RelativeCenterBasic

/-! # The unit half-braiding is forced by actual relative coherence -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {P : ObjectProperty C} [P.IsMonoidal]

lemma RelativeHalfBraiding.unit {X : C} (b : RelativeHalfBraiding P X) :
    (b.β (𝟙_ C) (ObjectProperty.prop_unit P)).hom = (ρ_ X).hom ≫ (λ_ X).inv := by
  let h1 := ObjectProperty.prop_unit P
  let t : X ≅ X := (ρ_ X).symm ≪≫ b.β (𝟙_ C) h1 ≪≫ λ_ X
  have ht : t.hom ≫ t.hom = t.hom := by
    change ((ρ_ X).inv ≫ (b.β (𝟙_ C) h1).hom ≫ (λ_ X).hom) ≫
      ((ρ_ X).inv ≫ (b.β (𝟙_ C) h1).hom ≫ (λ_ X).hom) = _
    calc
      _ = (ρ_ X).inv ≫ X ◁ (λ_ (𝟙_ C)).inv ≫
          (b.β ((𝟙_ C) ⊗ (𝟙_ C)) (ObjectProperty.prop_tensor h1 h1)).hom ≫
            (λ_ (𝟙_ C)).hom ▷ X ≫ (λ_ X).hom := by
        rw [b.monoidal _ _ h1 h1]
        monoidal
      _ = _ := by
        rw [← reassoc_of% b.naturality (ObjectProperty.prop_tensor h1 h1) h1 (λ_ (𝟙_ C)).hom]
        simp only [← whiskerLeft_comp_assoc, Iso.inv_hom_id, whiskerLeft_id, id_comp]
        rfl
  have hi : t.hom = 𝟙 X := (cancel_epi t.hom).mp (by simpa only [comp_id] using ht)
  have hh := congrArg (fun f => (ρ_ X).hom ≫ f ≫ (λ_ X).inv) hi
  simpa only [t, Iso.trans_hom, Iso.symm_hom, assoc, Iso.hom_inv_id_assoc,
    Iso.hom_inv_id, comp_id, id_comp] using hh

end Paper18.Category
