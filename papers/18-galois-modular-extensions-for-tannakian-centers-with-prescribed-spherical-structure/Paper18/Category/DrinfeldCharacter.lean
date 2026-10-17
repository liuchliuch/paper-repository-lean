import Paper18.Category.DrinfeldExact
import Paper18.Category.TensorCharacters

/-! # A tensor automorphism as an actual central structure on the unit -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u
namespace Paper18.Category.Drinfeld
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  (χ : 𝟭 C ≅ 𝟭 C) [NatTrans.IsMonoidal χ.hom]

def characterHalfBraiding : HalfBraiding (𝟙_ C) where
  β X := (λ_ X) ≪≫ χ.app X ≪≫ (ρ_ X).symm
  monoidal X Y := by
    have ht := NatTrans.IsMonoidal.tensor (τ := χ.hom) X Y
    change 𝟙 (X ⊗ Y) ≫ χ.hom.app (X ⊗ Y) =
      (χ.hom.app X ⊗ₘ χ.hom.app Y) ≫ 𝟙 (X ⊗ Y) at ht
    simp only [Category.id_comp, Category.comp_id] at ht
    simp only [Iso.trans_hom, Iso.symm_hom, NatIso.app_hom]
    rw [ht]
    simp only [MonoidalCategory.tensorHom_def]
    monoidal
  naturality {X Y} f := by
    have hn := χ.hom.naturality f
    change f ≫ χ.hom.app Y = χ.hom.app X ≫ f at hn
    simp only [Iso.trans_hom, Iso.symm_hom, NatIso.app_hom, Category.assoc]
    rw [leftUnitor_naturality_assoc,
      ← Category.assoc f (χ.hom.app Y) (ρ_ Y).inv, hn, Category.assoc]
    exact congrArg (fun k => (λ_ X).hom ≫ χ.hom.app X ≫ k)
      (rightUnitor_inv_naturality f)

def characterObject : Center C := ⟨𝟙_ C, characterHalfBraiding χ⟩

@[simp] lemma characterObject_underlying : (characterObject χ).1 = 𝟙_ C := rfl

lemma characterObject_halfBraiding (X : C) :
    (((characterObject χ).2).β X).hom =
      (λ_ X).hom ≫ χ.hom.app X ≫ (ρ_ X).inv := rfl

@[simp] lemma characterObject_recover (X : C) :
    (λ_ X).inv ≫ (((characterObject χ).2).β X).hom ≫ (ρ_ X).hom = χ.hom.app X := by
  simp [characterObject_halfBraiding]

end Paper18.Category.Drinfeld
