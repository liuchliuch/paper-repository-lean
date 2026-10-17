import Paper18.Category.BalancedModuleCategoryMonadDescent

/-! # Transport an actual split presentation through actual isomorphisms -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe v u
namespace Paper18.Category.BalancedModuleCategory
variable {E : Type u} [Category.{v} E]

/-- Every equation of the transported split coequalizer is derived from
its original splitting and the two actual commuting squares. -/
def transportSplitCoequalizer {X Y X' Y' Z : E} {f g : X ⟶ Y} {f' g' : X' ⟶ Y'}
    {q : Y' ⟶ Z} (h : IsSplitCoequalizer f' g' q) (e : X ≅ X') (d : Y ≅ Y')
    (hf : f ≫ d.hom = e.hom ≫ f') (hg : g ≫ d.hom = e.hom ≫ g') :
    IsSplitCoequalizer f g (d.hom ≫ q) where
  rightSection := h.rightSection ≫ d.inv
  leftSection := d.hom ≫ h.leftSection ≫ e.inv
  condition := by
    rw [← Category.assoc, hf, Category.assoc, h.condition, ← Category.assoc, ← hg, Category.assoc]
  rightSection_π := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc, h.rightSection_π]
  leftSection_bottom := by
    apply (cancel_mono d.hom).mp
    simp only [Category.assoc, hg, Iso.inv_hom_id_assoc,
      h.leftSection_bottom, Category.id_comp, Category.comp_id]
  leftSection_top := by
    apply (cancel_mono d.hom).mp
    simp only [Category.assoc, hf, Iso.inv_hom_id_assoc, h.leftSection_top, Iso.inv_hom_id, Category.comp_id]

end Paper18.Category.BalancedModuleCategory
