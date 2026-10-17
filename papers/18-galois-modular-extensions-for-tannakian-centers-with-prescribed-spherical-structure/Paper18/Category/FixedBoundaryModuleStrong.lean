import Paper18.Category.FixedBoundaryModuleRegular

/-!
# Strong native module functors from invertible actual lineators

All oplax module-functor coherence follows from the actual lax coherence
when the given lineators are isomorphisms.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped MonoidalLeftAction
universe v u v' u' v'' u''
namespace Paper18.Category.ModuleFunctor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {M : Type u'} [Category.{v'} M] [MonoidalLeftAction C M]
  {N : Type u''} [Category.{v''} N] [MonoidalLeftAction C N]
  (F : M ⥤ N) [F.LaxLeftLinear C]
  [∀ (X : C) (Y : M), IsIso (Functor.LaxLeftLinear.μₗ F X Y)]

/-- The genuine inverse-lineator construction for native module functors. -/
def leftLinearOfLax : F.LeftLinear C where
  toLaxLeftLinear := inferInstance
  δₗ X Y := inv (Functor.LaxLeftLinear.μₗ F X Y)
  δₗ_naturality_left {X X'} f Y := by
    apply (cancel_epi (Functor.LaxLeftLinear.μₗ F X Y)).mp
    rw [← Category.assoc, ← Functor.LaxLeftLinear.μₗ_naturality_left]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc, IsIso.hom_inv_id,
      IsIso.inv_hom_id_assoc, IsIso.inv_hom_id, Category.id_comp, Category.comp_id]
  δₗ_naturality_right X {Y Y'} f := by
    apply (cancel_epi (Functor.LaxLeftLinear.μₗ F X Y)).mp
    rw [← Category.assoc, ← Functor.LaxLeftLinear.μₗ_naturality_right]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc, IsIso.hom_inv_id,
      IsIso.inv_hom_id_assoc, IsIso.inv_hom_id, Category.id_comp, Category.comp_id]
  δₗ_associativity X Y Z := by
    apply (cancel_epi (Functor.LaxLeftLinear.μₗ F (X ⊗ Y) Z)).mp
    simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
    rw [Functor.LaxLeftLinear.μₗ_associativity]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    rw [← MonoidalLeftAction.actionHomRight_comp]
    simp
  δₗ_unitality_inv Y := by
    have he : (λₗ[C] (F.obj Y)) =
        asIso (Functor.LaxLeftLinear.μₗ F (𝟙_ C) Y) ≪≫ F.mapIso (λₗ[C] Y) :=
      Iso.ext (Functor.LaxLeftLinear.μₗ_unitality F (C := C) Y)
    exact congrArg (fun e => e.inv) he
  μₗ_comp_δₗ X Y := IsIso.hom_inv_id _
  δₗ_comp_μₗ X Y := IsIso.inv_hom_id _

section Oplax
variable {C' : Type u} [Category.{v} C'] [MonoidalCategory C']
  {M' : Type u'} [Category.{v'} M'] [MonoidalLeftAction C' M']
  {N' : Type u''} [Category.{v''} N'] [MonoidalLeftAction C' N']
  (G : M' ⥤ N') [G.OplaxLeftLinear C']
  [∀ (X : C') (Y : M'), IsIso (Functor.OplaxLeftLinear.δₗ G X Y)]

/-- The dual construction starts with actual invertible oplax lineators. -/
def leftLinearOfOplax : G.LeftLinear C' where
  toOplaxLeftLinear := inferInstance
  μₗ X Y := inv (Functor.OplaxLeftLinear.δₗ G X Y)
  μₗ_naturality_left {X X'} f Y := by
    apply (cancel_mono (Functor.OplaxLeftLinear.δₗ G X' Y)).mp
    simp only [Category.assoc]
    rw [Functor.OplaxLeftLinear.δₗ_naturality_left]
    simp only [IsIso.inv_hom_id_assoc, IsIso.inv_hom_id, Category.comp_id]
  μₗ_naturality_right X {Y Y'} f := by
    apply (cancel_mono (Functor.OplaxLeftLinear.δₗ G X Y')).mp
    simp only [Category.assoc]
    rw [Functor.OplaxLeftLinear.δₗ_naturality_right]
    simp only [IsIso.inv_hom_id_assoc, IsIso.inv_hom_id, Category.comp_id]
  μₗ_associativity X Y Z := by
    apply (cancel_mono (Functor.OplaxLeftLinear.δₗ G X (Y ⊙ₗ Z))).mp
    apply (cancel_mono (X ⊴ₗ Functor.OplaxLeftLinear.δₗ G Y Z)).mp
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    rw [← Functor.OplaxLeftLinear.δₗ_associativity]
    simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
    simp only [Category.assoc]
    rw [← MonoidalLeftAction.actionHomRight_comp]
    simp only [IsIso.inv_hom_id, MonoidalLeftAction.actionHomRight_id, Category.comp_id]
  μₗ_unitality Y := by
    have he : (λₗ[C'] (G.obj Y)).symm =
        (G.mapIso (λₗ[C'] Y)).symm ≪≫
          asIso (Functor.OplaxLeftLinear.δₗ G (𝟙_ C') Y) :=
      Iso.ext (Functor.OplaxLeftLinear.δₗ_unitality_inv G (C := C') Y)
    exact congrArg (fun e => e.inv) he
  μₗ_comp_δₗ X Y := IsIso.inv_hom_id _
  δₗ_comp_μₗ X Y := IsIso.hom_inv_id _

end Oplax
end Paper18.Category.ModuleFunctor
