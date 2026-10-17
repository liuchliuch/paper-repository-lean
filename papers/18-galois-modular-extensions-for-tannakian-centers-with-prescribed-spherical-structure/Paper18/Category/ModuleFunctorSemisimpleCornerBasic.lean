import Paper18.Category.ModuleFunctorAdjoint
import Paper18.Category.ModuleFunctorFiniteActionIso

/-! # Actual module naturality reflected by a full faithful target -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped MonoidalLeftAction
universe v u vM uM vN uN vP uP
namespace Paper18.Category.ModuleFunctor
open MonoidalLeftAction
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {M : Type uM} [Category.{vM} M] [MonoidalLeftAction C M]
  {N : Type uN} [Category.{vN} N] [MonoidalLeftAction C N]
  {P : Type uP} [Category.{vP} P] [MonoidalLeftAction C P]
  (I : N ⥤ P) [I.LeftLinear C] [I.Full] [I.Faithful]
  (F G : M ⥤ N) [F.LeftLinear C] [G.LeftLinear C]

/-- The actual ordinary full faithful preimage of a transformation. -/
def cornerPostPreimage (τ : F ⋙ I ⟶ G ⋙ I) : F ⟶ G where
  app m := I.preimage (τ.app m)
  naturality {m n} f := by
    apply I.map_injective
    simp only [I.map_comp, I.map_preimage]
    exact τ.naturality f

@[simp] lemma cornerPostPreimage_map (τ : F ⋙ I ⟶ G ⋙ I) (m : M) :
    I.map ((cornerPostPreimage I F G τ).app m) = τ.app m := I.map_preimage _

/-- Actual strong lineators and faithful cancellation force module
naturality of the genuine ordinary preimage. -/
instance cornerPostPreimage_moduleNatural (τ : F ⋙ I ⟶ G ⋙ I)
    [IsModuleNatural C τ] : IsModuleNatural C (cornerPostPreimage I F G τ) where
  lineator X m := by
    apply I.map_injective
    apply (cancel_epi (Functor.LaxLeftLinear.μₗ I X (F.obj m))).mp
    rw [I.map_comp, I.map_comp, ← assoc,
      ← Functor.LaxLeftLinear.μₗ_naturality_right_assoc]
    simp only [assoc, cornerPostPreimage_map]
    simpa only [ModuleAlphaInduction.comp_μ, assoc] using
      (inferInstance : IsModuleNatural C τ).lineator X m

instance cornerLeftUnitor_moduleNatural (H : M ⥤ N) [H.LeftLinear C] :
    IsModuleNatural C (Functor.leftUnitor H).hom where
  lineator X m := by
    change (Functor.LaxLeftLinear.μₗ H X m ≫ H.map (𝟙 _)) ≫ 𝟙 _ =
      (X ⊴ₗ 𝟙 _) ≫ Functor.LaxLeftLinear.μₗ H X m
    simp

end Paper18.Category.ModuleFunctor
