import Paper18.Category.ModuleFunctorFiniteRegular
import Paper18.Category.ModuleAlphaInductionComposition

/-! # The actual module-natural action lineator isomorphism

For a genuine strong module functor F, its actual strong lineators
identify acting on F(n) with applying F after acting on n. The module
naturality is the actual associativity coherence of F.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped MonoidalLeftAction
universe v u vM uM vN uN
namespace Paper18.Category.ModuleFunctor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {M : Type uM} [Category.{vM} M] [MonoidalLeftAction C M]
  {N : Type uN} [Category.{vN} N] [MonoidalLeftAction C N]
  (F : M ⥤ N) [F.LeftLinear C] (n : M)

/-- The genuine action lineators, regarded as an ordinary natural
isomorphism of actual functors out of the regular module. -/
def actionLineatorIso :
    MonoidalLeftAction.actionRight C (F.obj n) ≅
      MonoidalLeftAction.actionRight C n ⋙ F :=
  NatIso.ofComponents (fun X => Functor.LeftLinear.μₗIso F X n) (fun {X Y} f => by
    exact Functor.LaxLeftLinear.μₗ_naturality_left F f n)

@[simp] theorem actionLineatorIso_hom (X : C) :
    (actionLineatorIso (C := C) F n).hom.app X = Functor.LaxLeftLinear.μₗ F X n := rfl

/-- The action comparison is a genuine module natural isomorphism.
Its coherence is proved from the given genuine module coherence. -/
instance actionLineatorIso_moduleNatural :
    IsModuleNatural C (actionLineatorIso (C := C) F n).hom where
  lineator X Y := by
    change (αₗ X Y (F.obj n)).inv ≫ Functor.LaxLeftLinear.μₗ F (X ⊗ Y) n =
      X ⊴ₗ Functor.LaxLeftLinear.μₗ F Y n ≫
        Functor.LaxLeftLinear.μₗ F X (Y ⊙ₗ n) ≫ F.map (αₗ X Y n).inv
    apply (cancel_mono (F.map (αₗ X Y n).hom)).mp
    simp only [Category.assoc, ← F.map_comp, Iso.inv_hom_id, F.map_id, Category.comp_id]
    rw [Functor.LaxLeftLinear.μₗ_associativity]
    simp

section Associator
variable {P : Type*} [Category P] [MonoidalLeftAction C P]
  {Q : Type*} [Category Q] [MonoidalLeftAction C Q]
  (G : N ⥤ P) [G.LeftLinear C] (H : P ⥤ Q) [H.LeftLinear C]

/-- Association of actual native strong module functors is module natural
also when the source and the intermediate module categories differ. -/
instance compositionAssociator_moduleNatural :
    IsModuleNatural C (Functor.associator F G H).hom where
  lineator X m := by
    change Functor.LaxLeftLinear.μₗ ((F ⋙ G) ⋙ H) X m ≫ 𝟙 _ =
      X ⊴ₗ 𝟙 _ ≫ Functor.LaxLeftLinear.μₗ (F ⋙ (G ⋙ H)) X m
    simp only [ModuleAlphaInduction.comp_μ, Functor.comp_obj, Functor.comp_map,
      Functor.map_comp, MonoidalLeftAction.actionHomRight_id, Category.id_comp,
      Category.comp_id, Category.assoc]
end Associator

end Paper18.Category.ModuleFunctor
