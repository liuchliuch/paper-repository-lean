import Paper18.Category.GraphPicardMoritaProductAction

/-! # Central action commutes with genuine strong module functors

This comparison uses the given actual lineator of the module functor.
Its module naturality is derived from the two actual associativity laws
and naturality in the actual half-braiding. No ambient braiding, pivotal
structure, or comparison-coherence conclusion is assumed.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalLeftAction
universe v u vM uM vN uN
namespace Paper18.Category.GraphPicard.MoritaProduct
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {M : Type uM} [Category.{vM} M] [MonoidalLeftAction C M]
  {N : Type uN} [Category.{vN} N] [MonoidalLeftAction C N]
  (F : M ⥤ N) [F.LeftLinear C] (Z : Center C)

/-- The actual strong lineator, natural in the module object, compares
the two ways to apply a central action and a genuine module functor. -/
def centralActionNaturalityIso :
    F ⋙ ModuleAlphaInduction.centralFunctor (M := N) Z ≅
      ModuleAlphaInduction.centralFunctor (M := M) Z ⋙ F :=
  NatIso.ofComponents (Functor.LeftLinear.μₗIso F Z.1) (by
    intro m n f
    exact Functor.LaxLeftLinear.μₗ_naturality_right F Z.1 f)

/-- The genuine central comparison is a module natural isomorphism,
proved directly from actual strong-lineator coherence. -/
instance centralActionNaturality_moduleNatural :
    ModuleFunctor.IsModuleNatural C (centralActionNaturalityIso F Z).hom where
  lineator X m := by
    change
      (Functor.LaxLeftLinear.μₗ (ModuleAlphaInduction.centralFunctor (M := N) Z)
          X (F.obj m) ≫ Z.1 ⊴ₗ Functor.LaxLeftLinear.μₗ F X m) ≫
        Functor.LaxLeftLinear.μₗ F Z.1 (X ⊙ₗ m) =
      X ⊴ₗ Functor.LaxLeftLinear.μₗ F Z.1 m ≫
        Functor.LaxLeftLinear.μₗ F X (Z.1 ⊙ₗ m) ≫
          F.map (Functor.LaxLeftLinear.μₗ
            (ModuleAlphaInduction.centralFunctor (M := M) Z) X m)
    simp only [ModuleAlphaInduction.central_μ, ModuleAlphaInduction.centralLineator,
      Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, actionRight_map,
      F.map_comp, Category.assoc]
    apply (cancel_epi (αₗ X Z.1 (F.obj m)).hom).mp
    simp only [Iso.hom_inv_id_assoc]
    rw [← Functor.LaxLeftLinear.μₗ_associativity_assoc F X Z.1 m]
    simp only [← F.map_comp_assoc]
    rw [← Functor.LaxLeftLinear.μₗ_associativity F Z.1 X m]
    rw [Functor.LaxLeftLinear.μₗ_naturality_left_assoc F (Z.2.β X).inv m]
    simp only [Iso.hom_inv_id_assoc]

end Paper18.Category.GraphPicard.MoritaProduct
