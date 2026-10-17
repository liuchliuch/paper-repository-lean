import Paper18.Category.GraphPicardMoritaProductActionNaturality

/-! # Actual composition and natural isomorphisms for module transport -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalLeftAction
open scoped MonObj
universe v u vM uM vN uN vP uP
namespace Paper18.Category.GraphPicard.MoritaProduct
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {M : Type uM} [Category.{vM} M] [MonoidalLeftAction C M]
  {N : Type uN} [Category.{vN} N] [MonoidalLeftAction C N]
  {P : Type uP} [Category.{vP} P] [MonoidalLeftAction C P]
  {A : C} [MonObj A]
  (F : M ⥤ N) [F.LeftLinear C] (G : N ⥤ P) [G.LeftLinear C]

/-- Actual transport of algebra modules respects actual composition. -/
def transportCompComponent (X : Mod_ M A) :
    (ModuleFunctor.mapActionModules F ⋙ ModuleFunctor.mapActionModules G).obj X ≅
      (ModuleFunctor.mapActionModules (F ⋙ G)).obj X where
  hom := Mod_.Hom.mk' (𝟙 _) (by
    change (Functor.LaxLeftLinear.μₗ G A (F.obj X.X) ≫
      G.map (Functor.LaxLeftLinear.μₗ F A X.X ≫ F.map γ[A,X.X])) ≫ 𝟙 _ =
      (A ⊴ₗ 𝟙 _) ≫ ((Functor.LaxLeftLinear.μₗ G A (F.obj X.X) ≫
        G.map (Functor.LaxLeftLinear.μₗ F A X.X)) ≫ G.map (F.map γ[A,X.X]))
    simp only [Category.comp_id, actionHomRight_id, Category.id_comp,
      G.map_comp, Category.assoc])
  inv := Mod_.Hom.mk' (𝟙 _) (by
    change ((Functor.LaxLeftLinear.μₗ G A (F.obj X.X) ≫
      G.map (Functor.LaxLeftLinear.μₗ F A X.X)) ≫ G.map (F.map γ[A,X.X])) ≫ 𝟙 _ =
      (A ⊴ₗ 𝟙 _) ≫ (Functor.LaxLeftLinear.μₗ G A (F.obj X.X) ≫
        G.map (Functor.LaxLeftLinear.μₗ F A X.X ≫ F.map γ[A,X.X]))
    simp only [Category.comp_id, actionHomRight_id, Category.id_comp,
      G.map_comp, Category.assoc])
  hom_inv_id := by apply Mod_.Hom.ext; exact Category.id_comp _
  inv_hom_id := by apply Mod_.Hom.ext; exact Category.id_comp _

def transportCompIso :
    ModuleFunctor.mapActionModules (A := A) F ⋙ ModuleFunctor.mapActionModules G ≅
      ModuleFunctor.mapActionModules (F ⋙ G) :=
  NatIso.ofComponents (transportCompComponent F G) (by
    intro X Y f
    apply Mod_.Hom.ext
    exact (Category.comp_id (G.map (F.map f.hom))).trans (Category.id_comp _).symm)

section NaturalIso
variable {F} {G : M ⥤ N} [G.LeftLinear C] (e : F ≅ G)
  [ModuleFunctor.IsModuleNatural C e.hom]

/-- An actual module natural isomorphism transports to an actual
isomorphism of functors between the actual algebra-module categories. -/
def transportNatIso : ModuleFunctor.mapActionModules (A := A) F ≅
    ModuleFunctor.mapActionModules G where
  hom := ModuleFunctor.mapActionModulesTransformation e.hom
  inv := ModuleFunctor.mapActionModulesTransformation e.inv
  hom_inv_id := by
    apply NatTrans.ext
    funext X
    apply Mod_.Hom.ext
    exact e.hom_inv_id_app X.X
  inv_hom_id := by
    apply NatTrans.ext
    funext X
    apply Mod_.Hom.ext
    exact e.inv_hom_id_app X.X

end NaturalIso

/-- The actual central action and an actual module functor commute also
after transporting genuine algebra-module objects. -/
def transportedCentralActionIso (Z : Center C) :
    ModuleFunctor.mapActionModules (A := A) F ⋙
        ModuleFunctor.mapActionModules (ModuleAlphaInduction.centralFunctor (M := N) Z) ≅
      ModuleFunctor.mapActionModules (ModuleAlphaInduction.centralFunctor (M := M) Z) ⋙
        ModuleFunctor.mapActionModules F :=
  transportCompIso F (ModuleAlphaInduction.centralFunctor (M := N) Z) ≪≫
    transportNatIso (centralActionNaturalityIso F Z) ≪≫
      (transportCompIso (ModuleAlphaInduction.centralFunctor (M := M) Z) F).symm

@[simp] theorem transportedCentralActionIso_hom (Z : Center C) (X : Mod_ M A) :
    ((transportedCentralActionIso (A := A) F Z).hom.app X).hom =
      Functor.LaxLeftLinear.μₗ F Z.1 X.X := by
  change 𝟙 _ ≫ Functor.LaxLeftLinear.μₗ F Z.1 X.X ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]

end Paper18.Category.GraphPicard.MoritaProduct
