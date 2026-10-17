import Paper18.Category.ModuleFunctorSemisimpleWattsResolution
import Paper18.Category.ModuleFunctorFiniteDensity

/-! # Actual Eilenberg--Watts extension of maps at the regular algebra -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u
namespace Paper18.Category.ModuleFunctor
open MonoidalLeftAction
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  {R : D} [MonObj R]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
variable (F G : Mod_ D R ⥤ Mod_ D R) [F.LeftLinear Dᴹᵒᵖ] [G.LeftLinear Dᴹᵒᵖ]

/-- An actual map at the regular algebra extends to the action on it by
actual inverse lineators, with no fullness hypothesis. -/
def wattsFreeTransformation (h : F.obj (Mod_.regular R) ⟶ G.obj (Mod_.regular R)) :
    actionRight Dᴹᵒᵖ (Mod_.regular R) ⋙ F ⟶ actionRight Dᴹᵒᵖ (Mod_.regular R) ⋙ G :=
  (actionLineatorIso F (Mod_.regular R)).inv ≫ actionTransformation h ≫
    (actionLineatorIso G (Mod_.regular R)).hom

instance wattsFreeTransformation_moduleNatural
    (h : F.obj (Mod_.regular R) ⟶ G.obj (Mod_.regular R)) :
    IsModuleNatural Dᴹᵒᵖ (wattsFreeTransformation F G h) := by
  dsimp only [wattsFreeTransformation]
  infer_instance

@[simp]
lemma wattsFreeTransformation_app (h : F.obj (Mod_.regular R) ⟶ G.obj (Mod_.regular R))
    (X : Dᴹᵒᵖ) :
    (wattsFreeTransformation F G h).app X =
      Functor.OplaxLeftLinear.δₗ F X (Mod_.regular R) ≫ (X ⊴ₗ h) ≫
        Functor.LaxLeftLinear.μₗ G X (Mod_.regular R) := rfl

variable (S : SeparableAlgebra R)

instance wattsLeftUnitor_moduleNatural (H : Mod_ D R ⥤ Mod_ D R) [H.LeftLinear Dᴹᵒᵖ] :
    IsModuleNatural Dᴹᵒᵖ (Functor.leftUnitor H).hom where
  lineator X M := by
    change (Functor.LaxLeftLinear.μₗ H X M ≫ H.map (𝟙 _)) ≫ 𝟙 _ =
      (X ⊴ₗ 𝟙 _) ≫ Functor.LaxLeftLinear.μₗ H X M
    simp

/-- The actual separable free resolution extends the action map to an
ordinary natural transformation on every actual module. -/
def wattsTransformation (h : F.obj (Mod_.regular R) ⟶ G.obj (Mod_.regular R)) : F ⟶ G :=
  (Functor.leftUnitor F).inv ≫ Functor.whiskerRight (wattsSection S) F ≫
    (Functor.associator wattsForget (actionRight Dᴹᵒᵖ (Mod_.regular R)) F).hom ≫
      Functor.whiskerLeft wattsForget (wattsFreeTransformation F G h) ≫
        (Functor.associator wattsForget (actionRight Dᴹᵒᵖ (Mod_.regular R)) G).inv ≫
          Functor.whiskerRight wattsCounit G ≫ (Functor.leftUnitor G).hom

instance wattsTransformation_moduleNatural
    (h : F.obj (Mod_.regular R) ⟶ G.obj (Mod_.regular R)) :
    IsModuleNatural Dᴹᵒᵖ (wattsTransformation F G S h) := by
  dsimp only [wattsTransformation]
  infer_instance

@[simp]
lemma wattsTransformation_app (h : F.obj (Mod_.regular R) ⟶ G.obj (Mod_.regular R))
    (X : Mod_ D R) :
    (wattsTransformation F G S h).app X =
      F.map ((wattsSection S).app X) ≫
        (wattsFreeTransformation F G h).app (mop X.X) ≫ G.map (wattsCounit.app X) := by
  simp only [wattsTransformation, NatTrans.comp_app, Functor.leftUnitor_hom_app,
    Functor.leftUnitor_inv_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, id_comp]
  erw [id_comp, comp_id]
  rfl

include S in
/-- Module transformations are detected at the regular algebra, since
every actual module is an actual retract of a free action object. -/
lemma wattsTransformation_ext (τ σ : F ⟶ G)
    [IsModuleNatural Dᴹᵒᵖ τ] [IsModuleNatural Dᴹᵒᵖ σ]
    (h : τ.app (Mod_.regular R) = σ.app (Mod_.regular R)) : τ = σ := by
  apply NatTrans.ext
  funext X
  let r : Retract X ((actionRight Dᴹᵒᵖ (Mod_.regular R)).obj (mop X.X)) :=
    { i := (wattsSection S).app X
      r := wattsCounit.app X
      retract := congrArg (fun a => a.app X) (wattsSection_counit S) }
  exact natTrans_app_eq_of_retract τ σ r
    (moduleNatTrans_app_action_eq τ σ (mop X.X) (Mod_.regular R) h)

end Paper18.Category.ModuleFunctor
