import Paper18.Category.BimoduleRelativeTensorWattsLinear

/-! # Actual mixed-algebra Eilenberg--Watts evaluation and extension -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u
namespace Paper18.Category.BimoduleRelativeTensor.MixedWatts
open ModuleFunctor MonoidalLeftAction
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  {R S : D} [MonObj R] [MonObj S]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

/-- Actual evaluation at the source regular module, with its genuine
right source-algebra action transported by the strong lineator. -/
def evaluation : Bundled Dᴹᵒᵖ (Mod_ D S) (Mod_ D R) ⥤ Native R S where
  obj F := mapActionModule F.toFunctor (wattsRegular (R := S))
  map τ := (mapActionModulesTransformation τ.val).app (wattsRegular (R := S))
  map_id F := by apply Mod_.Hom.ext; rfl
  map_comp τ σ := by apply Mod_.Hom.ext; rfl

instance evaluation_additive : (evaluation (R := R) (S := S)).Additive where
  map_add := by intros; apply Mod_.Hom.ext; rfl

instance evaluation_linear : (evaluation (R := R) (S := S)).Linear ℂ where
  map_smul _ _ := by apply Mod_.Hom.ext; rfl

variable (F G : Mod_ D S ⥤ Mod_ D R) [F.LeftLinear Dᴹᵒᵖ] [G.LeftLinear Dᴹᵒᵖ]

/-- The actual free-action extension uses inverse strong lineators. -/
def freeTransformation (h : F.obj (Mod_.regular S) ⟶ G.obj (Mod_.regular S)) :
    actionRight Dᴹᵒᵖ (Mod_.regular S) ⋙ F ⟶ actionRight Dᴹᵒᵖ (Mod_.regular S) ⋙ G :=
  (actionLineatorIso F (Mod_.regular S)).inv ≫ actionTransformation h ≫
    (actionLineatorIso G (Mod_.regular S)).hom

instance freeTransformation_moduleNatural
    (h : F.obj (Mod_.regular S) ⟶ G.obj (Mod_.regular S)) :
    IsModuleNatural Dᴹᵒᵖ (freeTransformation F G h) := by
  dsimp only [freeTransformation]
  infer_instance

@[simp] lemma freeTransformation_app
    (h : F.obj (Mod_.regular S) ⟶ G.obj (Mod_.regular S)) (X : Dᴹᵒᵖ) :
    (freeTransformation F G h).app X =
      Functor.OplaxLeftLinear.δₗ F X (Mod_.regular S) ≫ X ⊴ₗ h ≫
        Functor.LaxLeftLinear.μₗ G X (Mod_.regular S) := rfl

instance mixedLeftUnitor_moduleNatural (H : Mod_ D S ⥤ Mod_ D R)
    [H.LeftLinear Dᴹᵒᵖ] : IsModuleNatural Dᴹᵒᵖ (Functor.leftUnitor H).hom where
  lineator X N := by
    change (Functor.LaxLeftLinear.μₗ H X N ≫ H.map (𝟙 _)) ≫ 𝟙 _ =
      (X ⊴ₗ 𝟙 _) ≫ Functor.LaxLeftLinear.μₗ H X N
    simp

variable (Sep : SeparableAlgebra S)

/-- The actual separable free resolution extends a genuine regular
component to every actual module. -/
def transformation (h : F.obj (Mod_.regular S) ⟶ G.obj (Mod_.regular S)) : F ⟶ G :=
  (Functor.leftUnitor F).inv ≫ Functor.whiskerRight (wattsSection Sep) F ≫
    (Functor.associator wattsForget (actionRight Dᴹᵒᵖ (Mod_.regular S)) F).hom ≫
      Functor.whiskerLeft wattsForget (freeTransformation F G h) ≫
        (Functor.associator wattsForget (actionRight Dᴹᵒᵖ (Mod_.regular S)) G).inv ≫
          Functor.whiskerRight wattsCounit G ≫ (Functor.leftUnitor G).hom

instance transformation_moduleNatural
    (h : F.obj (Mod_.regular S) ⟶ G.obj (Mod_.regular S)) :
    IsModuleNatural Dᴹᵒᵖ (transformation F G Sep h) := by
  dsimp only [transformation]
  infer_instance

@[simp] lemma transformation_app
    (h : F.obj (Mod_.regular S) ⟶ G.obj (Mod_.regular S)) (N : Mod_ D S) :
    (transformation F G Sep h).app N = F.map ((wattsSection Sep).app N) ≫
      (freeTransformation F G h).app (mop N.X) ≫ G.map (wattsCounit.app N) := by
  simp only [transformation, NatTrans.comp_app, Functor.leftUnitor_hom_app,
    Functor.leftUnitor_inv_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, id_comp]
  erw [id_comp, comp_id]
  rfl

include Sep in
/-- Genuine module transformations are determined on the source regular
algebra by the canonical separable free retracts. -/
lemma transformation_ext (τ σ : F ⟶ G)
    [IsModuleNatural Dᴹᵒᵖ τ] [IsModuleNatural Dᴹᵒᵖ σ]
    (h : τ.app (Mod_.regular S) = σ.app (Mod_.regular S)) : τ = σ := by
  apply NatTrans.ext
  funext N
  let r : Retract N ((actionRight Dᴹᵒᵖ (Mod_.regular S)).obj (mop N.X)) :=
    { i := (wattsSection Sep).app N
      r := wattsCounit.app N
      retract := congrArg (fun a => a.app N) (wattsSection_counit Sep) }
  exact natTrans_app_eq_of_retract τ σ r
    (moduleNatTrans_app_action_eq τ σ (mop N.X) (Mod_.regular S) h)

/-- Actual preservation of the transported right source action is
precisely the compatibility with the regular resolution counit. -/
lemma freeTransformation_counit
    (h : mapActionModule F (wattsRegular (R := S)) ⟶
      mapActionModule G (wattsRegular (R := S))) :
    (freeTransformation F G h.hom).app (mop S) ≫
        G.map (wattsCounit.app (Mod_.regular S)) =
      F.map (wattsCounit.app (Mod_.regular S)) ≫ h.hom := by
  rw [wattsCounit_regular]
  apply (cancel_epi (Functor.LaxLeftLinear.μₗ F (mop S) (Mod_.regular S))).mp
  simp only [freeTransformation_app, ← assoc, Functor.LeftLinear.μₗ_comp_δₗ, id_comp]
  have hh := IsMod_Hom.smul_hom (A := mop S) (f := h.hom)
  change (Functor.LaxLeftLinear.μₗ F (mop S) (Mod_.regular S) ≫
      F.map γ[mop S,(wattsRegular (R := S)).X]) ≫ h.hom =
    ((mop S) ⊴ₗ h.hom) ≫ (Functor.LaxLeftLinear.μₗ G (mop S) (Mod_.regular S) ≫
      G.map γ[mop S,(wattsRegular (R := S)).X]) at hh
  simpa only [assoc] using hh.symm

lemma transformation_app_regular
    (h : mapActionModule F (wattsRegular (R := S)) ⟶
      mapActionModule G (wattsRegular (R := S))) :
    (transformation F G Sep h.hom).app (Mod_.regular S) = h.hom := by
  rw [transformation_app]
  erw [freeTransformation_counit]
  rw [← assoc, ← F.map_comp]
  have hs := congrArg (fun a => a.app (Mod_.regular S)) (wattsSection_counit Sep)
  change (wattsSection Sep).app (Mod_.regular S) ≫
    wattsCounit.app (Mod_.regular S) = 𝟙 _ at hs
  rw [hs, F.map_id, id_comp]

end Paper18.Category.BimoduleRelativeTensor.MixedWatts
