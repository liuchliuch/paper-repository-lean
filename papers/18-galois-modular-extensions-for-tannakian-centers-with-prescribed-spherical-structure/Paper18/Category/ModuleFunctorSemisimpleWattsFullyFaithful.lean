import Paper18.Category.ModuleFunctorSemisimpleWattsHom

/-! # Actual full faithfulness of Eilenberg--Watts evaluation -/
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

lemma wattsCounit_regular : (wattsCounit (R := R)).app (Mod_.regular R) =
    γ[mop R,(wattsRegular (R := R)).X] := by
  apply Mod_.Hom.ext
  change 𝟙 _ ≫ μ[R] = μ[R]
  exact id_comp _

variable (F G : Mod_ D R ⥤ Mod_ D R) [F.LeftLinear Dᴹᵒᵖ] [G.LeftLinear Dᴹᵒᵖ]

/-- Compatibility with actual right multiplication is exactly the
compatibility needed on the regular free resolution. -/
lemma wattsFreeTransformation_counit
    (h : mapActionModule F (wattsRegular (R := R)) ⟶ mapActionModule G wattsRegular) :
    (wattsFreeTransformation F G h.hom).app (mop R) ≫ G.map (wattsCounit.app (Mod_.regular R)) =
      F.map (wattsCounit.app (Mod_.regular R)) ≫ h.hom := by
  rw [wattsCounit_regular]
  apply (cancel_epi (Functor.LaxLeftLinear.μₗ F (mop R) (Mod_.regular R))).mp
  simp only [wattsFreeTransformation_app, ← assoc, Functor.LeftLinear.μₗ_comp_δₗ,
    id_comp]
  have hh := IsMod_Hom.smul_hom (A := mop R) (f := h.hom)
  change (Functor.LaxLeftLinear.μₗ F (mop R) (Mod_.regular R) ≫
    F.map γ[mop R,(wattsRegular (R := R)).X]) ≫ h.hom =
      ((mop R) ⊴ₗ h.hom) ≫ (Functor.LaxLeftLinear.μₗ G (mop R) (Mod_.regular R) ≫
        G.map γ[mop R,(wattsRegular (R := R)).X]) at hh
  simpa only [assoc] using hh.symm

variable (S : SeparableAlgebra R)

/-- The actual extension of a bimodule map has its specified value at the
regular algebra; separability supplies the splitting used in the proof. -/
lemma wattsTransformation_app_regular
    (h : mapActionModule F (wattsRegular (R := R)) ⟶ mapActionModule G wattsRegular) :
    (wattsTransformation F G S h.hom).app (Mod_.regular R) = h.hom := by
  rw [wattsTransformation_app]
  erw [wattsFreeTransformation_counit]
  rw [← assoc, ← F.map_comp]
  have hs := congrArg (fun a => a.app (Mod_.regular R)) (wattsSection_counit S)
  change (wattsSection S).app (Mod_.regular R) ≫ wattsCounit.app (Mod_.regular R) = 𝟙 _ at hs
  rw [hs, F.map_id, id_comp]

variable [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]

/-- Actual evaluation at the regular algebra detects every module
transformation by the actual free retracts. -/
instance wattsEvaluation_faithful : (wattsEvaluation (R := R)).Faithful where
  map_injective {F G} τ σ h := by
    apply Subtype.ext
    apply wattsTransformation_ext F.toFunctor G.toFunctor S τ.val σ.val
    exact congrArg Mod_.Hom.hom h

/-- The actual extension of a genuine bimodule map is a genuine module
natural transformation between the specified strong functors. -/
def wattsHomPreimage {F G : Bundled Dᴹᵒᵖ (Mod_ D R) (Mod_ D R)}
    (h : wattsEvaluation.obj F ⟶ wattsEvaluation.obj G) : F ⟶ G :=
  ⟨wattsTransformation F.toFunctor G.toFunctor S h.hom,
    wattsTransformation_moduleNatural F.toFunctor G.toFunctor S h.hom⟩

@[simp]
lemma wattsEvaluation_map_preimage {F G : Bundled Dᴹᵒᵖ (Mod_ D R) (Mod_ D R)}
    (h : wattsEvaluation.obj F ⟶ wattsEvaluation.obj G) :
    wattsEvaluation.map (wattsHomPreimage S h) = h := by
  apply Mod_.Hom.ext
  exact wattsTransformation_app_regular F.toFunctor G.toFunctor S h

/-- Fullness is derived by the actual separable extension formula. -/
instance wattsEvaluation_full : (wattsEvaluation (R := R)).Full where
  map_surjective h := ⟨wattsHomPreimage S h, wattsEvaluation_map_preimage S h⟩

/-- The actual Eilenberg--Watts full faithful functor to genuine bimodules. -/
def wattsEvaluationFullyFaithful : (wattsEvaluation (R := R)).FullyFaithful := by
  letI := wattsEvaluation_faithful S
  letI := wattsEvaluation_full S
  exact Functor.FullyFaithful.ofFullyFaithful _

end Paper18.Category.ModuleFunctor
