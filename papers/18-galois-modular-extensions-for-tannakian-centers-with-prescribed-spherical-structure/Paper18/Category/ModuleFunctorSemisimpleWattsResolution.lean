import Paper18.Category.ModuleFunctorSemisimpleWattsAction
import Paper18.Category.ModuleFunctorSemisimpleSeparableAction

/-! # The actual separable free resolution respects the ambient action -/
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

/-- The actual action on the regular module followed by its genuine
forgetful functor is the free-module endofunctor. -/
def wattsResolution : Mod_ D R ⥤ Mod_ D R :=
  wattsForget ⋙ actionRight Dᴹᵒᵖ (Mod_.regular R)

instance wattsResolutionLeftLinear : (wattsResolution (R := R)).LeftLinear Dᴹᵒᵖ := by
  dsimp only [wattsResolution]
  infer_instance

@[simp]
lemma wattsResolution_μ_hom (X : Dᴹᵒᵖ) (M : Mod_ D R) :
    (Functor.LaxLeftLinear.μₗ (wattsResolution (R := R)) X M).hom =
      (α_ R M.X X.unmop).hom := by
  change (α_ R M.X X.unmop).hom ≫ (R ◁ 𝟙 _) = _
  simp

/-- The ambient free object and the regular action object carry the same
actual algebra action. -/
def wattsFreeIso (X : D) :
    (actionRight Dᴹᵒᵖ (Mod_.regular R)).obj (mop X) ≅ InternalModule.free R X where
  hom := Mod_.Hom.mk' (𝟙 _) (by change _ ≫ 𝟙 _ = (R ◁ 𝟙 _) ≫ _; simp)
  inv := Mod_.Hom.mk' (𝟙 _) (by change _ ≫ 𝟙 _ = (R ◁ 𝟙 _) ≫ _; simp)
  hom_inv_id := by apply Mod_.Hom.ext; simp
  inv_hom_id := by apply Mod_.Hom.ext; simp

/-- The actual free resolution counit. -/
def wattsCounit : wattsResolution (R := R) ⟶ 𝟭 (Mod_ D R) where
  app X := (wattsFreeIso X.X).hom ≫ InternalModule.actionHom X
  naturality {X Y} f := by
    apply Mod_.Hom.ext
    change (R ◁ f.hom) ≫ (𝟙 _ ≫ γ[R,Y.X]) =
      (𝟙 _ ≫ γ[R,X.X]) ≫ f.hom
    simpa only [id_comp] using (IsMod_Hom.smul_hom (A := R) (f := f.hom)).symm

instance wattsCounit_moduleNatural : IsModuleNatural Dᴹᵒᵖ (wattsCounit (R := R)) where
  lineator X M := by
    apply Mod_.Hom.ext
    simp only [Mod_.comp_hom', wattsResolution_μ_hom]
    change (α_ R M.X X.unmop).hom ≫
        (𝟙 _ ≫ ((α_ R M.X X.unmop).inv ≫ γ[R,M.X] ▷ X.unmop)) =
      (𝟙 _ ≫ γ[R,M.X]) ▷ X.unmop ≫ 𝟙 _
    simp

variable (S : SeparableAlgebra R)

/-- The actual separability section is natural as a map to the free
resolution. -/
def wattsSection : 𝟭 (Mod_ D R) ⟶ wattsResolution where
  app X := S.moduleSectionHom X ≫ (wattsFreeIso X.X).inv
  naturality {X Y} f := by
    apply Mod_.Hom.ext
    change f.hom ≫ (S.moduleSection Y ≫ 𝟙 _) =
      (S.moduleSection X ≫ 𝟙 _) ≫ (R ◁ f.hom)
    simpa only [comp_id] using S.moduleSection_naturality f

/-- Tensoring the actual separable section is compatible with actual
free reassociation. This is the action-functor image of naturality. -/
lemma wattsSection_tensor (X : Mod_ D R) (Y : D) :
    S.moduleSection (RelativeTensor.ambientTensor X Y) =
      (S.moduleSection X ▷ Y) ≫ (α_ R X.X Y).hom := by
  dsimp only [SeparableAlgebra.moduleSection, RelativeTensor.ambientTensor]
  monoidal

instance wattsSection_moduleNatural : IsModuleNatural Dᴹᵒᵖ (wattsSection S) where
  lineator X M := by
    apply Mod_.Hom.ext
    simp only [Mod_.comp_hom', wattsResolution_μ_hom]
    change 𝟙 _ ≫ (S.moduleSection (RelativeTensor.ambientTensor M X.unmop) ≫ 𝟙 _) =
      (S.moduleSection M ≫ 𝟙 _) ▷ X.unmop ≫ (α_ R M.X X.unmop).hom
    simp only [id_comp, comp_id, wattsSection_tensor]

@[reassoc (attr := simp)]
lemma wattsSection_counit : wattsSection S ≫ wattsCounit = 𝟙 (𝟭 (Mod_ D R)) := by
  ext X
  change (S.moduleSection X ≫ 𝟙 _) ≫ (𝟙 _ ≫ γ[R,X.X]) = 𝟙 X.X
  simp [S.moduleSection_action]

end Paper18.Category.ModuleFunctor
