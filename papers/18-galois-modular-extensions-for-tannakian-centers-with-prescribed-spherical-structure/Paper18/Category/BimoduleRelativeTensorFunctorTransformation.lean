import Paper18.Category.BimoduleRelativeTensorFunctorStrong
import Paper18.Category.BimoduleRelativeTensorFunctorLinear

/-! # Bimodule morphisms give actual strong-module transformations -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u
namespace Paper18.Category.BimoduleRelativeTensor
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [HasCoequalizers D] [LeftRigidCategory D] [RightRigidCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
variable {R S : D} [MonObj R] [MonObj S]

/-- The actual additive linear strong module functor defined by an actual
bimodule and the actual balancing quotient. -/
def tensorBundled (P : Native R S) : ModuleFunctor.Bundled Dᴹᵒᵖ (Mod_ D S) (Mod_ D R) where
  toFunctor := tensorFunctor P
  leftLinear := inferInstance
  additive := inferInstance
  linear := inferInstance

/-- An actual bimodule map acts by actual relative right whiskering. -/
def tensorNat {P P' : Native R S} (f : P ⟶ P') : tensorFunctor P ⟶ tensorFunctor P' where
  app N := (whiskerRight f (moduleAsNative N)).hom
  naturality {N N'} g := by
    apply Mod_.Hom.ext
    exact congrArg Bimod.Hom.hom (Bimod.whisker_exchange_bimod
      ((toBimod R S).map f) ((toBimod S (𝟙_ D)).map (moduleAsNativeFunctor.map g)))

@[reassoc (attr := simp)]
lemma moduleπ_tensorNat {P P' : Native R S} (f : P ⟶ P') (N : Mod_ D S) :
    moduleπ P N ≫ ((tensorNat f).app N).hom = f.hom.hom ▷ N.X ≫ moduleπ P' N :=
  π_whiskerRight f (moduleAsNative N)

instance tensorNat_moduleNatural {P P' : Native R S} (f : P ⟶ P') :
    ModuleFunctor.IsModuleNatural Dᴹᵒᵖ (tensorNat f) where
  lineator X N := by
    apply Mod_.Hom.ext
    change lineatorRaw P N X.unmop ≫
        ((tensorNat f).app (RelativeTensor.ambientTensor N X.unmop)).hom =
      ((tensorNat f).app N).hom ▷ X.unmop ≫ lineatorRaw P' N X.unmop
    apply (cancel_epi (moduleπ P N ▷ X.unmop)).mp
    rw [moduleπ_lineatorRaw_assoc, moduleπ_tensorNat,
      ← comp_whiskerRight_assoc, moduleπ_tensorNat, comp_whiskerRight_assoc,
      moduleπ_lineatorRaw]
    monoidal

/-- Actual relative tensor is functorial from bimodules to actual strong
ambient-module functors. -/
def tensorRepresentation : Native R S ⥤
    ModuleFunctor.Bundled Dᴹᵒᵖ (Mod_ D S) (Mod_ D R) where
  obj := tensorBundled
  map f := ⟨tensorNat f, tensorNat_moduleNatural f⟩
  map_id P := by
    apply Subtype.ext
    apply NatTrans.ext
    funext N
    apply Mod_.Hom.ext
    exact congrArg Bimod.Hom.hom (Bimod.id_whiskerRight_bimod
      (M := toBimodObj R S P) (N := leftModuleBimod N))
  map_comp f g := by
    apply Subtype.ext
    apply NatTrans.ext
    funext N
    apply Mod_.Hom.ext
    exact congrArg Bimod.Hom.hom (Bimod.comp_whiskerRight_bimod
      ((toBimod R S).map f) ((toBimod R S).map g) (leftModuleBimod N))

end Paper18.Category.BimoduleRelativeTensor
