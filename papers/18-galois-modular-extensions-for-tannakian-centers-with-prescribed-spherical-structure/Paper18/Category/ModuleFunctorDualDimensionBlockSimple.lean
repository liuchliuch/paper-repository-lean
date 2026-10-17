import Paper18.Category.ModuleFunctorDualDimensionBlock
import Paper18.Category.ModuleFunctorSemisimpleOrbit

/-! # The actual algebra block comes from a simple End unit -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonoidalLeftAction
universe v u w
namespace Paper18.Category.ModuleFunctor
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  [BraidedCategory D] [RightRigidCategory D]
  {R : D} [MonObj R] (S : SeparableAlgebra R)
  {ι : Type w} [Fintype ι] (T : FiniteSemisimpleSkeleton D ι) (j : S.SimpleIndex T)
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
attribute [local instance] MonoidalOppositeFusion.rightRigidCategory
attribute [local instance] Preadditive.hasEqualizers_of_hasKernels
local instance blockSimpleBaseFiniteLimits : HasFiniteLimits (Mod_ D R) :=
  hasFiniteLimits_of_hasEqualizers_and_finite_products
local instance blockSimpleComponentKernels : HasKernels (ModuleComponent.Component (C := Dᴹᵒᵖ) (S.skeleton T) j) :=
  ModuleComponent.hasKernels (S.skeleton T) j
local instance blockSimpleComponentFiniteLimits :
    HasFiniteLimits (ModuleComponent.Component (C := Dᴹᵒᵖ) (S.skeleton T) j) :=
  hasFiniteLimits_of_hasEqualizers_and_finite_products

/-- Extending the actual component tensor unit gives its actual projector. -/
def componentProjectionEndIso :
    (componentEndExtension (C := Dᴹᵒᵖ) (S.skeleton T) j).obj
      (𝟙_ (ModuleAlphaInduction.End Dᴹᵒᵖ (ModuleComponent.Component (C := Dᴹᵒᵖ) (S.skeleton T) j))) ≅
        componentProjectionEnd (C := Dᴹᵒᵖ) (S.skeleton T) j := by
  let P := (componentProjection (C := Dᴹᵒᵖ) (S.skeleton T) j).toFunctor
  let I := (componentInclusion (C := Dᴹᵒᵖ) (S.skeleton T) j).toFunctor
  letI : IsModuleNatural Dᴹᵒᵖ (Functor.rightUnitor P).hom :=
    { lineator X m := by
        change (𝟙 _ ≫ Functor.LaxLeftLinear.μₗ P X m) ≫ 𝟙 _ =
          (X ⊴ₗ 𝟙 _) ≫ Functor.LaxLeftLinear.μₗ P X m
        simp only [id_comp, comp_id, MonoidalLeftAction.actionHomRight_id] }
  letI : IsModuleNatural Dᴹᵒᵖ (Functor.isoWhiskerRight (Functor.rightUnitor P) I).hom :=
    { lineator X m := by
        change (Functor.LaxLeftLinear.μₗ I X (P.obj m) ≫
          I.map (𝟙 _ ≫ Functor.LaxLeftLinear.μₗ P X m)) ≫ I.map (𝟙 _) =
            (X ⊴ₗ I.map (𝟙 _)) ≫ Functor.LaxLeftLinear.μₗ I X (P.obj m) ≫
              I.map (Functor.LaxLeftLinear.μₗ P X m)
        simp only [id_comp, I.map_id, comp_id, MonoidalLeftAction.actionHomRight_id] }
  exact isoMk (Functor.isoWhiskerRight (Functor.rightUnitor P) I)

/-- The actual corner inclusion preserves the simple tensor unit, so the
actual projector is an actual simple endofunctor. -/
def componentProjectionEnd_simple : Simple (componentProjectionEnd (C := Dᴹᵒᵖ) (S.skeleton T) j) := by
  let TC := S.moduleComponentEndSkeleton T j
  let TE := wattsEndSkeleton S T
  let F := componentEndExtension (C := Dᴹᵒᵖ) (S.skeleton T) j
  letI : F.Additive := by dsimp only [F, componentEndExtension]; infer_instance
  letI : F.Linear ℂ := by dsimp only [F, componentEndExtension]; infer_instance
  letI : ∀ F G : ModuleAlphaInduction.End Dᴹᵒᵖ (Mod_ D R), FiniteDimensional ℂ (F ⟶ G) :=
    finiteDimensionalHom (S.skeleton T)
  letI : ∀ F G : ModuleAlphaInduction.End Dᴹᵒᵖ
      (ModuleComponent.Component (C := Dᴹᵒᵖ) (S.skeleton T) j), FiniteDimensional ℂ (F ⟶ G) :=
    finiteDimensionalHom (ModuleComponent.skeleton (S.skeleton T) j)
  letI := (componentEndExtensionFullyFaithful (C := Dᴹᵒᵖ) (S.skeleton T) j).full
  letI := (componentEndExtensionFullyFaithful (C := Dᴹᵒᵖ) (S.skeleton T) j).faithful
  letI : Simple (𝟙_ (ModuleAlphaInduction.End Dᴹᵒᵖ
      (ModuleComponent.Component (C := Dᴹᵒᵖ) (S.skeleton T) j))) :=
    componentEndUnit_simple (S.skeleton T) j TC
  letI := TE.simple_map F (𝟙_ _)
  exact CategoryTheory.Simple.of_iso (componentProjectionEndIso S T j).symm

/-- The algebra block itself is an actual simple regular-bimodule summand. -/
def orbitBlockBimodule_simple : Simple (orbitBlockBimodule S T j) := by
  letI : ∀ F G : ModuleAlphaInduction.End Dᴹᵒᵖ (Mod_ D R), FiniteDimensional ℂ (F ⟶ G) :=
    finiteDimensionalHom (S.skeleton T)
  letI := wattsEvaluation_full S
  letI := wattsEvaluation_faithful S
  letI := componentProjectionEnd_simple S T j
  exact (bimoduleSkeleton S T).simple_map wattsEvaluation _

/-- The algebra block lies in the actual chosen orbit as an old left module. -/
lemma orbitBlock_mem_component : ModuleComponent.property (C := Dᴹᵒᵖ) (S.skeleton T) j
    (orbitBlockBimodule S T j).X :=
  ((componentProjection (C := Dᴹᵒᵖ) (S.skeleton T) j).toFunctor.obj (Mod_.regular R)).property

/-- The actual block algebra is nonzero; this follows from actual simplicity
of its genuine two-sided module, rather than from a dimension premise. -/
lemma orbitBlock_ne_zero : (𝟙 (orbitBlockBimodule S T j).X.X) ≠ 0 := by
  letI := orbitBlockBimodule_simple S T j
  intro hz
  apply CategoryTheory.id_nonzero (orbitBlockBimodule S T j)
  apply Mod_.Hom.ext
  apply Mod_.Hom.ext
  exact hz

end Paper18.Category.ModuleFunctor
