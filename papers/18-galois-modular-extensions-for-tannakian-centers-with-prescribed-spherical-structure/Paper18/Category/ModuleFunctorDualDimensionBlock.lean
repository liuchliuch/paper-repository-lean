import Paper18.Category.ModuleFunctorDualDimensionBlockProjection
import Paper18.Category.ModuleFunctorSemisimpleWatts

/-! # The actual separable algebra block of a chosen module orbit -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u w
namespace Paper18.Category.ModuleFunctor
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  [BraidedCategory D] [RightRigidCategory D]
  {R : D} [MonObj R]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
attribute [local instance] MonoidalOppositeFusion.rightRigidCategory
attribute [local instance] Preadditive.hasEqualizers_of_hasKernels

local instance blockBaseFiniteLimits : HasFiniteLimits (Mod_ D R) :=
  hasFiniteLimits_of_hasEqualizers_and_finite_products

/-- Evaluation of the genuine identity module functor is the actual regular bimodule. -/
def wattsEvaluationUnitIso :
    wattsEvaluation.obj (ModuleAlphaInduction.endUnit Dᴹᵒᵖ (Mod_ D R)) ≅ wattsRegular (R := R) where
  hom := Mod_.Hom.mk' (𝟙 (Mod_.regular R)) (by
    change (𝟙 _ ≫ γ[mop R,(wattsRegular (R := R)).X]) ≫ 𝟙 _ =
      (mop R) ⊴ₗ (𝟙 (Mod_.regular R)) ≫ γ[mop R,(wattsRegular (R := R)).X]
    simp only [id_comp, comp_id, MonoidalLeftAction.actionHomRight_id])
  inv := Mod_.Hom.mk' (𝟙 (Mod_.regular R)) (by
    change γ[mop R,(wattsRegular (R := R)).X] ≫ 𝟙 _ =
      (mop R) ⊴ₗ (𝟙 (Mod_.regular R)) ≫ (𝟙 _ ≫ γ[mop R,(wattsRegular (R := R)).X])
    simp only [id_comp, comp_id, MonoidalLeftAction.actionHomRight_id])
  hom_inv_id := by
    apply Mod_.Hom.ext
    apply Mod_.Hom.ext
    change (𝟙 R : R ⟶ R) ≫ 𝟙 R = 𝟙 R
    simp
  inv_hom_id := by
    apply Mod_.Hom.ext
    apply Mod_.Hom.ext
    change (𝟙 R : R ⟶ R) ≫ 𝟙 R = 𝟙 R
    simp

variable (S : SeparableAlgebra R) {ι : Type w} [Fintype ι]
  (T : FiniteSemisimpleSkeleton D ι) (j : S.SimpleIndex T)

/-- The actual orbit projector evaluated on the regular algebra, with both actions. -/
def orbitBlockBimodule : Bimodules R :=
  wattsEvaluation.obj (componentProjectionEnd (S.skeleton T) j)

/-- The actual counit includes it into the actual regular bimodule. -/
def orbitBlockInclusion : orbitBlockBimodule S T j ⟶ wattsRegular (R := R) :=
  wattsEvaluation.map (componentProjectionCounit (S.skeleton T) j) ≫ wattsEvaluationUnitIso.hom

instance orbitBlockInclusion_mono : Mono (orbitBlockInclusion S T j) := by
  unfold orbitBlockInclusion
  infer_instance

/-- Actual two-sided semisimplicity splits the actual orbit block inclusion. -/
def orbitBlockRetract : Retract (orbitBlockBimodule S T j) (wattsRegular (R := R)) where
  i := orbitBlockInclusion S T j
  r := ((bimoduleSkeleton S T).splitMono (orbitBlockInclusion S T j)).retraction
  retract := ((bimoduleSkeleton S T).splitMono (orbitBlockInclusion S T j)).id

/-- The resulting actual quotient algebra on the actual block. -/
def orbitBlockMonObj : MonObj (orbitBlockBimodule S T j).X.X :=
  blockMonObj _ (orbitBlockRetract S T j)

/-- Separability is inherited through the actual split algebra epimorphism. -/
def orbitBlockSeparable : letI := orbitBlockMonObj S T j;
    SeparableAlgebra (orbitBlockBimodule S T j).X.X :=
  blockSeparable _ (orbitBlockRetract S T j) S

end Paper18.Category.ModuleFunctor
