import Paper18.Category.BimoduleRelativeTensorBlockRegularSimple
import Paper18.Category.ModuleFunctorDualDimensionBlockImage

/-! # The actual quotient-block restriction image is the chosen orbit -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u w
namespace Paper18.Category.BimoduleRelativeTensor.BlockOrbit
open ModuleFunctor
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  [BraidedCategory D] [RightRigidCategory D]
  {R : D} [MonObj R] (S : SeparableAlgebra R)
  {ι : Type w} [Fintype ι] (T : FiniteSemisimpleSkeleton D ι) (j : S.SimpleIndex T)
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
attribute [local instance] MonoidalOppositeFusion.rightRigidCategory

/-- The actual algebra of the actual regular bimodule orbit block. -/
abbrev algebra : D := (orbitBlockBimodule S T j).X.X

instance algebraMonObj : MonObj (algebra S T j) := orbitBlockMonObj S T j

def projection : R ⟶ algebra S T j :=
  blockProjection (orbitBlockBimodule S T j) (orbitBlockRetract S T j)

instance projection_isMonHom : IsMonHom (projection S T j) :=
  blockProjection_isMonHom (orbitBlockBimodule S T j) (orbitBlockRetract S T j)

instance projection_isSplitEpi : IsSplitEpi (projection S T j) :=
  Block.blockProjection_isSplitEpi (orbitBlockBimodule S T j) (orbitBlockRetract S T j)

def separable : SeparableAlgebra (algebra S T j) := orbitBlockSeparable S T j

def restrictionFunctor : Mod_ D (algebra S T j) ⥤ Mod_ D R :=
  Mod_.comap (projection S T j)

instance restrictionFunctor_faithful : (restrictionFunctor S T j).Faithful := by
  unfold restrictionFunctor
  infer_instance

instance restrictionFunctor_full : (restrictionFunctor S T j).Full := by
  unfold restrictionFunctor
  infer_instance

instance restrictionFunctor_additive : (restrictionFunctor S T j).Additive := by
  unfold restrictionFunctor
  infer_instance

instance restrictionFunctor_linear : (restrictionFunctor S T j).Linear ℂ := by
  unfold restrictionFunctor
  infer_instance

instance restrictionFunctor_leftLinear : (restrictionFunctor S T j).LeftLinear Dᴹᵒᵖ :=
  Block.restrictionLeftLinear (projection S T j)

def regularLeftIso :
    (restrictionFunctor S T j).obj (Mod_.regular (algebra S T j)) ≅
      (orbitBlockBimodule S T j).X :=
  Block.restrictedRegularLeftIso (orbitBlockBimodule S T j) (orbitBlockRetract S T j)

lemma regularImage_mem : ModuleComponent.property (C := Dᴹᵒᵖ) (S.skeleton T) j
    ((restrictionFunctor S T j).obj (Mod_.regular (algebra S T j))) :=
  IsAdditiveFullProperty.of_iso _ (regularLeftIso S T j) (orbitBlock_mem_component S T j)

lemma regularImage_ne_zero :
    (𝟙 ((restrictionFunctor S T j).obj (Mod_.regular (algebra S T j)))) ≠ 0 := by
  intro h
  apply orbitBlock_ne_zero S T j
  exact congrArg Mod_.Hom.hom h

/-- Every actual block module is an actual retract of an ambient action
on its actual regular module, by the canonical separability splitting. -/
lemma regular_retract_dominant (M : Mod_ D (algebra S T j)) :
    ∃ X : Dᴹᵒᵖ, Nonempty (Retract M (X ⊙ₗ Mod_.regular (algebra S T j))) := by
  refine ⟨mop M.X, ⟨((separable S T j).freeRetract M).trans ?_⟩⟩
  exact Retract.ofIso (wattsFreeIso (R := algebra S T j) M.X).symm

/-- Actual source free retracts and target orbit connectivity identify
the actual image exactly, with no essential-surjectivity premise. -/
theorem restriction_essImage_iff (M : Mod_ D R) :
    (restrictionFunctor S T j).essImage M ↔
      ModuleComponent.property (C := Dᴹᵒᵖ) (S.skeleton T) j M :=
  moduleEssImage_eq_component (C := Dᴹᵒᵖ) (S.skeleton T)
    (restrictionFunctor S T j) (Mod_.regular (algebra S T j)) j
    (regular_retract_dominant S T j) (regularImage_mem S T j) (regularImage_ne_zero S T j) M

end Paper18.Category.BimoduleRelativeTensor.BlockOrbit
