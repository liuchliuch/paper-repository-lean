import Paper18.Category.BimoduleRelativeTensorBlockOrbitBasic
import Paper18.Category.BimoduleRelativeTensorModuleInverse

/-! # The actual strong module equivalence from a quotient block to its orbit -/
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

abbrev Component := ModuleComponent.Component (C := Dᴹᵒᵖ) (S.skeleton T) j

/-- The actual scalar restriction lands in the actual chosen orbit. -/
def intoComponent : Mod_ D (algebra S T j) ⥤ Component S T j where
  obj M := ⟨(restrictionFunctor S T j).obj M,
    (restriction_essImage_iff S T j _).mp ((restrictionFunctor S T j).obj_mem_essImage M)⟩
  map f := (restrictionFunctor S T j).map f
  map_id M := (restrictionFunctor S T j).map_id M
  map_comp f g := (restrictionFunctor S T j).map_comp f g

instance intoComponent_faithful : (intoComponent S T j).Faithful where
  map_injective {M N} f g h := (restrictionFunctor S T j).map_injective h

instance intoComponent_full : (intoComponent S T j).Full where
  map_surjective {M N} f :=
    ⟨(restrictionFunctor S T j).preimage f, (restrictionFunctor S T j).map_preimage f⟩

instance intoComponent_essSurj : (intoComponent S T j).EssSurj where
  mem_essImage M := by
    obtain ⟨N, ⟨e⟩⟩ := (restriction_essImage_iff S T j M.obj).mpr M.property
    exact ⟨N, ⟨(ModuleComponent.property (C := Dᴹᵒᵖ) (S.skeleton T) j).isoMk e⟩⟩

instance intoComponent_additive : (intoComponent S T j).Additive where
  map_add := (restrictionFunctor S T j).map_add

instance intoComponent_linear : (intoComponent S T j).Linear ℂ where
  map_smul f z := (restrictionFunctor S T j).map_smul z f

/-- The genuine restricted lineators, as actual maps within the actual
full orbit component. -/
def intoComponentLaxLeftLinear : (intoComponent S T j).LaxLeftLinear Dᴹᵒᵖ where
  μₗ X M := Functor.LaxLeftLinear.μₗ (restrictionFunctor S T j) X M
  μₗ_naturality_left f M :=
    Functor.LaxLeftLinear.μₗ_naturality_left (restrictionFunctor S T j) f M
  μₗ_naturality_right X M N f :=
    Functor.LaxLeftLinear.μₗ_naturality_right (restrictionFunctor S T j) X f
  μₗ_associativity X Y M :=
    Functor.LaxLeftLinear.μₗ_associativity (restrictionFunctor S T j) X Y M
  μₗ_unitality M := Functor.LaxLeftLinear.μₗ_unitality (restrictionFunctor S T j) M

instance intoComponent_leftLinear : (intoComponent S T j).LeftLinear Dᴹᵒᵖ := by
  letI := intoComponentLaxLeftLinear S T j
  letI (X : Dᴹᵒᵖ) (M : Mod_ D (algebra S T j)) :
      IsIso (Functor.LaxLeftLinear.μₗ (intoComponent S T j) X M) := by
    let I := (ModuleComponent.property (C := Dᴹᵒᵖ) (S.skeleton T) j).ι
    letI : IsIso (I.map (Functor.LaxLeftLinear.μₗ (intoComponent S T j) X M)) := by
      change IsIso (Functor.LaxLeftLinear.μₗ (restrictionFunctor S T j) X M)
      infer_instance
    exact isIso_of_fully_faithful I _
  exact ModuleFunctor.leftLinearOfLax (intoComponent S T j)

/-- Actual full faithfulness and actual orbit-image equality produce
the actual equivalence; essential surjectivity is proved above. -/
def equivalence : Mod_ D (algebra S T j) ≌ Component S T j := by
  letI : (intoComponent S T j).IsEquivalence := {}
  exact (intoComponent S T j).asEquivalence

instance equivalence_functorLeftLinear : (equivalence S T j).functor.LeftLinear Dᴹᵒᵖ := by
  change (intoComponent S T j).LeftLinear Dᴹᵒᵖ
  infer_instance

instance equivalence_functorAdditive : (equivalence S T j).functor.Additive := by
  change (intoComponent S T j).Additive
  infer_instance

instance equivalence_functorLinear : (equivalence S T j).functor.Linear ℂ := by
  change (intoComponent S T j).Linear ℂ
  infer_instance

instance equivalence_inverseLeftLinear : (equivalence S T j).inverse.LeftLinear Dᴹᵒᵖ :=
  ModuleInverse.inverseLeftLinear (C := Dᴹᵒᵖ) (equivalence S T j)

instance equivalence_unit_moduleNatural : IsModuleNatural Dᴹᵒᵖ (equivalence S T j).unitIso.hom :=
  ModuleInverse.unit_moduleNatural (C := Dᴹᵒᵖ) (equivalence S T j)

instance equivalence_counit_moduleNatural : IsModuleNatural Dᴹᵒᵖ (equivalence S T j).counitIso.hom :=
  ModuleInverse.counit_moduleNatural (C := Dᴹᵒᵖ) (equivalence S T j)

end Paper18.Category.BimoduleRelativeTensor.BlockOrbit
