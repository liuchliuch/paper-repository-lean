import Paper18.Category.FixedBoundaryMinimalExistenceTannakian
import Paper18.Category.FixedBoundaryMinimalSpherical
import Paper18.Category.NondegenerateExtension

/-! # Actual spherical output from genuinely realized C₂ crossed data

All extension structures and conclusions are constructed. The actual
Picard crossed-realization input is still required and is not asserted here.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits Functor.LaxMonoidal
open Paper18.Category.CrossedBraidedGauging
universe v u w v' u' w'
namespace Paper18.Category.FixedBoundary.MinimalExistence
attribute [local instance] ModularExtension.category ModularExtension.preadditive
  ModularExtension.linear ModularExtension.kernels ModularExtension.biproducts
  ModularExtension.finiteHom ModularExtension.monoidal ModularExtension.monoidalPreadditive
  ModularExtension.monoidalLinear ModularExtension.rightRigid ModularExtension.simpleUnit
  ModularExtension.braiding ModularExtension.finiteIndex
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)] [HasCoequalizers C]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (T : TannakianCenter C C2)

local instance sphericalDeeqRightRigid : RightRigidCategory T.Deequivariantization := T.deequivariantRightRigid
local instance sphericalDeeqBraided : BraidedCategory T.Deequivariantization := T.deequivariantBraided
local instance sphericalDeeqActionBraided : T.deequivariantAction.IsBraided := T.deequivariantActionBraided
local instance sphericalDescentBraided : T.descentComparison.Braided := T.descentComparisonBraided

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [RightRigidCategory D] [Simple (𝟙_ D)]
  {κ : Type w'} [Fintype κ] (SD : FiniteSemisimpleSkeleton D κ)
  {H : WeakAction C2 D}
  [∀ g : C2, (H.ρ g).Monoidal] [H.IsMonoidal]
  [∀ g : C2, (H.ρ g).Additive] [∀ g : C2, (H.ρ g).Linear ℂ]
  {P : Grading C2 D} {Q : GradedAction P H} (B : CrossedBraiding P H Q)
  (F : T.deequivariantAction.Intertwiner H) [F.functor.Monoidal] [F.IsMonoidal]
  [F.functor.Additive] [F.functor.Linear ℂ] [F.functor.Full] [F.functor.Faithful]
  (hdeg : ∀ X : T.Deequivariantization, P.Homogeneous 1 (F.functor.obj X))
  (hcover : ∀ Y : D, P.Homogeneous 1 Y →
    ∃ X : T.Deequivariantization, Nonempty (F.functor.obj X ≅ Y))

/-- Once genuine crossed components have been realized, the actual
minimal extension carries an actual modular pivotal structure extending
the prescribed source structure, with integral actual centralizer.
This intermediate constructor does not assert crossed realization. -/
def tannakianModularExtensionOfCrossedData (hf : P.Faithful)
    (hβ : ∀ X Y : T.Deequivariantization,
      μ F.functor X Y ≫ F.functor.map (β_ X Y).hom =
        (B.neutralIso (F.functor.obj X) (hdeg X) (F.functor.obj Y)).hom ≫ μ F.functor Y X)
    (J : PivotalStructure C) (hJ : J.Spherical) (hd : J.rightDim T.c2Generator = -1) :
    ModularExtension J := by
  let E := tannakianMinimalExtensionOfCrossedData S T SD B F hdeg hcover hf hβ
  let h := spherical_extension_of_c2_minimal S T J hJ hd E
  let K := Classical.choose h
  have hK := (Classical.choose_spec h).1
  have hpres := (Classical.choose_spec h).2
  refine
    { ambient := E.ambient
      index := E.index
      skeleton := E.skeleton
      pivotal := K
      modular := ⟨hK, E.nondegenerate⟩
      embedding :=
        { functor := E.inclusion
          pivotal := hpres }
      integralCentralizer := ?_ }
  exact tannakianSourceEmbeddingCentralizerIntegral S T SD B F hdeg hcover hf hβ

/-- The constructed ambient dimension is exactly twice the prescribed
source dimension; the spherical enhancement does not change its category. -/
theorem tannakianModularExtensionOfCrossedData_minimal (hf : P.Faithful)
    (hβ : ∀ X Y : T.Deequivariantization,
      μ F.functor X Y ≫ F.functor.map (β_ X Y).hom =
        (B.neutralIso (F.functor.obj X) (hdeg X) (F.functor.obj Y)).hom ≫ μ F.functor Y X)
    (J : PivotalStructure C) (hJ : J.Spherical) (hd : J.rightDim T.c2Generator = -1) :
    (tannakianModularExtensionOfCrossedData S T SD B F hdeg hcover hf hβ J hJ hd).skeleton.fusionBasis.totalFPdim =
      2 * S.fusionBasis.totalFPdim := by
  exact (tannakianMinimalExtensionOfCrossedData S T SD B F hdeg hcover hf hβ).minimal

end Paper18.Category.FixedBoundary.MinimalExistence
