import Paper18.Category.GraphPicardMoritaGraphAdjoint
import Paper18.Category.RelativeTensorRigid
import Paper18.Category.SemisimpleCokernels

/-! # Actual monicity of the graph algebra map

Connected separable algebras are simple as their actual regular modules.
A genuine nonzero algebra map is therefore monic, by viewing it as a
map to the actual restriction of the target regular module.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj ModObj MonoidalLeftAction
universe v u w
namespace Paper18.Category.GraphPicard.Morita
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [RightRigidCategory C] [HasCoequalizers C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {A B : C} [MonObj A] [IsCommMonObj A] [MonObj B]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (s : SeparableAlgebra A)

/-- A genuine algebra map is a genuine map of actual left modules. -/
def algebraHomRegular (f : A ⟶ B) [IsMonHom f] :
    Mod_.regular A ⟶ (Mod_.comap (D := C) f).obj (Mod_.regular B) :=
  Mod_.Hom.mk' f (by
    change μ[A] ≫ f = A ◁ f ≫ (f ▷ B ≫ μ[B])
    rw [IsMonHom.mul_hom, tensorHom_def', Category.assoc])

include S s in
/-- A nonzero map out of a connected actual separable algebra is monic.
The proof uses actual regular-module simplicity, not an injectivity field. -/
lemma mono_algebraHom_of_connected (hc : Module.finrank ℂ (𝟙_ C ⟶ A) = 1)
    (f : A ⟶ B) [IsMonHom f] (hf : f ≠ 0) : Mono f := by
  letI : Simple (Mod_.regular A) := SeparableAlgebra.moduleSimpleUnit s S hc
  have hn : algebraHomRegular f ≠ 0 := by
    intro h
    exact hf (congrArg Mod_.Hom.hom h)
  letI : Mono (algebraHomRegular f) := mono_of_nonzero_from_simple hn
  exact inferInstanceAs (Mono ((Mod_.forget (D := C) A).map (algebraHomRegular f)))

end Paper18.Category.GraphPicard.Morita

namespace Paper18.Category.GraphPicard
attribute [local instance 2000] RightRigidCategory.rightDual
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)
  (α : D ⥤ D) [α.Braided] [α.Additive] [α.Linear ℂ] [α.IsEquivalence]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
local notation "M" => GraphLagrangian.ModuleOrbit S α
local notation "E" => ModuleAlphaInduction.End Dᴹᵒᵖ M
local notation "R" => GraphLagrangian.underlyingSeparableNoPivotal S α
local notation "hR" => GraphLagrangian.underlying_id_ne_zero S α

/-- The actual transpose is nonzero because its actual character acts
by the identity on the actual component unit. -/
lemma graphAlgebraToAdjointUnit_ne_zero : graphAlgebraToAdjointUnit S α ≠ 0 := by
  letI := graphEndSimpleUnit S α
  intro h
  have hq : graphComponentCharacter S α = 0 := by
    rw [← graphAlgebraToAdjointUnit_counit S α, h, Functor.map_zero, zero_comp]
  have hu := componentCentralCharacter_one (GraphLagrangian.algebra S α)
    (GraphLagrangian.moduleSkeleton S α) (SeparableAlgebra.orbitLabel R S hR)
  change (rightCentralUnitIso D M).hom ≫
    (rightCentralAction D M).map η[GraphLagrangian.algebra S α] ≫
      graphComponentCharacter S α = 𝟙 _ at hu
  rw [hq, comp_zero, comp_zero] at hu
  exact CategoryTheory.id_nonzero (𝟙_ E) hu.symm

/-- The actual graph algebra embeds in the actual right-adjoint unit;
its connectedness is derived from actual ambient nondegeneracy. -/
def graphAlgebraToAdjointUnit_mono (hD : IsNondegenerate (C := D)) :
    Mono (graphAlgebraToAdjointUnit S α) := by
  let SC := DrinfeldCoendModules.centerSkeletonNoPivotal S
  letI := SC.hasCoequalizers
  exact Morita.mono_algebraHom_of_connected SC (GraphLagrangian.separableNoPivotal S α)
    (GraphLagrangian.connected S α hD) (graphAlgebraToAdjointUnit S α)
    (graphAlgebraToAdjointUnit_ne_zero S α)

end Paper18.Category.GraphPicard
