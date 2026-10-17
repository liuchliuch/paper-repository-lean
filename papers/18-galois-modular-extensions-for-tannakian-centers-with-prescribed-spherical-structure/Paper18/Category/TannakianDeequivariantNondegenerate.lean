import Paper18.Category.TannakianDeequivariantNondegenerateBasic
import Paper18.Category.RepresentationTrivialUnitSum

/-!
# Actual nondegeneracy of Tannakian de-equivariantization

Transparency descends to the underlying ambient object.  The actual
Tannakian identification then realizes it as a representation, whose free
module is a finite sum of units by regular absorption.  Separability gives
an actual retract, so every transparent simple module is the tensor unit.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open CategoryTheory.Functor.Monoidal
universe v u w
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [HasCoequalizers C]
  {G : Type} [Group G] [Fintype G] (T : TannakianCenter C G)

omit [HasKernels C] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] in
/-- The free module on a representation is a genuine finite direct sum
of the regular unit module. -/
theorem TannakianCenter.free_inclusion_isUnitSum (V : FDRep ℂ G) :
    IsUnitSum (T.deequivariantFree.obj (T.inclusion.obj V)) := by
  let e := InternalModule.mapFreeIso T.inclusion
    (Representation.regularAbsorptionModuleIso V)
  apply IsUnitSum.of_iso e
  obtain ⟨n, ⟨f⟩⟩ := Representation.trivialUnderlying_isUnitSum V
  let F := T.inclusion ⋙ T.deequivariantFree
  refine ⟨n, ⟨F.mapIso f ≪≫ F.mapBiproduct (fun _ : Fin n => 𝟙_ (FDRep ℂ G)) ≪≫
    biproduct.mapIso (fun _ => (εIso F).symm)⟩⟩

variable {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

include S in
/-- De-equivariantization by the actual full Tannakian Müger center is
Müger nondegenerate, with its constructed module tensor and braiding. -/
theorem TannakianCenter.deequivariant_isNondegenerate :
    letI := T.deequivariantBraided
    IsNondegenerate (C := T.Deequivariantization) := by
  letI := T.deequivariantBraided
  letI := T.deequivariantSimpleUnit S
  let D := T.deequivariantSkeleton S
  apply (nondegenerate_iff_simple_center D).mpr
  intro i hi
  have hu : (D.simpleObject i).X ∈ mugerCenter (C := C) :=
    underlying_transparent_of_module_transparent T.regularAlgebra_transparent
      (D.simpleObject i) hi
  obtain ⟨V, ⟨e⟩⟩ := T.exists_representation _ hu
  let r := T.regularAlgebraSeparable.freeRetract (D.simpleObject i)
  let r' := r.trans (Retract.ofIso (T.deequivariantFree.mapIso e).symm)
  obtain ⟨f⟩ := iso_unit_of_simple_retract_unitSum r' (T.free_inclusion_isUnitSum V)
  exact D.iso_injective i D.unitLabel ⟨f ≪≫ D.unitIso.symm⟩

end Paper18.Category
