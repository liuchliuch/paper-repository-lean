import Paper18.Category.DrinfeldGeneralNondegenerateUnderlying
import Paper18.Category.DrinfeldGeneralNondegenerateHom

/-!
# Actual nondegeneracy of the Drinfeld center of a fusion category

A transparent central object has only unit constituents underneath, by the
actual induction coend test. Every underlying map between transparent
central objects is central, since every ambient object is an actual retract
of the underlying induction object. The underlying unit decomposition
therefore lifts to a unit decomposition in the actual center.
-/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u w
namespace Paper18.Category.Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
include S

/-- The actual Drinfeld center of an actual pivotal fusion category is
Müger nondegenerate. No ambient braiding, ambient nondegeneracy, positive
pivotal dimensions, sphericality, or center skeleton is assumed. -/
theorem center_nondegenerate (J : PivotalStructure C) :
    IsNondegenerate (C := Center C) := by
  intro Z hZ
  obtain ⟨n, ⟨e⟩⟩ := transparent_underlying_unitSum S J Z hZ
  let W : Center C := ⨁ fun _ : Fin n => 𝟙_ (Center C)
  have hW : W ∈ mugerCenter :=
    unitSum_mem_mugerCenter (C := Center C) ⟨n, ⟨Iso.refl W⟩⟩
  let e' : Z.1 ≅ W.1 := e ≪≫
    ((Center.forget C).mapBiproduct (fun _ : Fin n => 𝟙_ (Center C))).symm
  let f : Z ⟶ W := transparentHom S J Z W hZ hW e'.hom
  letI : IsIso f.f := by
    change IsIso e'.hom
    infer_instance
  exact ⟨n, ⟨Center.isoMk f⟩⟩

end Paper18.Category.Drinfeld
