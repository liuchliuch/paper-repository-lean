import Paper18.Category.LocalModulesCoherence
import Paper18.Category.SeparableModulesSemisimple
import Paper18.Category.FusionSubcategoryBasic

/-! # Actual finite semisimplicity of local modules

Locality is stable under actual retracts and finite biproducts. Restricting
the actual separable-module skeleton therefore supplies all local simple
objects and their finite decompositions, as well as actual local kernels.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open CategoryTheory.BraidedCategory
open scoped MonObj BigOperators
universe v u w
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasFiniteBiproducts C] {A : C} [MonObj A]

omit [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasFiniteBiproducts C] in
/-- Locality descends to actual module summands. -/
theorem IsLocalModule.of_retract {M N : Mod_ C A} (r : Retract M N)
    (hN : IsLocalModule N) : IsLocalModule M :=
  hN.of_mono r.i

omit [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasFiniteBiproducts C] in
/-- Any module morphism into a local module equalizes its source's two
braiding-induced actions. -/
@[reassoc]
theorem IsLocalModule.condition_map {M N : Mod_ C A} (f : M ⟶ N)
    (hN : IsLocalModule N) :
    RelativeTensor.rightAction M ≫ f.hom =
      ((β_ A M.X).inv ≫ γ[A,M.X]) ≫ f.hom := by
  have hf : γ[A,M.X] ≫ f.hom = (A ◁ f.hom) ≫ γ[A,N.X] :=
    IsMod_Hom.smul_hom (A := A) (f := f.hom)
  rw [RelativeTensor.rightAction_naturality, hN]
  simp only [Category.assoc]
  rw [braiding_inv_naturality_left_assoc, hf]

/-- Finite sums of actual local modules are local. The mapped biproduct
total identity detects the equality of the two actual action maps. -/
theorem IsLocalModule.biproduct {J : Type} [Fintype J] (P : J → Mod_ C A)
    (hP : ∀ j, IsLocalModule (P j)) : IsLocalModule (⨁ P) := by
  have ht : ∑ j, (biproduct.π P j).hom ≫ (biproduct.ι P j).hom = 𝟙 (⨁ P).X := by
    simpa only [Functor.map_sum, Functor.map_comp, Functor.map_id] using
      congrArg ((Mod_.forget (D := C) A).map) (biproduct.total (f := P))
  have hj (j : J) := (hP j).condition_map (biproduct.π P j)
  unfold IsLocalModule
  calc
    _ = RelativeTensor.rightAction (⨁ P) ≫
        (∑ j, (biproduct.π P j).hom ≫ (biproduct.ι P j).hom) := by rw [ht, Category.comp_id]
    _ = ((β_ A (⨁ P).X).inv ≫ γ[A,(⨁ P).X]) ≫
        (∑ j, (biproduct.π P j).hom ≫ (biproduct.ι P j).hom) := by
      simp only [Preadditive.comp_sum, ← Category.assoc, hj]
    _ = _ := by rw [ht, Category.comp_id]

instance localModule_isAdditive : IsAdditiveFullProperty (localModuleProperty (A := A)) where
  of_retract := IsLocalModule.of_retract
  biproduct := IsLocalModule.biproduct

section FiniteHom
variable [RightRigidCategory C] [HasCoequalizers C] [IsCommMonObj A]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]

/-- Local-module Hom spaces are the actual finite-dimensional module Hom spaces. -/
instance localModulesFiniteHom (X Y : LocalModules A) :
    FiniteDimensional ℂ (X ⟶ Y) :=
  inferInstanceAs (FiniteDimensional ℂ (X.obj ⟶ Y.obj))

end FiniteHom

namespace SeparableAlgebra
variable [HasKernels C] [RightRigidCategory C] [HasCoequalizers C] [IsCommMonObj A]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  (S : SeparableAlgebra A) {ι : Type w} [Fintype ι] (T : FiniteSemisimpleSkeleton C ι)

/-- The finite set of actual simple module classes satisfying locality. -/
def LocalSimpleIndex := {i : S.SimpleIndex T // IsLocalModule ((S.skeleton T).simpleObject i)}

instance localSimpleIndex_fintype : Fintype (S.LocalSimpleIndex T) := by
  unfold LocalSimpleIndex
  infer_instance

/-- The local full subcategory inherits actual kernels from the constructed
module kernels and semisimple splittings. -/
def localHasKernels : HasKernels (LocalModules A) :=
  (S.skeleton T).fullSubcategoryHasKernels (localModuleProperty (A := A))

/-- The actual finite semisimple skeleton of local modules. -/
def localSkeleton : FiniteSemisimpleSkeleton (LocalModules A) (S.LocalSimpleIndex T) :=
  (S.skeleton T).fullSubcategorySkeleton (localModuleProperty (A := A))

end SeparableAlgebra
end Paper18.Category
