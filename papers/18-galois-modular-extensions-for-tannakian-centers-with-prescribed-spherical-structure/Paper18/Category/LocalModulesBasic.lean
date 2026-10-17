import Paper18.Category.RelativeTensorLinear
import Paper18.Category.Braided

/-!
# Actual local modules for commutative internal algebras

Locality says that the two right actions induced by the braiding agree.
Equivalently, monodromy acts trivially before the actual module action.
The actual balancing relation proves closure under relative tensor.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open CategoryTheory.BraidedCategory
open scoped MonObj
universe v u
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  {A : C} [MonObj A]

/-- An actual local module: its two braiding-induced right actions agree. -/
def IsLocalModule (M : Mod_ C A) : Prop :=
  RelativeTensor.rightAction M = (β_ A M.X).inv ≫ γ[A,M.X]

/-- The usual monodromy-invariance definition of locality. -/
theorem isLocalModule_iff (M : Mod_ C A) : IsLocalModule M ↔
    (doubleBraiding A M.X).hom ≫ γ[A,M.X] = γ[A,M.X] := by
  change (β_ M.X A).hom ≫ γ[A,M.X] = (β_ A M.X).inv ≫ γ[A,M.X] ↔
    ((β_ A M.X).hom ≫ (β_ M.X A).hom) ≫ γ[A,M.X] = γ[A,M.X]
  constructor
  · intro h
    rw [Category.assoc, h, Iso.hom_inv_id_assoc]
  · intro h
    apply (cancel_epi (β_ A M.X).hom).mp
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h

/-- Every module over an actual transparent algebra is local. -/
theorem localModule_of_transparent (hA : A ∈ mugerCenter (C := C)) (M : Mod_ C A) :
    IsLocalModule M := by
  rw [isLocalModule_iff]
  rw [hA M.X (Set.mem_univ _), Category.id_comp]

/-- Locality descends to actual module subobjects. -/
theorem IsLocalModule.of_mono {M N : Mod_ C A} (f : M ⟶ N) [Mono f]
    (hN : IsLocalModule N) : IsLocalModule M := by
  letI : Mono f.hom := (Mod_.forget (D := C) A).map_mono f
  have hf : γ[A,M.X] ≫ f.hom = (A ◁ f.hom) ≫ γ[A,N.X] :=
    IsMod_Hom.smul_hom (A := A) (f := f.hom)
  unfold IsLocalModule at hN ⊢
  apply (cancel_mono f.hom).mp
  rw [RelativeTensor.rightAction_naturality, hN]
  simp only [Category.assoc]
  rw [braiding_inv_naturality_left_assoc, hf]

/-- Locality regarded as a property of actual module objects. -/
def localModuleProperty : ObjectProperty (Mod_ C A) := IsLocalModule

section Tensor
variable [RightRigidCategory C] [HasCoequalizers C] [IsCommMonObj A]

/-- Locality is closed under the actual relative tensor product. This is
canonical-bimodule tensor closure for both the braiding and its reverse. -/
theorem IsLocalModule.tensor {M N : Mod_ C A} (hM : IsLocalModule M) (hN : IsLocalModule N) :
    IsLocalModule (M ⊗ N) := by
  let P := (RelativeTensor.toBimodObj M).tensorBimod (RelativeTensor.toBimodObj N)
  have hf : P.actRight = (β_ P.X A).hom ≫ P.actLeft :=
    RelativeTensor.canonical_tensor (RelativeTensor.toBimodObj M)
      (RelativeTensor.toBimodObj N) rfl rfl
  have hr : P.actRight = (β_ A P.X).inv ≫ P.actLeft := by
    exact @RelativeTensor.canonical_tensor C _ _ (reverseBraiding C) _ _ A _
      (RelativeTensor.toBimodObj M) (RelativeTensor.toBimodObj N) hM hN
  change (β_ P.X A).hom ≫ P.actLeft = (β_ A P.X).inv ≫ P.actLeft
  exact hf.symm.trans hr

instance localModule_isMonoidal : (localModuleProperty (A := A)).IsMonoidal where
  prop_unit := by
    change (β_ A A).hom ≫ μ[A] = (β_ A A).inv ≫ μ[A]
    rw [IsCommMonObj.mul_comm, IsCommMonObj.mul_comm']
  prop_tensor _ _ hM hN := hM.tensor hN

/-- The actual local-module category inherits the actual relative-tensor
monoidal structure. -/
abbrev LocalModules (A : C) [MonObj A] := (localModuleProperty (A := A)).FullSubcategory

end Tensor
end Paper18.Category
