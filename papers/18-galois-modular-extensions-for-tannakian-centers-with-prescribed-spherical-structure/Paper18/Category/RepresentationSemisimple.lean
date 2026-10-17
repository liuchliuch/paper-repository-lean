import Paper18.Category.RepresentationBasic
import Mathlib.LinearAlgebra.DFinsupp

/-!
# Genuine Maschke decompositions

For a finite-dimensional representation of a finite group the associated
complex group-algebra module is semisimple, and has a finite direct sum
decomposition into actual simple submodules. These results use Maschke's
averaging proof from mathlib.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators
namespace Paper18.Category.Representation
variable {G : Type} [Group G] [Fintype G]

instance finiteDimensional_asModule (V : FDRep ℂ G) :
    FiniteDimensional ℂ (_root_.Representation.asModule V.ρ) :=
  FiniteDimensional.of_injective (_root_.Representation.asModuleEquiv V.ρ).toLinearMap (_root_.Representation.asModuleEquiv V.ρ).injective

instance finite_asGroupAlgebraModule (V : FDRep ℂ G) :
    Module.Finite (MonoidAlgebra ℂ G) (_root_.Representation.asModule V.ρ) :=
  Module.Finite.of_restrictScalars_finite ℂ (MonoidAlgebra ℂ G) (_root_.Representation.asModule V.ρ)

/-- The underlying group-algebra module of every actual finite representation
is semisimple. -/
theorem isSemisimple_asModule (V : FDRep ℂ G) :
    IsSemisimpleModule (MonoidAlgebra ℂ G) (_root_.Representation.asModule V.ρ) := by infer_instance

/-- Maschke's finite direct sum theorem, with genuine simple invariant
subspaces and an actual group-algebra linear isomorphism. -/
theorem exists_finite_simple_decomposition (V : FDRep ℂ G) :
    ∃ (n : ℕ) (S : Fin n → Submodule (MonoidAlgebra ℂ G) (_root_.Representation.asModule V.ρ))
      (_ : (_root_.Representation.asModule V.ρ) ≃ₗ[MonoidAlgebra ℂ G] Π₀ i : Fin n, S i),
      ∀ i, IsSimpleModule (MonoidAlgebra ℂ G) (S i) :=
  IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp (MonoidAlgebra ℂ G) (_root_.Representation.asModule V.ρ)

/-- Equivalently the decomposition is a finite product of simple modules;
for finitely many summands the sum-to-product map is an actual linear
isomorphism. -/
theorem exists_finite_simple_product_decomposition (V : FDRep ℂ G) :
    ∃ (n : ℕ) (S : Fin n → Submodule (MonoidAlgebra ℂ G) (_root_.Representation.asModule V.ρ))
      (_ : (_root_.Representation.asModule V.ρ) ≃ₗ[MonoidAlgebra ℂ G] ∀ i : Fin n, S i),
      ∀ i, IsSimpleModule (MonoidAlgebra ℂ G) (S i) := by
  obtain ⟨n, S, e, hS⟩ := exists_finite_simple_decomposition V
  exact ⟨n, S, e.trans DFinsupp.linearEquivFunOnFintype, hS⟩

end Paper18.Category.Representation

namespace Paper18.Category.Representation
variable {G : Type} [Group G]
variable (M : Type) [AddCommGroup M] [Module ℂ M] [Module (MonoidAlgebra ℂ G) M]
  [IsScalarTower ℂ (MonoidAlgebra ℂ G) M] [FiniteDimensional ℂ M]

/-- Convert an actual finite-dimensional group-algebra module to an actual
finite representation, using its existing complex vector-space structure. -/
def ofModule : FDRep ℂ G := FDRep.of (_root_.Representation.ofModule' M)

/-- The group-algebra module recovered from this representation is the
original module, by the group-algebra universal property. -/
def toGroupAlgebra_ofModuleIso :
    (toGroupAlgebra (G := G)).obj (ofModule (G := G) M) ≅ ModuleCat.of (MonoidAlgebra ℂ G) M := by
  apply LinearEquiv.toModuleIso
  refine { (_root_.Representation.asModuleEquiv (_root_.Representation.ofModule' M)).toAddEquiv with
    map_smul' := ?_ }
  intro r x
  simp [_root_.Representation.asAlgebraHom, _root_.Representation.ofModule']

/-- A simple finite-dimensional group-algebra module gives a simple actual
representation. -/
theorem simple_ofModule [IsSimpleModule (MonoidAlgebra ℂ G) M] : Simple (ofModule (G := G) M) := by
  haveI : Simple ((toGroupAlgebra (G := G)).obj (ofModule (G := G) M)) :=
    Simple.of_iso (toGroupAlgebra_ofModuleIso (G := G) M)
  exact simple_of_groupAlgebra_simple _

end Paper18.Category.Representation

namespace Paper18.Category.Representation
variable {G : Type} [Group G] [Fintype G]

instance finiteDimensional_groupAlgebraSubmodule (V : FDRep ℂ G)
    (S : Submodule (MonoidAlgebra ℂ G) (_root_.Representation.asModule V.ρ)) :
    FiniteDimensional ℂ S :=
  FiniteDimensional.of_injective (S.subtype.restrictScalars ℂ) S.injective_subtype

/-- Complete semisimplicity in the actual representation category: every
object is isomorphic to a finite categorical biproduct of actual simple
representations. -/
theorem exists_simple_biproduct (V : FDRep ℂ G) :
    ∃ (n : ℕ) (W : Fin n → FDRep ℂ G), (∀ i, Simple (W i)) ∧ Nonempty (V ≅ ⨁ W) := by
  obtain ⟨n, S, e, hS⟩ := exists_finite_simple_product_decomposition V
  let W : Fin n → FDRep ℂ G := fun i => ofModule (G := G) (S i)
  have hs : ∀ i, Simple (W i) := fun i => by
    letI := hS i
    exact simple_ofModule (G := G) (S i)
  let F := toGroupAlgebra (G := G)
  let e₁ : F.obj V ≅ ModuleCat.of (MonoidAlgebra ℂ G) (∀ i, S i) :=
    LinearEquiv.toModuleIso e
  let e₂ : (⨁ fun i => ModuleCat.of (MonoidAlgebra ℂ G) (S i)) ≅ ⨁ F.obj ∘ W :=
    biproduct.mapIso (fun i => (toGroupAlgebra_ofModuleIso (G := G) (S i)).symm)
  exact ⟨n, W, hs, ⟨F.preimageIso
    (e₁ ≪≫ (ModuleCat.biproductIsoPi (fun i => ModuleCat.of (MonoidAlgebra ℂ G) (S i))).symm ≪≫ e₂ ≪≫ (F.mapBiproduct W).symm)⟩⟩

end Paper18.Category.Representation
