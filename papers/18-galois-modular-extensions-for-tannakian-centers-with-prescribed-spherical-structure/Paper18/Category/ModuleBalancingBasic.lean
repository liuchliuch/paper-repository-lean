import Paper18.Category.LocalModulesCoherence
import Paper18.Category.PivotalBalancing
import Paper18.Category.ModuleTensorCharacters

/-!
# Descent of the actual ambient twist to local modules

If the ambient twist fixes the algebra, the twist of a local module is an
actual module morphism. The proof uses actual monodromy locality of the action.
For a transparent algebra this applies to every module.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj
universe v u
namespace Paper18.Category.ModuleBalancing
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C]
  (J : PivotalStructure C) {A : C} [MonObj A]
  (hA : (J.twistIso A).hom = 𝟙 A)

include hA in
/-- Locality is exactly what makes the ambient twist commute with the
actual module action when the twist of the algebra is the identity. -/
lemma action_compatible (M : Mod_ C A) (hM : IsLocalModule M) :
    γ[A,M.X] ≫ (J.twistIso M.X).hom =
      (A ◁ (J.twistIso M.X).hom) ≫ γ[A,M.X] := by
  have hn := J.twistNatIso.hom.naturality γ[A,M.X]
  change γ[A,M.X] ≫ (J.twistIso M.X).hom =
    (J.twistIso (A ⊗ M.X)).hom ≫ γ[A,M.X] at hn
  rw [J.twist_tensor, hA, id_tensorHom] at hn
  have hc := doubleBraiding_naturality (𝟙 A) (J.twistIso M.X).hom
  simp only [id_tensorHom] at hc
  rw [← hc, assoc, (isLocalModule_iff M).mp hM] at hn
  exact hn

def moduleMap (M : Mod_ C A) (hM : IsLocalModule M) : M ⟶ M :=
  Mod_.Hom.mk' (J.twistIso M.X).hom (action_compatible J hA M hM)

def moduleIso (M : Mod_ C A) (hM : IsLocalModule M) : M ≅ M where
  hom := moduleMap J hA M hM
  inv := Mod_.Hom.mk' (J.twistIso M.X).inv (by
    apply (cancel_mono (J.twistIso M.X).hom).mp
    simp only [assoc, Iso.inv_hom_id, comp_id]
    rw [action_compatible J hA M hM]
    change γ[A,M.X] = (A ◁ (J.twistIso M.X).inv) ≫
      (A ◁ (J.twistIso M.X).hom) ≫ γ[A,M.X]
    rw [← whiskerLeft_comp_assoc, Iso.inv_hom_id, whiskerLeft_id, id_comp])
  hom_inv_id := by apply Mod_.Hom.ext; exact (J.twistIso M.X).hom_inv_id
  inv_hom_id := by apply Mod_.Hom.ext; exact (J.twistIso M.X).inv_hom_id

section Tensor
variable [HasCoequalizers C] [IsCommMonObj A]

/-- The actual natural twist of local modules, with ambient components. -/
def localTwist : 𝟭 (LocalModules A) ≅ 𝟭 (LocalModules A) :=
  NatIso.ofComponents
    (fun M => (localModuleProperty (A := A)).isoMk (moduleIso J hA M.obj M.property))
    (fun f => by apply Mod_.Hom.ext; exact J.twistNatIso.hom.naturality f.hom)

@[simp] lemma localTwist_hom (M : LocalModules A) :
    ((localTwist J hA).hom.app M).hom = (J.twistIso M.obj.X).hom := rfl

@[simp] lemma localTwist_inv (M : LocalModules A) :
    ((localTwist J hA).inv.app M).hom = (J.twistIso M.obj.X).inv := rfl

/-- The actual natural twist of all modules over a transparent algebra. -/
def moduleTwist (htransparent : A ∈ mugerCenter (C := C)) :
    𝟭 (Mod_ C A) ≅ 𝟭 (Mod_ C A) :=
  NatIso.ofComponents
    (fun M => moduleIso J hA M (localModule_of_transparent htransparent M))
    (fun f => by apply Mod_.Hom.ext; exact J.twistNatIso.hom.naturality f.hom)

@[simp] lemma moduleTwist_hom (htransparent : A ∈ mugerCenter (C := C))
    (M : Mod_ C A) :
    ((moduleTwist J hA htransparent).hom.app M).hom = (J.twistIso M.X).hom := rfl

@[simp] lemma moduleTwist_inv (htransparent : A ∈ mugerCenter (C := C))
    (M : Mod_ C A) :
    ((moduleTwist J hA htransparent).inv.app M).hom = (J.twistIso M.X).inv := rfl

end Tensor
end Paper18.Category.ModuleBalancing
