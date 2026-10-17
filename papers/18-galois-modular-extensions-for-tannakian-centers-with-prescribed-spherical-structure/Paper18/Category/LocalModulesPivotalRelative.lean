import Paper18.Category.LocalModulesPivotalDual

/-! # Perfect ambient evaluation for the chosen actual local-module dual -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj
universe v u
namespace Paper18.Category.ModuleBalancing.MultiplicationPairing
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C] [HasCoequalizers C]
  {A : C} [MonObj A] [IsCommMonObj A]
  [RightRigidCategory (Mod_ C A)] [RightRigidCategory (LocalModules A)]
  (P : MultiplicationPairing A)

def localAmbientCap (M : LocalModules A) :
    (dual (LocalModules A) M).obj.X ⊗ M.obj.X ⟶ 𝟙_ C :=
  RelativeTensor.π (dual (LocalModules A) M).obj M.obj ≫
    (ε_ M (dual (LocalModules A) M)).hom ≫ P.counit

/-- Canonical comparison with the module dual, followed by the derived
Frobenius ambient dual comparison. -/
def localAmbientDualIso (M : LocalModules A) :
    (dual (LocalModules A) M).obj.X ≅ dual C M.obj.X :=
  (Mod_.forget (D := C) A).mapIso
    (dualComparison (localModuleProperty (A := A)).ι M) ≪≫ P.ambientDualIso M.obj

lemma localAmbientDualIso_evaluation (M : LocalModules A) :
    (P.localAmbientDualIso M).hom ▷ M.obj.X ≫ ε_ M.obj.X (dual C M.obj.X) =
      P.localAmbientCap M := by
  have hc := dualComparison_evaluation (localModuleProperty (A := A)).ι M
  change (dualComparison (localModuleProperty (A := A)).ι M).hom ▷ M.obj ≫
      ε_ M.obj (dual (Mod_ C A) M.obj) =
    𝟙 _ ≫ ε_ M (dual (LocalModules A) M) ≫ 𝟙 _ at hc
  simp only [id_comp, comp_id] at hc
  have hh := congrArg (fun t => RelativeTensor.π (dual (LocalModules A) M).obj M.obj ≫
    t.hom ≫ P.counit) hc
  simp only [Mod_.comp_hom', assoc] at hh
  rw [RelativeTensor.π_whiskerRight_assoc] at hh
  change ((dualComparison (localModuleProperty (A := A)).ι M).hom.hom ≫
      (P.ambientDualIso M.obj).hom) ▷ M.obj.X ≫ ε_ M.obj.X (dual C M.obj.X) = _
  rw [comp_whiskerRight, assoc, P.ambientDualIso_evaluation]
  exact hh

/-- The actual local evaluation, composed with the multiplication counit,
detects actual ambient maps into the actual chosen local dual. -/
lemma localAmbientCap_ext (M : LocalModules A) {X : C}
    (f g : X ⟶ (dual (LocalModules A) M).obj.X)
    (h : f ▷ M.obj.X ≫ P.localAmbientCap M = g ▷ M.obj.X ≫ P.localAmbientCap M) :
    f = g := by
  apply (cancel_mono (P.localAmbientDualIso M).hom).mp
  apply pairing_hom_ext
    (inferInstanceAs (ExactPairing M.obj.X (dual C M.obj.X)))
  simpa only [comp_whiskerRight, assoc, P.localAmbientDualIso_evaluation] using h

end Paper18.Category.ModuleBalancing.MultiplicationPairing
