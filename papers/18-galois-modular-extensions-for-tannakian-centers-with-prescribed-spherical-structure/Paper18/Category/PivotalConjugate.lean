import Paper18.Category.RadfordBraidedMonoidal
import Paper18.Category.RadfordBraidedTrace

/-!
# The conjugate of an actual pivotal structure

The canonical braided four-dual comparison and the double dual of the pivotal
identification give a second pivotal structure. Its right trace is the original
left trace, as an equality of actual endomorphisms of the tensor unit.
-/
noncomputable section
universe v u
namespace Paper18.Category
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Functor CategoryTheory.Functor.LaxMonoidal
attribute [local instance 2000] RightRigidCategory.rightDual

namespace PivotalStructure
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] (J : PivotalStructure C)

/-- Apply canonical double dualization to the components of the pivotal map. -/
def doubleDualPivotalNatIso : doubleDualFunctor C ≅
    doubleDualFunctor C ⋙ doubleDualFunctor C :=
  (Functor.leftUnitor (doubleDualFunctor C)).symm ≪≫
    isoWhiskerRight J.j (doubleDualFunctor C)

@[simp] lemma doubleDualPivotalNatIso_hom_app (X : C) :
    J.doubleDualPivotalNatIso.hom.app X =
      (doubleDualFunctor C).map (J.j.hom.app X) := by
  simp [doubleDualPivotalNatIso]

@[simp] lemma doubleDualPivotalNatIso_inv_app (X : C) :
    J.doubleDualPivotalNatIso.inv.app X =
      (doubleDualFunctor C).map (J.j.inv.app X) := by
  simp [doubleDualPivotalNatIso]

instance doubleDualPivotal_isMonoidal :
    NatTrans.IsMonoidal J.doubleDualPivotalNatIso.hom where
  unit := by
    rw [J.doubleDualPivotalNatIso_hom_app, J.unit, comp_ε,
      canonicalDoubleDual_unit]
  tensor X Y := by
    rw [J.doubleDualPivotalNatIso_hom_app, J.doubleDualPivotalNatIso_hom_app,
      J.doubleDualPivotalNatIso_hom_app, J.tensor, Functor.map_comp, comp_μ]
    simp only [← canonicalDoubleDual_tensor]
    exact (μ_natural_assoc (doubleDualFunctor C) (J.j.hom.app X) (J.j.hom.app Y) _).symm

variable [BraidedCategory C]

/-- Radford conjugation of the pivotal identification. -/
def conjugateNatIso : 𝟭 C ≅ doubleDualFunctor C :=
  braidedFourDualNatIso ≪≫ J.doubleDualPivotalNatIso.symm

instance conjugateNatIso_isMonoidal : NatTrans.IsMonoidal J.conjugateNatIso.hom := by
  dsimp only [conjugateNatIso, Iso.trans_hom, Iso.symm_hom]
  infer_instance

/-- The conjugate pivotal structure, whose coherence follows from the actual
monoidality of Radford's comparison and of double dualization. -/
def conjugate : PivotalStructure C where
  j := J.conjugateNatIso
  unit := by
    simpa only [id_ε, id_comp, canonicalDoubleDual_unit] using
      (NatTrans.IsMonoidal.unit (τ := J.conjugateNatIso.hom))
  tensor X Y := by
    simpa only [id_μ, id_comp, canonicalDoubleDual_tensor] using
      (NatTrans.IsMonoidal.tensor (τ := J.conjugateNatIso.hom) X Y)

@[simp] lemma conjugate_hom_app (X : C) :
    J.conjugate.j.hom.app X = (braidedFourDualIso X).hom ≫
      (doubleDualFunctor C).map (J.j.inv.app X) := by
  change (braidedFourDualNatIso (C := C)).hom.app X ≫
    J.doubleDualPivotalNatIso.inv.app X = _
  rw [J.doubleDualPivotalNatIso_inv_app]
  rfl

/-- Conjugation exchanges the actual left and right cap/cup traces. -/
theorem conjugate_rightTrace {X : C} (f : X ⟶ X) :
    J.conjugate.rightTrace f = J.leftTrace f := by
  simpa only [rightTrace, leftTrace, leftEvaluation, leftCoevaluation,
    J.conjugate_hom_app, Category.assoc] using
      (braidedFourDual_trace X (J.j.app X) f).symm

lemma conjugate_rightDimension (X : C) :
    J.conjugate.rightDimension X = J.leftDimension X :=
  J.conjugate_rightTrace (𝟙 X)

end PivotalStructure
end Paper18.Category
