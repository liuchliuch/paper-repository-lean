import Paper18.Category.RelativeTensorPivotalDescent
import Paper18.Category.RelativeTensorPivotalDominant
import Paper18.Category.PivotalFunctorTensor

/-! # Actual pivotal structures on separable Frobenius modules -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
open Functor.LaxMonoidal
open scoped MonObj
universe v u
namespace Paper18.Category.ModuleBalancing.MultiplicationPairing
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C] [HasCoequalizers C]
  {A : C} [MonObj A] [IsCommMonObj A] (P : MultiplicationPairing A)
  [RightRigidCategory (Mod_ C A)] (S : SeparableAlgebra A)
  (J : PivotalStructure C) (hA : (J.twistIso A).hom = 𝟙 A)

/-- The actual descended pivotal maps satisfy monoidal coherence after
precomposition with the actual strong free functor. -/
theorem pivotalNatIsoFreeIsMonoidal :
    NatTrans.IsMonoidal (Functor.whiskerLeft (InternalModule.freeFunctor (A := A))
      (P.pivotalNatIso S J hA).hom) := by
  let F := InternalModule.freeFunctor (A := A)
  let τ := (P.pivotalNatIso S J hA).hom
  have heq (X : C) : τ.app (F.obj X) =
      F.map (J.j.hom.app X) ≫ (doubleDualComparison F X).hom :=
    P.pivotalNatIso_free S J hA X
  refine ⟨?_, ?_⟩
  · change (𝟙 _ ≫ ε F) ≫ τ.app (F.obj (𝟙_ C)) =
      ε (doubleDualFunctor (Mod_ C A)) ≫ (doubleDualFunctor (Mod_ C A)).map (ε F)
    rw [id_comp, heq, J.unit]
    simpa only [comp_ε, canonicalDoubleDual_unit, assoc] using
      canonicalDoubleDualComparison_unit F
  · intro X Y
    change (𝟙 _ ≫ Functor.LaxMonoidal.μ F X Y) ≫ τ.app (F.obj (X ⊗ Y)) =
      (τ.app (F.obj X) ⊗ₘ τ.app (F.obj Y)) ≫
        Functor.LaxMonoidal.μ (doubleDualFunctor (Mod_ C A)) (F.obj X) (F.obj Y) ≫
        (doubleDualFunctor (Mod_ C A)).map (Functor.LaxMonoidal.μ F X Y)
    rw [id_comp, heq, heq, heq, J.tensor, F.map_comp, assoc,
      ← Functor.LaxMonoidal.μ_natural_assoc]
    have h := canonicalDoubleDualComparison_tensor F X Y
    simp only [comp_μ, canonicalDoubleDual_tensor, assoc] at h
    rw [h, tensorHom_comp_tensorHom_assoc, canonicalDoubleDual_tensor]

/-- The canonical natural module maps are actually monoidal, detected on
free objects and then transported through their actual separable retracts. -/
theorem pivotalNatIsoIsMonoidal : NatTrans.IsMonoidal (P.pivotalNatIso S J hA).hom := by
  letI := P.pivotalNatIsoFreeIsMonoidal S J hA
  exact RelativeTensor.isMonoidal_of_retract_dominant
    (InternalModule.freeFunctor (A := A)) (doubleDualFunctor (Mod_ C A))
    (P.pivotalNatIso S J hA).hom S.free_retract_dominant

/-- The actual pivotal structure on the full module category, derived from
the ambient pivotal structure, actual separability, symmetric multiplication
pairing, and trivial algebra twist. -/
def modulePivotal : PivotalStructure (Mod_ C A) := by
  letI := P.pivotalNatIsoIsMonoidal S J hA
  refine ⟨P.pivotalNatIso S J hA, ?_, ?_⟩
  · simpa only [canonicalDoubleDual_unit, Functor.LaxMonoidal.ε,
      id_comp] using NatTrans.IsMonoidal.unit (τ := (P.pivotalNatIso S J hA).hom)
  · intro M N
    have h := NatTrans.IsMonoidal.tensor (τ := (P.pivotalNatIso S J hA).hom) M N
    change 𝟙 _ ≫ _ = _ at h
    simpa only [id_comp, canonicalDoubleDual_tensor] using h

/-- The actual strong free functor preserves the constructed pivotal
structure through its canonical double-dual comparison. -/
theorem freePreservesPivotal :
    PreservesPivotal (InternalModule.freeFunctor (A := A)) J (P.modulePivotal S J hA) :=
  fun X => (P.pivotalNatIso_free S J hA X).symm

end Paper18.Category.ModuleBalancing.MultiplicationPairing
