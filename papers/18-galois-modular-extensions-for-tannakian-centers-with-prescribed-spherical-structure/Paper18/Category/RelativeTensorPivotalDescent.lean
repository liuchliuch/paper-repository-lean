import Paper18.Category.RelativeTensorPivotalFree
import Paper18.Category.SeparableModulesSemisimple

/-! # Actual pivotal maps on separable modules from their free retracts -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped MonObj
universe v u
namespace Paper18.Category.ModuleBalancing.MultiplicationPairing
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C] [HasCoequalizers C]
  {A : C} [MonObj A] [IsCommMonObj A] (P : MultiplicationPairing A)
  [RightRigidCategory (Mod_ C A)] (S : SeparableAlgebra A)
  (J : PivotalStructure C) (hA : (J.twistIso A).hom = 𝟙 A)

/-- The actual free pivotal map transported to an actual separable retract. -/
def pivotalComponentHom (M : Mod_ C A) : M ⟶ (doubleDualFunctor (Mod_ C A)).obj M :=
  (S.freeRetract M).i ≫
    (InternalModule.freeFunctor (A := A)).map (J.j.hom.app M.X) ≫
    (doubleDualComparison (InternalModule.freeFunctor (A := A)) M.X).hom ≫
    (doubleDualFunctor (Mod_ C A)).map (S.freeRetract M).r

include hA in
/-- The retract formula is exactly the canonical underlying pivotal map.
In particular it proves the latter's module linearity. -/
@[simp]
lemma pivotalComponentHom_hom (M : Mod_ C A) :
    (pivotalComponentHom S J M).hom = (P.pivotalUnderlyingIso J).hom.app M := by
  have hn := (P.pivotalUnderlyingIso J).hom.naturality (S.freeRetract M).r
  change (S.freeRetract M).r.hom ≫ (P.pivotalUnderlyingIso J).hom.app M =
    (P.pivotalUnderlyingIso J).hom.app (InternalModule.free A M.X) ≫
      ((doubleDualFunctor (Mod_ C A)).map (S.freeRetract M).r).hom at hn
  have hr := congrArg Mod_.Hom.hom (S.freeRetract M).retract
  calc
    _ = (S.freeRetract M).i.hom ≫
        ((InternalModule.freeFunctor (A := A)).map (J.j.hom.app M.X) ≫
          (doubleDualComparison (InternalModule.freeFunctor (A := A)) M.X).hom).hom ≫
        ((doubleDualFunctor (Mod_ C A)).map (S.freeRetract M).r).hom := by
      simp only [pivotalComponentHom, Mod_.comp_hom', assoc]
    _ = (S.freeRetract M).i.hom ≫
        (P.pivotalUnderlyingIso J).hom.app (InternalModule.free A M.X) ≫
        ((doubleDualFunctor (Mod_ C A)).map (S.freeRetract M).r).hom := by
      rw [P.free_pivotalUnderlying J hA]
    _ = _ := by
      rw [← hn, ← assoc]
      simpa only [Mod_.comp_hom', Mod_.id_hom', id_comp] using
        congrArg (fun f => f ≫ (P.pivotalUnderlyingIso J).hom.app M) hr

omit [RightRigidCategory C] [BraidedCategory C] [HasCoequalizers C]
  [IsCommMonObj A] [RightRigidCategory (Mod_ C A)] in
/-- The actual underlying inverse of an internal module isomorphism is
module linear, by the native inverse-linearity theorem. -/
private theorem moduleIsIsoOfUnderlying {M N : Mod_ C A} (f : M ⟶ N)
    [IsIso f.hom] : IsIso f := by
  letI : IsMod_Hom A (asIso f.hom).hom := f.isMod_Hom
  let g : N ⟶ M := ⟨(asIso f.hom).inv⟩
  refine ⟨⟨g, ?_, ?_⟩⟩
  · apply Mod_.Hom.ext
    exact IsIso.hom_inv_id f.hom
  · apply Mod_.Hom.ext
    exact IsIso.inv_hom_id f.hom

/-- The actual module pivotal component is an isomorphism because its
underlying morphism belongs to the canonical underlying natural iso. -/
def pivotalComponentIso (M : Mod_ C A) : M ≅ (doubleDualFunctor (Mod_ C A)).obj M := by
  letI : IsIso (pivotalComponentHom S J M).hom := by
    rw [P.pivotalComponentHom_hom S J hA]
    infer_instance
  letI := moduleIsIsoOfUnderlying (pivotalComponentHom S J M)
  exact asIso (pivotalComponentHom S J M)

/-- The descended actual pivotal components form a natural isomorphism.
Unit and tensor coherence are proved separately from free dominance. -/
def pivotalNatIso : 𝟭 (Mod_ C A) ≅ doubleDualFunctor (Mod_ C A) :=
  NatIso.ofComponents (P.pivotalComponentIso S J hA) (by
    intro M N f
    apply Mod_.Hom.ext
    simp only [Mod_.comp_hom']
    change f.hom ≫ (pivotalComponentHom S J N).hom =
      (pivotalComponentHom S J M).hom ≫ ((doubleDualFunctor (Mod_ C A)).map f).hom
    rw [P.pivotalComponentHom_hom S J hA, P.pivotalComponentHom_hom S J hA]
    exact (P.pivotalUnderlyingIso J).hom.naturality f)

@[simp]
lemma pivotalNatIso_free (X : C) :
    (P.pivotalNatIso S J hA).hom.app (InternalModule.free A X) =
      (InternalModule.freeFunctor (A := A)).map (J.j.hom.app X) ≫
        (doubleDualComparison (InternalModule.freeFunctor (A := A)) X).hom := by
  apply Mod_.Hom.ext
  change (pivotalComponentHom S J (InternalModule.free A X)).hom = _
  rw [P.pivotalComponentHom_hom S J hA]
  exact (P.free_pivotalUnderlying J hA X).symm

end Paper18.Category.ModuleBalancing.MultiplicationPairing
