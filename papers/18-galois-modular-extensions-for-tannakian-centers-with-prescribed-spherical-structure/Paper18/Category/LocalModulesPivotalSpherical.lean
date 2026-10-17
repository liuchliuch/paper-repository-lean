import Paper18.Category.LocalModulesPivotalRibbon
import Paper18.Category.LocalModulesPivotalRelative
import Paper18.Category.LocalModulesPivotalTransparent

/-! # Sphericality of actual local modules from a perfect multiplication pairing -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj
universe v u w
namespace Paper18.Category.ModuleBalancing
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C] [HasCoequalizers C]
  {A : C} [MonObj A] [IsCommMonObj A]
  [RightRigidCategory (Mod_ C A)] [RightRigidCategory (LocalModules A)]
  (P : MultiplicationPairing A) (J : PivotalStructure C)
  (hA : (J.twistIso A).hom = 𝟙 A)
include P

/-- Ambient ribbon compatibility applies to the actual perfect pairing
obtained from the relative evaluation and the Frobenius counit. -/
lemma localAmbientCap_twist (hJ : J.TwistSelfDual) (M : LocalModules A) :
    (J.twistIso (dual (LocalModules A) M).obj.X).hom ▷ M.obj.X ≫ P.localAmbientCap M =
      (dual (LocalModules A) M).obj.X ◁ (J.twistIso M.obj.X).hom ≫ P.localAmbientCap M := by
  let q := P.localAmbientDualIso M
  have hn := J.twist_naturality q.hom
  calc
    _ = ((J.twistIso (dual (LocalModules A) M).obj.X).hom ≫ q.hom) ▷ M.obj.X ≫
        ε_ M.obj.X (dual C M.obj.X) := by
      rw [comp_whiskerRight, assoc, P.localAmbientDualIso_evaluation]
    _ = (q.hom ≫ dualMap C (J.twistIso M.obj.X).hom) ▷ M.obj.X ≫
        ε_ M.obj.X (dual C M.obj.X) := by rw [← hn, hJ M.obj.X]
    _ = _ := by
      rw [comp_whiskerRight, assoc,
        rightAdjointMate_comp_evaluation (J.twistIso M.obj.X).hom,
        ← whisker_exchange_assoc, P.localAmbientDualIso_evaluation]

/-- The actual descended local twist is self-dual. Actual relative mates
are detected by the perfect ambient pairing, rather than assumed compatible. -/
theorem localPivotal_twistSelfDual (hJ : J.TwistSelfDual) :
    (localPivotal J hA).TwistSelfDual := by
  intro M
  have hθ (N : LocalModules A) :
      ((localPivotal J hA).twistIso N).hom.hom = (J.twistIso N.obj.X).hom := by
    change (((localPivotal J hA).twistNatIso).hom.app N).hom = _
    rw [localPivotal_twist]
    rfl
  have hc := rightAdjointMate_comp_evaluation ((localPivotal J hA).twistIso M).hom
  have hh := congrArg (fun t => RelativeTensor.π (dual (LocalModules A) M).obj M.obj ≫
    t.hom ≫ P.counit) hc
  change RelativeTensor.π (dual (LocalModules A) M).obj M.obj ≫
      ((dualMap (LocalModules A) ((localPivotal J hA).twistIso M).hom ▷ M).hom ≫
        (ε_ M (dual (LocalModules A) M)).hom) ≫ P.counit =
    RelativeTensor.π (dual (LocalModules A) M).obj M.obj ≫
      (((dual (LocalModules A) M) ◁ ((localPivotal J hA).twistIso M).hom).hom ≫
        (ε_ M (dual (LocalModules A) M)).hom) ≫ P.counit at hh
  simp only [assoc] at hh
  have hwR := RelativeTensor.π_whiskerRight
    (show (dual (LocalModules A) M).obj ⟶ (dual (LocalModules A) M).obj from
      dualMap (LocalModules A) ((localPivotal J hA).twistIso M).hom) M.obj
  have hwL := RelativeTensor.π_whiskerLeft (dual (LocalModules A) M).obj
    (show M.obj ⟶ M.obj from ((localPivotal J hA).twistIso M).hom)
  have ir := Functor.Monoidal.map_whiskerRight (localModuleProperty (A := A)).ι
    (dualMap (LocalModules A) ((localPivotal J hA).twistIso M).hom) M
  have il := Functor.Monoidal.map_whiskerLeft (localModuleProperty (A := A)).ι
    (dual (LocalModules A) M) ((localPivotal J hA).twistIso M).hom
  simp only [ObjectProperty.ι_δ, ObjectProperty.ι_μ, id_comp, comp_id] at ir il
  have irh := congrArg Mod_.Hom.hom ir
  have ilh := congrArg Mod_.Hom.hom il
  dsimp only [ObjectProperty.ι_map, ObjectProperty.ι_obj] at irh ilh
  rw [irh, ilh, reassoc_of% hwR, reassoc_of% hwL] at hh
  change (dualMap (LocalModules A) ((localPivotal J hA).twistIso M).hom).hom ▷ M.obj.X ≫
      P.localAmbientCap M = (dual (LocalModules A) M).obj.X ◁
        ((localPivotal J hA).twistIso M).hom.hom ≫ P.localAmbientCap M at hh
  rw [hθ] at hh
  apply Mod_.Hom.ext
  apply P.localAmbientCap_ext M
  rw [hθ]
  exact (localAmbientCap_twist P J hJ M).trans hh.symm

section Fusion
variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  (R : SeparableAlgebra A) {ι : Type w} [Fintype ι] (T : FiniteSemisimpleSkeleton C ι)
include R T

/-- A connected separable algebra with an actual nondegenerate
multiplication pairing and trivial ambient twist has an actual spherical
local-module pivotal structure, descended from the ambient spherical one. -/
theorem localPivotal_spherical_of_multiplicationPairing
    (hconnected : Module.finrank ℂ (𝟙_ C ⟶ A) = 1) (hJ : J.Spherical) :
    (localPivotal J hA).Spherical := by
  letI := R.localHasKernels T
  letI := R.localSimpleUnit T hconnected
  exact (localPivotal J hA).spherical_of_twistSelfDual (R.localSkeleton T)
    (localPivotal_twistSelfDual P J hA (J.twistSelfDual_of_spherical T hJ))

end Fusion
end Paper18.Category.ModuleBalancing
