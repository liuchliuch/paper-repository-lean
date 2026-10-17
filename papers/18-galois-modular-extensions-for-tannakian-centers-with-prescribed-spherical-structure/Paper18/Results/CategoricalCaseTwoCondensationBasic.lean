import Paper18.Category.DiagonalCondensationEmbeddingLocal
import Paper18.Category.ModuleBalancingLocalFunctor
import Paper18.Category.LocalModulesCondensation
import Paper18.Category.NondegenerateExtension

/-! # Actual spherical local free embeddings for case-2 condensation -/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped MonObj
universe v u v' u' w
namespace Paper18.Category.CaseTwoCondensation
variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℂ B]
  [MonoidalCategory B] [BraidedCategory B] [RightRigidCategory B]
  {W : Type u'} [Category.{v'} W] [Preadditive W] [Linear ℂ W]
  [MonoidalCategory W] [BraidedCategory W] [RightRigidCategory W]
  [MonoidalPreadditive W] [MonoidalLinear ℂ W]
  [HasKernels W] [HasFiniteBiproducts W] [HasCoequalizers W]
  [∀ X Y : W, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ W)]
  {A : W} [MonObj A] [IsCommMonObj A]
  [RightRigidCategory (Mod_ W A)] [RightRigidCategory (LocalModules A)]
  (JB : PivotalStructure B) (JW : PivotalStructure W)
  (hA : (JW.twistIso A).hom = 𝟙 A)
  (H : B ⥤ W) [H.Braided] [H.Additive] [H.Linear ℂ]
  (hH : ∀ X, Centralizes A (H.obj X))

/-- Actual pivotal compatibility descends through the actual free local
functor. This is proved from actual twist preservation on free generators;
the algebra need not be transparent. -/
theorem localFreeAlong_preservesPivotal (hP : PreservesPivotal H JB JW) :
    PreservesPivotal (DiagonalCondensation.localFreeAlong H hH) JB
      (ModuleBalancing.localPivotal JW hA) := by
  apply preservesPivotal_of_twist
  intro X
  change InternalModule.freeMap (H.map (JB.twistIso X).hom) =
    (ModuleBalancing.localPivotal JW hA).twistNatIso.hom.app
      ((DiagonalCondensation.localFreeAlong H hH).obj X)
  rw [hP.twist, ModuleBalancing.localPivotal_twist]
  exact (ModuleBalancing.free_twist JW hA (H.obj X) (hH X)).symm

/-- A proved actual free-module Hom comparison supplies the full and
faithful structure on the actual spherical local embedding. -/
def localSphericalEmbedding (hP : PreservesPivotal H JB JW)
    (hFF : (H ⋙ InternalModule.freeFunctor (A := A)).FullyFaithful) :
    BraidedSphericalEmbedding JB (ModuleBalancing.localPivotal JW hA) := by
  let ff := DiagonalCondensation.localFreeAlongFullyFaithful H hH hFF
  letI := ff.full
  letI := ff.faithful
  exact
    { functor := DiagonalCondensation.localFreeAlong H hH
      pivotal := localFreeAlong_preservesPivotal JB JW hA H hH hP }

end Paper18.Category.CaseTwoCondensation
