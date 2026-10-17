import Paper18.Category.ModularExtensionOfEmbedding
import Paper18.Category.DrinfeldCoendModulesInverseTransport
import Paper18.Category.PivotalPullbackMonoidal
import Paper18.Category.PivotalFunctorMonoidalInverse
import Paper18.Category.RelativeTensorCentralImage
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Monoidal.Braided.Transport
import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.Group.ULift
import Mathlib.Algebra.Module.ULift

/-! # Actual fusion-category universe enlargement

The lifted category is monoidally transported along the ordinary
object-and-Hom universe-lifting equivalence.  All structures below are
actual categorical structures; no numerical replacement is used.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u vR uR
namespace Paper18.Category.ModularExtensionUniverseLift
attribute [local instance] CategoryTheory.uliftCategory
variable (D : Type u) [Category.{v} D] [MonoidalCategory D]

abbrev Ambient := Monoidal.Transported (ULiftHomULiftCategory.equiv.{vR,uR,v,u} D)
abbrev equivalence : D ≌ Ambient.{v,u,vR,uR} D :=
  Monoidal.equivalenceTransported (ULiftHomULiftCategory.equiv.{vR,uR,v,u} D)

instance ambientPreadditive [Preadditive D] : Preadditive (Ambient.{v,u,vR,uR} D) where
  homGroup X Y := inferInstanceAs (AddCommGroup (ULift.{vR} (X.objDown.down ⟶ Y.objDown.down)))
  add_comp _ _ _ f g h := by apply ULift.ext; exact Preadditive.add_comp _ _ _ _ _ _
  comp_add _ _ _ f g h := by apply ULift.ext; exact Preadditive.comp_add _ _ _ _ _ _

instance ambientLinear [Preadditive D] [Linear ℂ D] : Linear ℂ (Ambient.{v,u,vR,uR} D) where
  homModule X Y := inferInstanceAs (Module ℂ (ULift.{vR} (X.objDown.down ⟶ Y.objDown.down)))
  smul_comp _ _ _ r f g := by apply ULift.ext; exact Linear.smul_comp _ _ _ _ _ _
  comp_smul _ _ _ f r g := by apply ULift.ext; exact Linear.comp_smul _ _ _ _ _ _

instance upAdditive [Preadditive D] : (equivalence.{v,u,vR,uR} D).functor.Additive where
  map_add := rfl
instance downAdditive [Preadditive D] : (equivalence.{v,u,vR,uR} D).inverse.Additive where
  map_add := rfl
instance upLinear [Preadditive D] [Linear ℂ D] :
    (equivalence.{v,u,vR,uR} D).functor.Linear ℂ where
  map_smul _ _ := rfl
instance downLinear [Preadditive D] [Linear ℂ D] :
    (equivalence.{v,u,vR,uR} D).inverse.Linear ℂ where
  map_smul _ _ := rfl

instance ambientMonoidalPreadditive [Preadditive D] [MonoidalPreadditive D] :
    MonoidalPreadditive (Ambient.{v,u,vR,uR} D) :=
  monoidalPreadditive_of_faithful (equivalence D).inverse

instance ambientMonoidalLinear [Preadditive D] [Linear ℂ D]
    [MonoidalPreadditive D] [MonoidalLinear ℂ D] :
    MonoidalLinear ℂ (Ambient.{v,u,vR,uR} D) :=
  monoidalLinearOfFaithful ℂ (equivalence D).inverse

instance ambientFiniteHom [Preadditive D] [Linear ℂ D]
    [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] (X Y : Ambient.{v,u,vR,uR} D) :
    FiniteDimensional ℂ (X ⟶ Y) :=
  FiniteDimensional.of_injective ((equivalence D).inverse.mapLinearMap ℂ)
    (equivalence D).inverse.map_injective

instance ambientBiproducts [Preadditive D] [HasFiniteBiproducts D] :
    HasFiniteBiproducts (Ambient.{v,u,vR,uR} D) where
  out n := ⟨fun f => by
    change HasBiproduct (fun j => (equivalence D).functor.obj ((equivalence D).inverse.obj (f j)))
    infer_instance⟩

instance ambientKernels [Preadditive D] [HasKernels D] :
    HasKernels (Ambient.{v,u,vR,uR} D) where
  has_limit {X Y} f := by
    let F := (equivalence.{v,u,vR,uR} D).inverse
    letI : HasLimit (parallelPair f 0 ⋙ F) := by
      letI : HasLimit (parallelPair
          ((parallelPair f 0 ⋙ F).map WalkingParallelPairHom.left)
          ((parallelPair f 0 ⋙ F).map WalkingParallelPairHom.right)) := by
        simpa only [Functor.comp_map, parallelPair_map_left, parallelPair_map_right,
          Functor.map_zero] using (inferInstance : HasLimit (parallelPair (F.map f) 0))
      exact hasLimit_of_iso (diagramIsoParallelPair (parallelPair f 0 ⋙ F)).symm
    exact Adjunction.hasLimit_of_comp_equivalence _ F

instance ambientRightRigid [RightRigidCategory D] : RightRigidCategory (Ambient.{v,u,vR,uR} D) :=
  rightRigidCategoryOfEquivalence (equivalence D).symm.toAdjunction

instance ambientSimpleUnit [Preadditive D] [Simple (𝟙_ D)] :
    Simple (𝟙_ (Ambient.{v,u,vR,uR} D)) := by
  have h := DrinfeldCoendModules.SkeletonTransport.simple_image
    (equivalence.{v,u,vR,uR} D).functor (𝟙_ D)
  exact h

end Paper18.Category.ModularExtensionUniverseLift
