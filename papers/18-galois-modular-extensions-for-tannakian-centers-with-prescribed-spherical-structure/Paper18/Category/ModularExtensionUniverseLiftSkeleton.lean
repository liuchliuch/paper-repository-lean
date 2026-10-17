import Paper18.Category.ModularExtensionUniverseLiftBasic

/-! # Actual lifted simple representatives and finite decompositions -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w vR uR wR
namespace Paper18.Category.ModularExtensionUniverseLift
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [Preadditive D]
  [HasFiniteBiproducts D] {ι : Type w} [Fintype ι]
  (S : FiniteSemisimpleSkeleton D ι)

/-- Simple labels are independently lifted; every decomposition remains
an actual finite biproduct isomorphism in the enlarged category. -/
def skeleton : FiniteSemisimpleSkeleton (Ambient.{v,u,vR,uR} D) (ULift.{wR} ι) where
  simpleObject i := (equivalence D).functor.obj (S.simpleObject i.down)
  simple i := DrinfeldCoendModules.SkeletonTransport.simple_image
    (equivalence D).functor (S.simpleObject i.down)
  iso_injective i j e := by
    apply ULift.ext
    exact S.iso_injective i.down j.down ⟨(equivalence D).inverse.mapIso e.some⟩
  length Z := S.length ((equivalence D).inverse.obj Z)
  label Z a := ULift.up (S.label ((equivalence D).inverse.obj Z) a)
  decomposition Z :=
    ((equivalence D).counitIso.app Z).symm ≪≫
      (equivalence D).functor.mapIso (S.decomposition ((equivalence D).inverse.obj Z)) ≪≫
      (equivalence D).functor.mapBiproduct
        (fun a => S.simpleObject (S.label ((equivalence D).inverse.obj Z) a))

omit [MonoidalCategory D] in
@[simp] lemma skeleton_simpleObject (i : ULift.{wR} ι) :
    (skeleton.{v,u,w,vR,uR,wR} S).simpleObject i =
      (equivalence D).functor.obj (S.simpleObject i.down) := rfl

end Paper18.Category.ModularExtensionUniverseLift
