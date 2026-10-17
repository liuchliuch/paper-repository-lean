import CounterFreeHDA.MiddleCorner

namespace CounterFreeHDA.EndoPom
universe u
open Cubical
variable {Lab : Type u} {k : ℕ} {U A B : Cube Lab k}

theorem boundary_reduced_cube (P : EndoPom (cubeInterface U)) (α : Cubical.Face A U) (β : Cubical.Face B U)
    (hw : P.pom.val.WidthLE k) :
    P.reducedCube (P.boundaryDeleted α β) hw = Cubical.Face.activeCube U (P.boundaryStatus α β) := by
  apply Cube.interface_injective
  have he := (P.middlePowerIso α β hw 0).source_type
  exact he.trans ((P.boundedPower hw 0).toArrow.corner (P.width_pow hw 0)
      (P.boundaryFace α β) (P.boundaryFace α β) (P.boundary_middle_compatible α β hw 0)).source

end CounterFreeHDA.EndoPom
