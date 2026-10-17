import CounterFreeHDA.BoundaryReducedCube
import CounterFreeHDA.BoundarySaturation
import CounterFreeHDA.EndoCornerComposition
import CounterFreeHDA.TypedCornerIso

namespace CounterFreeHDA.EndoPom
universe u
open Cubical
variable {Lab : Type u} {k : ℕ} {U A B : Cube Lab k}

noncomputable def transport {V W : Interface Lab} (h : V = W) (P : EndoPom V) : EndoPom W := h ▸ P

noncomputable def transportPowIso {V W : Interface Lab} (h : V = W) (P : EndoPom V) (n : ℕ) :
    PomsetIso ((transport h P).pow n).pom.val (P.pow n).pom.val := by
  cases h
  exact PomsetIso.refl _

theorem transport_width {V W : Interface Lab} (h : V = W) (P : EndoPom V)
    (hw : P.pom.val.WidthLE k) : (transport h P).pom.val.WidthLE k := by
  cases h
  exact hw

noncomputable def boundaryReduced (P : EndoPom (cubeInterface U)) (α : Cubical.Face A U) (β : Cubical.Face B U)
    (hw : P.pom.val.WidthLE k) : EndoPom (cubeInterface (Cubical.Face.activeCube U (P.boundaryStatus α β))) :=
  transport (congrArg cubeInterface (P.boundary_reduced_cube α β hw))
    (P.reduced (P.boundaryDeleted α β) (P.boundaryDeleted_persistent α β) hw)

theorem boundaryReduced_width (P : EndoPom (cubeInterface U)) (α : Cubical.Face A U) (β : Cubical.Face B U)
    (hw : P.pom.val.WidthLE k) : (P.boundaryReduced α β hw).pom.val.WidthLE k :=
  transport_width _ _ (P.deleteData_width _ hw)

noncomputable def boundaryReducedMiddleIso (P : EndoPom (cubeInterface U)) (α : Cubical.Face A U) (β : Cubical.Face B U)
    (hw : P.pom.val.WidthLE k) (n : ℕ) :
    PomsetIso ((P.boundaryReduced α β hw).pow n).pom.val
      (((P.boundedPower hw n).toArrow.corner (P.width_pow hw n) (P.boundaryFace α β) (P.boundaryFace α β)
        (P.boundary_middle_compatible α β hw n)).pom.val) :=
  (transportPowIso _ _ n).trans (P.middlePowerIso α β hw n)

noncomputable def leftFactor (P : EndoPom (cubeInterface U)) (α : Cubical.Face A U) (β : Cubical.Face B U)
    (hc : P.StableCompatible α β) (hw : P.pom.val.WidthLE k) :
    BoundedArrow A (Cubical.Face.activeCube U (P.boundaryStatus α β)) :=
  (P.boundedPower hw k).toArrow.corner (P.width_pow hw k) α (P.boundaryFace α β)
    (P.boundary_left_compatible α β hc hw (le_refl k))

noncomputable def rightFactor (P : EndoPom (cubeInterface U)) (α : Cubical.Face A U) (β : Cubical.Face B U)
    (hc : P.StableCompatible α β) (hw : P.pom.val.WidthLE k) :
    BoundedArrow (Cubical.Face.activeCube U (P.boundaryStatus α β)) B :=
  (P.boundedPower hw k).toArrow.corner (P.width_pow hw k) (P.boundaryFace α β) β
    (P.boundary_right_compatible α β hc hw (le_refl k))

theorem power_compatible (P : EndoPom (cubeInterface U)) (α : Cubical.Face A U) (β : Cubical.Face B U)
    (hc : P.StableCompatible α β) (hw : P.pom.val.WidthLE k) {n : ℕ} (hn : k ≤ n) :
    (P.boundedPower hw n).toArrow.Compatible α β := by
  intro i j hij
  change (P.pow n).Shared i j at hij
  obtain ⟨he,hp⟩ := (P.lemma_4_1_actual (Nat.le_of_lt_succ U.1.isLt) hn i j).mp hij
  subst j
  exact hc i hp

end CounterFreeHDA.EndoPom
