import CounterFreeHDA.BoundaryFactorization

/-! Interface history length is the number of interface events, independently
of the ambient width available to internal events and intermediate cubes. -/
namespace CounterFreeHDA.EndoPom
universe u
open Cubical
variable {Lab : Type u} {k : ℕ} {U A B : Cube Lab k}

theorem boundary_left_compatible_interface (P : EndoPom (cubeInterface U)) (α : Cubical.Face A U) (β : Cubical.Face B U)
    (hc : P.StableCompatible α β) (hw : P.pom.val.WidthLE k) {n : ℕ} (hn : U.dim ≤ n) :
    (P.boundedPower hw n).toArrow.Compatible α (P.boundaryFace α β) := by
  intro i j hij
  change (P.pow n).Shared i j at hij
  obtain ⟨hij,hi⟩ := (P.lemma_4_1_actual (le_refl U.dim) hn i j).mp hij
  subst j
  exact (P.source_le_boundary α β hc i hi).trans_eq (Cubical.Face.ofStatuses_status U (P.boundaryStatus α β) i).symm

theorem boundary_right_compatible_interface (P : EndoPom (cubeInterface U)) (α : Cubical.Face A U) (β : Cubical.Face B U)
    (hc : P.StableCompatible α β) (hw : P.pom.val.WidthLE k) {n : ℕ} (hn : U.dim ≤ n) :
    (P.boundedPower hw n).toArrow.Compatible (P.boundaryFace α β) β := by
  intro i j hij
  change (P.pow n).Shared i j at hij
  obtain ⟨hij,hi⟩ := (P.lemma_4_1_actual (le_refl U.dim) hn i j).mp hij
  subst j
  exact (Cubical.Face.ofStatuses_status U (P.boundaryStatus α β) i).le.trans (P.boundary_le_target α β hc i hi)

theorem boundary_zero_reached_interface (P : EndoPom (cubeInterface U)) (α : Cubical.Face A U) (β : Cubical.Face B U)
    (hc : P.StableCompatible α β) {n : ℕ} (hn : U.dim ≤ n) (i j : Fin U.dim)
    (hij : (P.pow n).Shared i j) (hj : β.status j = Status.zero) :
    P.boundaryStatus α β i = Status.zero := by
  obtain ⟨he,hp⟩ := (P.lemma_4_1_actual (le_refl U.dim) hn i j).mp hij
  subst j
  exact (P.boundary_zero_iff α β hc i).mpr ⟨hp,hj⟩

theorem boundary_one_reached_interface (P : EndoPom (cubeInterface U)) (α : Cubical.Face A U) (β : Cubical.Face B U)
    {n : ℕ} (hn : U.dim ≤ n) (i j : Fin U.dim)
    (hij : (P.pow n).Shared i j) (hi : α.status i = Status.one) :
    P.boundaryStatus α β j = Status.one := by
  obtain ⟨he,hp⟩ := (P.lemma_4_1_actual (le_refl U.dim) hn i j).mp hij
  subst j
  exact (P.boundary_one_iff α β i).mpr ⟨hp,hi⟩


noncomputable def leftFactorInterface (P : EndoPom (cubeInterface U)) (α : Cubical.Face A U) (β : Cubical.Face B U)
    (hc : P.StableCompatible α β) (hw : P.pom.val.WidthLE k) :
    BoundedArrow A (Cubical.Face.activeCube U (P.boundaryStatus α β)) :=
  (P.boundedPower hw U.dim).toArrow.corner (P.width_pow hw U.dim) α (P.boundaryFace α β)
    (P.boundary_left_compatible_interface α β hc hw (le_refl U.dim))

noncomputable def rightFactorInterface (P : EndoPom (cubeInterface U)) (α : Cubical.Face A U) (β : Cubical.Face B U)
    (hc : P.StableCompatible α β) (hw : P.pom.val.WidthLE k) :
    BoundedArrow (Cubical.Face.activeCube U (P.boundaryStatus α β)) B :=
  (P.boundedPower hw U.dim).toArrow.corner (P.width_pow hw U.dim) (P.boundaryFace α β) β
    (P.boundary_right_compatible_interface α β hc hw (le_refl U.dim))

theorem power_compatible_interface (P : EndoPom (cubeInterface U)) (α : Cubical.Face A U) (β : Cubical.Face B U)
    (hc : P.StableCompatible α β) (hw : P.pom.val.WidthLE k) {n : ℕ} (hn : U.dim ≤ n) :
    (P.boundedPower hw n).toArrow.Compatible α β := by
  intro i j hij
  change (P.pow n).Shared i j at hij
  obtain ⟨he,hp⟩ := (P.lemma_4_1_actual (le_refl U.dim) hn i j).mp hij
  subst j
  exact hc i hp

end CounterFreeHDA.EndoPom
