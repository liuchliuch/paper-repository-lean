import CounterFreeHDA.EndoDeletionRestrictions

namespace CounterFreeHDA.EndoPom
universe u
open Cubical
variable {Lab : Type u} {k : ℕ} {U A B : Cube Lab k}

theorem boundary_one_iff (P : EndoPom (cubeInterface U)) (α : Cubical.Face A U) (β : Cubical.Face B U)
    (i : Fin U.dim) : P.boundaryStatus α β i = Status.one ↔ P.Shared i i ∧ α.status i = Status.one := by
  classical
  by_cases hp : P.Shared i i <;> by_cases ha : α.status i = Status.one <;>
    by_cases hb : β.status i = Status.zero <;>
      simp [boundaryStatus,boundaryDeleted,hp,ha,hb,Status.zero,Status.star,Status.one]

theorem boundary_zero_iff (P : EndoPom (cubeInterface U)) (α : Cubical.Face A U) (β : Cubical.Face B U)
    (hc : P.StableCompatible α β) (i : Fin U.dim) :
    P.boundaryStatus α β i = Status.zero ↔ P.Shared i i ∧ β.status i = Status.zero := by
  classical
  by_cases hp : P.Shared i i <;> by_cases ha : α.status i = Status.one <;>
    by_cases hb : β.status i = Status.zero <;>
      simp [boundaryStatus,boundaryDeleted,hp,ha,hb,Status.zero,Status.star,Status.one]
  exfalso
  have hh := hc i hp
  rw [ha,hb] at hh
  exact (by decide : ¬ Status.one ≤ Status.zero) hh

theorem boundary_zero_persistent (P : EndoPom (cubeInterface U)) (α : Cubical.Face A U) (β : Cubical.Face B U)
    (hc : P.StableCompatible α β) (n : ℕ) (i : Fin U.dim)
    (hi : P.boundaryStatus α β i = Status.zero) :
    (P.pow n).Shared i i ∧ β.status i = Status.zero := by
  obtain ⟨hp,hb⟩ := (P.boundary_zero_iff α β hc i).mp hi
  exact ⟨P.persistent_pow n i hp,hb⟩

theorem boundary_one_persistent (P : EndoPom (cubeInterface U)) (α : Cubical.Face A U) (β : Cubical.Face B U)
    (n : ℕ) (i : Fin U.dim) (hi : P.boundaryStatus α β i = Status.one) :
    (P.pow n).Shared i i ∧ α.status i = Status.one := by
  obtain ⟨hp,ha⟩ := (P.boundary_one_iff α β i).mp hi
  exact ⟨P.persistent_pow n i hp,ha⟩

theorem boundary_zero_reached (P : EndoPom (cubeInterface U)) (α : Cubical.Face A U) (β : Cubical.Face B U)
    (hc : P.StableCompatible α β) {n : ℕ} (hn : k ≤ n) (i j : Fin U.dim)
    (hij : (P.pow n).Shared i j) (hj : β.status j = Status.zero) :
    P.boundaryStatus α β i = Status.zero := by
  obtain ⟨he,hp⟩ := (P.lemma_4_1_actual (Nat.le_of_lt_succ U.1.isLt) hn i j).mp hij
  subst j
  exact (P.boundary_zero_iff α β hc i).mpr ⟨hp,hj⟩

theorem boundary_one_reached (P : EndoPom (cubeInterface U)) (α : Cubical.Face A U) (β : Cubical.Face B U)
    {n : ℕ} (hn : k ≤ n) (i j : Fin U.dim)
    (hij : (P.pow n).Shared i j) (hi : α.status i = Status.one) :
    P.boundaryStatus α β j = Status.one := by
  obtain ⟨he,hp⟩ := (P.lemma_4_1_actual (Nat.le_of_lt_succ U.1.isLt) hn i j).mp hij
  subst j
  exact (P.boundary_one_iff α β i).mpr ⟨hp,hi⟩

theorem boundary_one_through (P : EndoPom (cubeInterface U)) (α : Cubical.Face A U) (β : Cubical.Face B U)
    (n : ℕ) (i j : Fin U.dim) (hij : (P.pow n).Shared i j)
    (hi : P.boundaryStatus α β i = Status.one) : P.boundaryStatus α β j = Status.one := by
  have hii := (P.boundary_one_persistent α β n i hi).1
  have he := shared_target_unique (P.pow n) hij hii
  subst j
  exact hi

end CounterFreeHDA.EndoPom
