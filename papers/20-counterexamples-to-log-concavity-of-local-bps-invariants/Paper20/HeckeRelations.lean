import Paper20.HeckeOperators

namespace Paper20.HeckeOperators
open Paper20.BraidWalk
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

lemma swap_braid {α : Type*} [DecidableEq α] (a b c : α)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    Equiv.swap a b * Equiv.swap b c * Equiv.swap a b =
      Equiv.swap b c * Equiv.swap a b * Equiv.swap b c := by
  have hleft := Equiv.swap_mul_swap_mul_swap (x:=c) (y:=b) (z:=a)
    hbc.symm hac.symm
  have hright := Equiv.swap_mul_swap_mul_swap (x:=a) (y:=b) (z:=c) hab hac
  rw [Equiv.swap_comm b a, Equiv.swap_comm c b] at hleft
  rw [Equiv.swap_comm c a] at hright
  exact hleft.trans hright.symm

lemma adjacentMove_braid {r : ℕ} (i j : Fin (r-1)) (hij : j.val=i.val+1)
    (p : Equiv.Perm (Fin r)) :
    adjacentMove i (adjacentMove j (adjacentMove i p)) =
      adjacentMove j (adjacentMove i (adjacentMove j p)) := by
  let a : Fin r := ⟨i.val,by omega⟩
  let b : Fin r := ⟨i.val+1,by omega⟩
  let c : Fin r := ⟨i.val+2,by omega⟩
  have hab : a ≠ b := by intro h; have := congrArg Fin.val h; dsimp [a,b] at this; omega
  have hbc : b ≠ c := by intro h; have := congrArg Fin.val h; dsimp [b,c] at this; omega
  have hac : a ≠ c := by intro h; have := congrArg Fin.val h; dsimp [a,c] at this; omega
  have hj0 : (⟨j.val,by omega⟩:Fin r) = b := Fin.ext hij
  have hj1 : (⟨j.val+1,by omega⟩:Fin r) = c := Fin.ext (by dsimp [c]; omega)
  simp only [adjacentMove,hj0,hj1]
  change Equiv.swap a b*(Equiv.swap b c*(Equiv.swap a b*p)) =
    Equiv.swap b c*(Equiv.swap a b*(Equiv.swap b c*p))
  simp only [← mul_assoc,swap_braid a b c hab hbc hac]

section Pair
variable {α R : Type*} [LinearOrder α] [CommRing R]

def pairOperator (a b : α) (z : R) (f : Equiv.Perm α → R) : Equiv.Perm α → R :=
  operator (fun p => Equiv.swap a b*p) (fun p => p.symm b < p.symm a) z f

lemma inverse_swap_mul (a b x : α) (p : Equiv.Perm α) :
    (Equiv.swap a b*p).symm x = p.symm (Equiv.swap a b x) := rfl

/-- The braid relation is verified in the actual permutation basis,
including all descent-stay terms. -/
theorem pairOperator_braid (a b c : α) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (z : R) (f : Equiv.Perm α → R) (p : Equiv.Perm α) :
    pairOperator a b z (pairOperator b c z (pairOperator a b z f)) p =
      pairOperator b c z (pairOperator a b z (pairOperator b c z f)) p := by
  have hleft := swap_braid a b c hab hbc hac
  have hab' : p.symm a ≠ p.symm b := fun h => hab (p.symm.injective h)
  have hbc' : p.symm b ≠ p.symm c := fun h => hbc (p.symm.injective h)
  have hac' : p.symm a ≠ p.symm c := fun h => hac (p.symm.injective h)
  simp only [pairOperator,operator,inverse_swap_mul,
    Equiv.swap_apply_left,Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm,
    Equiv.swap_apply_of_ne_of_ne hab hac]
  simp only [← mul_assoc,Equiv.swap_mul_self,one_mul,hleft]
  split_ifs <;> first | order | ring

lemma swap_commute (a b c d : α) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) :
    Equiv.swap a b*Equiv.swap c d = Equiv.swap c d*Equiv.swap a b := by
  rw [Equiv.mul_swap_eq_swap_mul]
  rw [Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm,
    Equiv.swap_apply_of_ne_of_ne had.symm hbd.symm]

theorem pairOperator_commute (a b c d : α) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (z : R) (f : Equiv.Perm α → R) (p : Equiv.Perm α) :
    pairOperator a b z (pairOperator c d z f) p =
      pairOperator c d z (pairOperator a b z f) p := by
  have hm := swap_commute a b c d hac had hbc hbd
  simp only [pairOperator,operator,inverse_swap_mul,
    Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm,
    Equiv.swap_apply_of_ne_of_ne had.symm hbd.symm,
    Equiv.swap_apply_of_ne_of_ne hac had,
    Equiv.swap_apply_of_ne_of_ne hbc hbd]
  simp only [← mul_assoc,hm]
  split_ifs <;> ring

end Pair

lemma adjacent_pairOperator {r : ℕ} {R : Type*} [CommRing R]
    (i : Fin (r-1)) (z : R) (f : Equiv.Perm (Fin r) → R) :
    operator (adjacentMove i) (descent i) z f =
      pairOperator (⟨i.val,by omega⟩:Fin r) ⟨i.val+1,by omega⟩ z f := by
  funext p
  simp only [pairOperator,operator,adjacentMove,descent,Fin.lt_def]
  have hd : instDecidableEqFin r = (fun a b : Fin r => Classical.propDecidable (a=b)) :=
    Subsingleton.elim _ _
  simp only [hd]
  split_ifs <;> rfl

/-- The full adjacent braid relation for the standard Hecke action. -/
theorem adjacent_braid {r : ℕ} {R : Type*} [CommRing R]
    (i j : Fin (r-1)) (hij : j.val=i.val+1) (z : R)
    (f : Equiv.Perm (Fin r) → R) (p : Equiv.Perm (Fin r)) :
    operator (adjacentMove i) (descent i) z
      (operator (adjacentMove j) (descent j) z
        (operator (adjacentMove i) (descent i) z f)) p =
    operator (adjacentMove j) (descent j) z
      (operator (adjacentMove i) (descent i) z
        (operator (adjacentMove j) (descent j) z f)) p := by
  let a : Fin r := ⟨i.val,by omega⟩
  let b : Fin r := ⟨i.val+1,by omega⟩
  let c : Fin r := ⟨i.val+2,by omega⟩
  have hab : a ≠ b := by intro h; have := congrArg Fin.val h; dsimp [a,b] at this; omega
  have hbc : b ≠ c := by intro h; have := congrArg Fin.val h; dsimp [b,c] at this; omega
  have hac : a ≠ c := by intro h; have := congrArg Fin.val h; dsimp [a,c] at this; omega
  have hj0 : (⟨j.val,by omega⟩:Fin r) = b := Fin.ext hij
  have hj1 : (⟨j.val+1,by omega⟩:Fin r) = c := Fin.ext (by dsimp [c]; omega)
  simp only [adjacent_pairOperator]
  change pairOperator a b z (pairOperator (⟨j.val,by omega⟩:Fin r)
    ⟨j.val+1,by omega⟩ z (pairOperator a b z f)) p =
      pairOperator (⟨j.val,by omega⟩:Fin r) ⟨j.val+1,by omega⟩ z
        (pairOperator a b z (pairOperator (⟨j.val,by omega⟩:Fin r) ⟨j.val+1,by omega⟩ z f)) p
  rw [hj0,hj1]
  exact pairOperator_braid a b c hab hbc hac z f p

/-- Distant adjacent generators commute in this same action. -/
theorem adjacent_commute {r : ℕ} {R : Type*} [CommRing R]
    (i j : Fin (r-1)) (hij : i.val+1 < j.val ∨ j.val+1 < i.val) (z : R)
    (f : Equiv.Perm (Fin r) → R) (p : Equiv.Perm (Fin r)) :
    operator (adjacentMove i) (descent i) z (operator (adjacentMove j) (descent j) z f) p =
      operator (adjacentMove j) (descent j) z (operator (adjacentMove i) (descent i) z f) p := by
  simp only [adjacent_pairOperator]
  apply pairOperator_commute (⟨i.val,by omega⟩:Fin r) ⟨i.val+1,by omega⟩
    (⟨j.val,by omega⟩:Fin r) ⟨j.val+1,by omega⟩ _ _ _ _ z f p
  all_goals intro h; have := congrArg Fin.val h; simp only [Fin.mk.injEq] at *; omega

end
end Paper20.HeckeOperators
