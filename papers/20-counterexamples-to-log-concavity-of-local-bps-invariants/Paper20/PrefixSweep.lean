import Paper20.HeckeDelta
import Paper20.HalfTwistWord

namespace Paper20.PrefixSweep
open Paper20.BraidWalk
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

def reversePrefixFn (r m : ℕ) (hm : m ≤ r) (a : Fin r) : Fin r :=
  if ha : a.val < m then ⟨m-1-a.val,by omega⟩ else a

lemma reversePrefix_involutive (r m : ℕ) (hm : m ≤ r) :
    Function.Involutive (reversePrefixFn r m hm) := by
  intro a
  apply Fin.ext
  by_cases ha : a.val < m
  · have hb : m-1-a.val < m := by omega
    simp only [reversePrefixFn,dif_pos ha,Fin.val_mk,hb,↓reduceDIte]
    omega
  · simp only [reversePrefixFn,dif_neg ha,ha,↓reduceDIte]

def reversePrefix (r m : ℕ) (hm : m ≤ r) : Equiv.Perm (Fin r) :=
  { toFun := reversePrefixFn r m hm
    invFun := reversePrefixFn r m hm
    left_inv := reversePrefix_involutive r m hm
    right_inv := reversePrefix_involutive r m hm }

lemma reversePrefix_symm_val (r m : ℕ) (hm : m ≤ r) (x : Fin r) :
    ((reversePrefix r m hm).symm x).val=if x.val < m then m-1-x.val else x.val := by
  change (reversePrefixFn r m hm x).val = _
  unfold reversePrefixFn
  split_ifs <;> rfl

def adjacentNat (r i : ℕ) (p : Equiv.Perm (Fin r)) : Equiv.Perm (Fin r) :=
  if hi : i < r-1 then adjacentMove ⟨i,hi⟩ p else p

def state (r m : ℕ) (hm : m < r) : ℕ → Equiv.Perm (Fin r)
  | 0 => reversePrefix r m hm.le
  | t+1 => adjacentNat r (m-1-t) (state r m hm t)

/-- Explicit inverse positions throughout the descending insertion sweep.
The next generator always meets the two positions t and m in that order. -/
theorem state_symm_val (r m : ℕ) (hm : m < r) (t : ℕ) (ht : t ≤ m) (x : Fin r) :
    ((state r m hm t).symm x).val =
      if x.val < m-t then m-1-x.val else
        if x.val=m-t then m else if x.val ≤ m then m-x.val else x.val := by
  induction t generalizing x with
  | zero =>
    rw [state,reversePrefix_symm_val]
    split_ifs <;> omega
  | succ t ih =>
    have ht' : t < m := by omega
    let j := m-1-t
    have hj : j < r-1 := by dsimp [j]; omega
    let a : Fin r := ⟨j,by omega⟩
    let b : Fin r := ⟨j+1,by omega⟩
    rw [state,adjacentNat,dif_pos hj]
    change ((state r m hm t).symm (Equiv.swap a b x)).val = _
    by_cases hxa : x=a
    · subst x
      rw [Equiv.swap_apply_left,ih (by omega)]
      dsimp only [a,b,j]
      split_ifs <;> omega
    · by_cases hxb : x=b
      · subst x
        rw [Equiv.swap_apply_right,ih (by omega)]
        dsimp only [a,b,j]
        split_ifs <;> omega
      · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb,ih (by omega)]
        have hja : x.val ≠ j := fun h => hxa (Fin.ext h)
        have hjb : x.val ≠ j+1 := fun h => hxb (Fin.ext h)
        dsimp only [j] at hja hjb
        split_ifs <;> omega

theorem state_ascent (r m : ℕ) (hm : m < r) (t : ℕ) (ht : t < m) :
    ¬descent (⟨m-1-t,by omega⟩:Fin (r-1)) (state r m hm t) := by
  unfold descent
  rw [state_symm_val r m hm t (by omega),state_symm_val r m hm t (by omega)]
  dsimp only
  split_ifs <;> omega

lemma perm_symm_injective {α : Type*} :
    Function.Injective (fun p : Equiv.Perm α => p.symm) := by
  intro p q h
  exact congrArg (fun e : Equiv.Perm α => e.symm) h

theorem state_final (r m : ℕ) (hm : m < r) :
    state r m hm m=reversePrefix r (m+1) (by omega) := by
  apply perm_symm_injective
  ext x
  dsimp only
  rw [state_symm_val r m hm m le_rfl,reversePrefix_symm_val]
  split_ifs <;> omega

lemma reversePrefix_one (r : ℕ) (hr : 1 ≤ r) : reversePrefix r 1 hr=1 := by
  apply perm_symm_injective
  ext x
  dsimp only
  rw [reversePrefix_symm_val]
  change (if x.val < 1 then 1-1-x.val else x.val)=x.val
  split_ifs <;> omega

lemma reversePrefix_full (r : ℕ) : reversePrefix r r le_rfl=Fin.revPerm := by
  apply perm_symm_injective
  ext x
  dsimp only
  rw [reversePrefix_symm_val,Fin.revPerm_symm]
  simp only [Fin.revPerm_apply,Fin.val_rev,if_pos x.isLt]
  omega

end
end Paper20.PrefixSweep
