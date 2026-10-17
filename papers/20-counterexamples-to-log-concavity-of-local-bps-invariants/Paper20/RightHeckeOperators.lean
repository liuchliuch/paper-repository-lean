import Paper20.HeckeMatrices

namespace Paper20.HeckeOperators
open Paper20.BraidWalk
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

def rightMove {r : ℕ} (j : Fin (r-1)) (p : Equiv.Perm (Fin r)) : Equiv.Perm (Fin r) :=
  p*Equiv.swap ⟨j.val,by omega⟩ ⟨j.val+1,by omega⟩

def rightDescent {r : ℕ} (j : Fin (r-1)) (p : Equiv.Perm (Fin r)) : Prop :=
  (p (⟨j.val+1,by omega⟩:Fin r)).val < (p ⟨j.val,by omega⟩).val

lemma rightMove_symm {r : ℕ} (j : Fin (r-1)) (p : Equiv.Perm (Fin r)) :
    (rightMove j p).symm=adjacentMove j p.symm := by
  change (p*Equiv.swap _ _)⁻¹=Equiv.swap _ _*p⁻¹
  simp [mul_inv_rev]

lemma adjacentMove_symm {r : ℕ} (i : Fin (r-1)) (p : Equiv.Perm (Fin r)) :
    (adjacentMove i p).symm=rightMove i p.symm := by
  change (Equiv.swap _ _*p)⁻¹=p⁻¹*Equiv.swap _ _
  simp [mul_inv_rev]

lemma rightMove_involutive {r : ℕ} (j : Fin (r-1)) : Function.Involutive (rightMove j) := by
  intro p
  simp [rightMove,← mul_assoc,mul_assoc]

lemma rightDescent_eq {r : ℕ} (j : Fin (r-1)) (p : Equiv.Perm (Fin r)) :
    rightDescent j p ↔ descent j p.symm := Iff.rfl

lemma rightDescent_flip {r : ℕ} (j : Fin (r-1)) (p : Equiv.Perm (Fin r)) :
    rightDescent j (rightMove j p) ↔ ¬rightDescent j p := by
  rw [rightDescent_eq,rightMove_symm,rightDescent_eq]
  exact adjacent_descent_flip j p.symm

lemma left_right_moves_commute {r : ℕ} (i j : Fin (r-1)) (p : Equiv.Perm (Fin r)) :
    adjacentMove i (rightMove j p)=rightMove j (adjacentMove i p) := by
  simp only [adjacentMove,rightMove,mul_assoc]

lemma moves_eq_of_images {r : ℕ} (i j : Fin (r-1)) (p : Equiv.Perm (Fin r))
    (hp : ((p (⟨j.val,by omega⟩:Fin r)).val=i.val ∧
        (p (⟨j.val+1,by omega⟩:Fin r)).val=i.val+1) ∨
      ((p (⟨j.val,by omega⟩:Fin r)).val=i.val+1 ∧
        (p (⟨j.val+1,by omega⟩:Fin r)).val=i.val)) :
    adjacentMove i p=rightMove j p := by
  rw [rightMove,Equiv.mul_swap_eq_swap_mul]
  rcases hp with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · have h0 : p (⟨j.val,by omega⟩:Fin r)=⟨i.val,by omega⟩ := Fin.ext ha
    have h1 : p (⟨j.val+1,by omega⟩:Fin r)=⟨i.val+1,by omega⟩ := Fin.ext hb
    rw [h0,h1]
    rfl
  · have h0 : p (⟨j.val,by omega⟩:Fin r)=⟨i.val+1,by omega⟩ := Fin.ext ha
    have h1 : p (⟨j.val+1,by omega⟩:Fin r)=⟨i.val,by omega⟩ := Fin.ext hb
    rw [h0,h1,Equiv.swap_comm]
    rfl

lemma images_of_moves_eq {r : ℕ} (i j : Fin (r-1)) (p : Equiv.Perm (Fin r))
    (hp : adjacentMove i p=rightMove j p) :
    ((p (⟨j.val,by omega⟩:Fin r)).val=i.val ∧
        (p (⟨j.val+1,by omega⟩:Fin r)).val=i.val+1) ∨
      ((p (⟨j.val,by omega⟩:Fin r)).val=i.val+1 ∧
        (p (⟨j.val+1,by omega⟩:Fin r)).val=i.val) := by
  have he := congrArg (fun q : Equiv.Perm (Fin r) => q (⟨j.val,by omega⟩:Fin r)) hp
  simp only [adjacentMove,rightMove,Equiv.Perm.mul_apply,Equiv.swap_apply_left] at he
  simp only [Equiv.swap_apply_def] at he
  split_ifs at he with ha hb
  · exact Or.inl ⟨congrArg Fin.val ha,congrArg Fin.val he.symm⟩
  · exact Or.inr ⟨congrArg Fin.val hb,congrArg Fin.val he.symm⟩
  · have hj : j.val=j.val+1 := congrArg Fin.val (p.injective he)
    omega

lemma adjacent_swap_lt_stable {r : ℕ} (i : Fin (r-1)) (x y : Fin r)
    (hp : ¬((x.val=i.val ∧ y.val=i.val+1) ∨ (x.val=i.val+1 ∧ y.val=i.val))) :
    (Equiv.swap (⟨i.val,by omega⟩:Fin r) ⟨i.val+1,by omega⟩ x).val <
      (Equiv.swap (⟨i.val,by omega⟩:Fin r) ⟨i.val+1,by omega⟩ y).val ↔ x.val < y.val := by
  simp only [Equiv.swap_apply_def]
  split_ifs <;> simp_all only [Fin.ext_iff,Fin.val_mk,true_and,and_true,false_and,and_false,
    or_true,true_or,or_false,false_or,not_true_eq_false,not_false_eq_true] <;> omega

lemma rightDescent_leftMove {r : ℕ} (i j : Fin (r-1)) (p : Equiv.Perm (Fin r))
    (hp : adjacentMove i p ≠ rightMove j p) :
    rightDescent j (adjacentMove i p) ↔ rightDescent j p := by
  unfold rightDescent
  simp only [adjacentMove,Equiv.Perm.mul_apply]
  apply adjacent_swap_lt_stable
  rintro (⟨hd,hc⟩ | ⟨hd,hc⟩)
  · exact hp (moves_eq_of_images i j p (Or.inr ⟨hc,hd⟩))
  · exact hp (moves_eq_of_images i j p (Or.inl ⟨hc,hd⟩))

lemma descent_rightMove {r : ℕ} (i j : Fin (r-1)) (p : Equiv.Perm (Fin r))
    (hp : adjacentMove i p ≠ rightMove j p) :
    descent i (rightMove j p) ↔ descent i p := by
  have hn : adjacentMove j p.symm ≠ rightMove i p.symm := by
    intro he
    have hs := congrArg (fun q : Equiv.Perm (Fin r) => q.symm) he
    simp only [adjacentMove_symm,rightMove_symm,Equiv.symm_symm] at hs
    exact hp hs.symm
  have he := rightDescent_leftMove j i p.symm hn
  rw [rightDescent_eq,rightDescent_eq,← rightMove_symm] at he
  exact he

lemma descents_eq_of_moves_eq {r : ℕ} (i j : Fin (r-1)) (p : Equiv.Perm (Fin r))
    (hp : adjacentMove i p=rightMove j p) : descent i p ↔ rightDescent j p := by
  rcases images_of_moves_eq i j p hp with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · have h0 : p (⟨j.val,by omega⟩:Fin r)=⟨i.val,by omega⟩ := Fin.ext ha
    have h1 : p (⟨j.val+1,by omega⟩:Fin r)=⟨i.val+1,by omega⟩ := Fin.ext hb
    have h0' : p.symm (⟨i.val,by omega⟩:Fin r)=⟨j.val,by omega⟩ := by rw [← h0]; simp
    have h1' : p.symm (⟨i.val+1,by omega⟩:Fin r)=⟨j.val+1,by omega⟩ := by rw [← h1]; simp
    unfold descent rightDescent
    rw [h0',h1',h0,h1]
    simp
  · have h0 : p (⟨j.val,by omega⟩:Fin r)=⟨i.val+1,by omega⟩ := Fin.ext ha
    have h1 : p (⟨j.val+1,by omega⟩:Fin r)=⟨i.val,by omega⟩ := Fin.ext hb
    have h0' : p.symm (⟨i.val+1,by omega⟩:Fin r)=⟨j.val,by omega⟩ := by rw [← h0]; simp
    have h1' : p.symm (⟨i.val,by omega⟩:Fin r)=⟨j.val+1,by omega⟩ := by rw [← h1]; simp
    unfold descent rightDescent
    rw [h0',h1',h0,h1]
    simp

/-- The actual left and right standard Hecke actions commute. The proof
checks the only exceptional case, where both moves coincide and both
descent conditions agree and flip, rather than assuming a bimodule. -/
theorem left_right_operators_commute {r : ℕ} {R : Type*} [CommRing R]
    (i j : Fin (r-1)) (z : R) (f : Equiv.Perm (Fin r) → R) (p : Equiv.Perm (Fin r)) :
    operator (adjacentMove i) (descent i) z (operator (rightMove j) (rightDescent j) z f) p =
      operator (rightMove j) (rightDescent j) z (operator (adjacentMove i) (descent i) z f) p := by
  by_cases hp : adjacentMove i p=rightMove j p
  · have hd := descents_eq_of_moves_eq i j p hp
    have hflip : rightDescent j (adjacentMove i p) ↔ ¬rightDescent j p := by
      rw [hp,rightDescent_flip]
    have hflip' : descent i (rightMove j p) ↔ ¬descent i p := by
      rw [← hp,adjacent_descent_flip]
    simp only [operator,left_right_moves_commute,hflip,hflip',hd,hp,rightDescent_flip]
  · simp only [operator,left_right_moves_commute,rightDescent_leftMove i j p hp,
      descent_rightMove i j p hp]
    split_ifs <;> ring

end
end Paper20.HeckeOperators
