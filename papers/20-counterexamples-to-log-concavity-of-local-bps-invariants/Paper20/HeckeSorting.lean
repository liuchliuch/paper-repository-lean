import Paper20.HeckeTraceAlgebra

namespace Paper20.HeckeSorting
open Polynomial Finset Paper20.BraidWalk Paper20.HeckeOperators
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-- A natural-valued sorting potential. Adjacent descent swaps strictly
decrease it, so no Coxeter length theorem is assumed in the construction. -/
def potential {r : ℕ} (p : Equiv.Perm (Fin r)) : ℕ :=
  ∑ x : Fin r, (r-1-x.val)*(p.symm x).val

lemma sum_two_complement {S : Type*} [Fintype S] [DecidableEq S]
    (f : S → ℕ) (a b : S) (hab : a ≠ b) :
    (∑ x, f x)=f a+f b+∑ x ∈ (univ.erase a).erase b, f x := by
  have h1 := Finset.sum_erase_add univ f (Finset.mem_univ a)
  have hb : b ∈ (univ : Finset S).erase a := by simp [Ne.symm hab]
  have h2 := Finset.sum_erase_add (univ.erase a) f hb
  omega

lemma potential_swap {r : ℕ} (i : Fin (r-1)) (p : Equiv.Perm (Fin r)) :
    potential (adjacentMove i p)+(p.symm (⟨i.val,by omega⟩:Fin r)).val =
      potential p+(p.symm (⟨i.val+1,by omega⟩:Fin r)).val := by
  let a : Fin r := ⟨i.val,by omega⟩
  let b : Fin r := ⟨i.val+1,by omega⟩
  have hab : a ≠ b := by intro h; have he : i.val=i.val+1 := congrArg Fin.val h; omega
  have ha : (adjacentMove i p).symm a=p.symm b := by
    simp only [adjacentMove,Equiv.Perm.mul_def,Equiv.symm_trans_apply,Equiv.symm_swap]
    exact congrArg p.symm (Equiv.swap_apply_left _ _)
  have hb : (adjacentMove i p).symm b=p.symm a := by
    simp only [adjacentMove,Equiv.Perm.mul_def,Equiv.symm_trans_apply,Equiv.symm_swap]
    exact congrArg p.symm (Equiv.swap_apply_right _ _)
  have htail : (∑ x ∈ (univ.erase a).erase b,
      (r-1-x.val)*((adjacentMove i p).symm x).val) =
      ∑ x ∈ (univ.erase a).erase b, (r-1-x.val)*(p.symm x).val := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxa : x ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
    have hxb : x ≠ b := (Finset.mem_erase.mp hx).1
    have he : (adjacentMove i p).symm x=p.symm x := by
      simp only [adjacentMove,Equiv.Perm.mul_def,Equiv.symm_trans_apply,Equiv.symm_swap]
      rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]
    rw [he]
  unfold potential
  rw [sum_two_complement (fun x => (r-1-x.val)*((adjacentMove i p).symm x).val) a b hab,
    sum_two_complement (fun x => (r-1-x.val)*(p.symm x).val) a b hab,ha,hb,htail]
  have hw : r-1-i.val=(r-1-(i.val+1))+1 := by omega
  dsimp only [a,b]
  rw [hw]
  ring

theorem potential_descent_lt {r : ℕ} (i : Fin (r-1)) (p : Equiv.Perm (Fin r))
    (hd : descent i p) : potential (adjacentMove i p) < potential p := by
  have he := potential_swap i p
  unfold descent at hd
  omega

/-- A permutation with no adjacent inverse-position descent is the identity. -/
theorem eq_one_of_no_descent {r : ℕ} (p : Equiv.Perm (Fin r))
    (hp : ∀ i : Fin (r-1), ¬descent i p) : p=1 := by
  have hm : StrictMono p.symm := by
    cases r with
    | zero => intro a; exact Fin.elim0 a
    | succ r =>
      apply Fin.strictMono_iff_lt_succ.mpr
      intro i
      have hn := hp i
      have he : p.symm i.castSucc ≠ p.symm i.succ := by
        intro h
        have hv : i.val=i.val+1 := congrArg Fin.val (p.symm.injective h)
        omega
      change ¬(p.symm i.succ).val < (p.symm i.castSucc).val at hn
      change (p.symm i.castSucc).val < (p.symm i.succ).val
      have he' : (p.symm i.castSucc).val ≠ (p.symm i.succ).val := fun h => he (Fin.ext h)
      omega
  have he : p.symm=(1 : Equiv.Perm (Fin r)) := by
    ext x
    exact le_antisymm (hm.le_id x) (hm.id_le x)
  have hf := congrArg (fun q : Equiv.Perm (Fin r) => q.symm) he
  exact hf

theorem exists_descent {r : ℕ} (p : Equiv.Perm (Fin r)) (hp : p ≠ 1) :
    ∃ i : Fin (r-1), descent i p := by
  by_contra hn
  apply hp
  apply eq_one_of_no_descent p
  simpa only [not_exists] using hn

end
end Paper20.HeckeSorting
