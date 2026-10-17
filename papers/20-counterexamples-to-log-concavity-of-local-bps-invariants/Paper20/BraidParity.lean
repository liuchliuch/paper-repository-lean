import Paper20.HeckeWalkExpansion

namespace Paper20.BraidWalk
open Polynomial
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

lemma adjacentMove_sign {r : ℕ} (i : Fin (r-1)) (p : Equiv.Perm (Fin r)) :
    Equiv.Perm.sign (adjacentMove i p) = -Equiv.Perm.sign p := by
  have hne : (⟨i.val,by omega⟩:Fin r) ≠ ⟨i.val+1,by omega⟩ := by
    intro h
    have hv : i.val=i.val+1 := congrArg Fin.val h
    omega
  rw [adjacentMove,map_mul,Equiv.Perm.sign_swap hne,neg_one_mul]

/-- Permutation parity records precisely the number of actual moves. -/
theorem endpoint_sign {r : ℕ} (xs : List (Fin (r-1) × Bool))
    (p : Equiv.Perm (Fin r)) :
    Equiv.Perm.sign (endpoint adjacentMove xs p) =
      (-1 : ℤˣ)^((xs.map Prod.snd).count false)*Equiv.Perm.sign p := by
  induction xs generalizing p with
  | nil => simp [endpoint]
  | cons a xs ih =>
    rcases a with ⟨i,b⟩
    cases b with
    | false =>
      rw [endpoint]
      simp only [Bool.false_eq_true,↓reduceIte]
      rw [ih,adjacentMove_sign]
      simp [pow_succ,mul_assoc,mul_comm,mul_left_comm]
    | true => simpa [endpoint] using ih p

lemma bool_counts (xs : List Bool) : xs.count false+xs.count true=xs.length := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp only [List.count_cons,List.length_cons] <;> norm_num <;> omega

/-- Every closed actual permutation walk has an even number of moves. -/
theorem closed_even_moves {r : ℕ} (xs : List (Fin (r-1) × Bool))
    (p : Equiv.Perm (Fin r)) (hc : endpoint adjacentMove xs p=p) :
    Even ((xs.map Prod.snd).count false) := by
  have he := endpoint_sign xs p
  rw [hc] at he
  have hp : (-1:ℤˣ)^((xs.map Prod.snd).count false)=1 := by
    exact mul_right_cancel (b:=Equiv.Perm.sign p) (by simpa using he.symm)
  exact (neg_one_pow_eq_one_iff_even (by decide : (-1:ℤˣ) ≠ 1)).mp hp

/-- For an even-length braid word, every closed walk has an even number
of stays. This justifies collecting the polynomial in `w=z²`. -/
theorem admissible_even_stays {r : ℕ} (word : List (Fin (r-1)))
    (top : Equiv.Perm (Fin r)) (w : Walks.Walk word.length)
    (he : Even word.length) (hw : admissible adjacentMove descent top word w) :
    Even (Walks.nStays w) := by
  have hc := closed_even_moves (word.zip (List.ofFn w)) top hw.2
  have hm : (word.zip (List.ofFn w)).map Prod.snd=List.ofFn w := by
    rw [List.map_snd_zip]
    simp
  rw [hm] at hc
  have hcnt := bool_counts (List.ofFn w)
  rw [List.length_ofFn,nStays_ofFn] at hcnt
  obtain ⟨a,ha⟩ := hc
  obtain ⟨b,hb⟩ := he
  apply even_iff_two_dvd.mpr
  omega

end
end Paper20.BraidWalk
