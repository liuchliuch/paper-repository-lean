import Paper14.Kac

open Set Function Finset
open Classical
namespace Paper14
noncomputable section

/-- Among ordinary times 1,...,R_n there are precisely n visits to the inducing set. -/
theorem ordinary_visit_count {A : Type*} (T : A → A) (Y : Set A) (x : A)
    (hret : ∀ i, ∃ k, 0 < k ∧ T^[k] ((inducedMap T Y)^[i] x) ∈ Y) (n : ℕ) :
    ((Finset.Ioc 0 (Rn T Y n x)).filter (fun j => T^[j] x ∈ Y)).card = n := by
  classical
  induction n with
  | zero => simp [Rn_zero]
  | succ n ih =>
    let N := Rn T Y n x
    let τ := firstReturnTime T Y ((inducedMap T Y)^[n] x)
    have hτ : 0 < τ ∧ T^[τ] ((inducedMap T Y)^[n] x) ∈ Y := firstReturn_spec (hret n)
    have hpoint : (inducedMap T Y)^[n] x = T^[N] x := induced_iterate_eq T Y n x
    have hNsucc : Rn T Y (n+1) x = N+τ := Rn_succ T Y n x
    have hlast : T^[N+τ] x ∈ Y := by
      rw [Nat.add_comm,iterate_add_apply,← hpoint]
      exact hτ.2
    have heq : ((Finset.Ioc 0 (N+τ)).filter (fun j => T^[j] x ∈ Y)) =
        insert (N+τ) ((Finset.Ioc 0 N).filter (fun j => T^[j] x ∈ Y)) := by
      ext j
      simp only [Finset.mem_filter,Finset.mem_Ioc,Finset.mem_insert]
      constructor
      · intro hj
        by_cases hprev : j ≤ N
        · exact Or.inr ⟨⟨hj.1.1,hprev⟩,hj.2⟩
        · have hk : 0 < j-N := by omega
          have hsum : j-N+N=j := by omega
          have hmem : T^[j-N] ((inducedMap T Y)^[n] x) ∈ Y := by
            rw [hpoint,← iterate_add_apply,hsum]
            exact hj.2
          have hmin := firstReturn_le hk hmem
          left
          change τ ≤ j-N at hmin
          omega
      · rintro (rfl | hj)
        · exact ⟨⟨by omega,le_rfl⟩,hlast⟩
        · exact ⟨⟨hj.1.1,by omega⟩,hj.2⟩
    have hnot : N+τ ∉ ((Finset.Ioc 0 N).filter (fun j => T^[j] x ∈ Y)) := by
      simp only [Finset.mem_filter,Finset.mem_Ioc,not_and]
      omega
    rw [hNsucc,heq,Finset.card_insert_of_notMem hnot]
    simpa only [N,ih]

/-- The excess is precisely the number of omitted ordinary visits. -/
theorem ordinary_outside_count {A : Type*} (T : A → A) (Y : Set A) (x : A)
    (hret : ∀ i, ∃ k, 0 < k ∧ T^[k] ((inducedMap T Y)^[i] x) ∈ Y) (n : ℕ) :
    ((Finset.Ioc 0 (Rn T Y n x)).filter (fun j => T^[j] x ∉ Y)).card+n = Rn T Y n x := by
  classical
  have hv := ordinary_visit_count T Y x hret n
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card (s := Finset.Ioc 0 (Rn T Y n x)) (p := fun j => T^[j] x ∈ Y)
  rw [hv] at hsplit
  simp only [Nat.card_Ioc,Nat.sub_zero] at hsplit
  omega

end
end Paper14
