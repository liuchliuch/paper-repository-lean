import Paper17.Support
import Paper17.ChainCombination

/-! Finite Minkowski sums and linear combinations of support functions. -/
noncomputable section
open scoped BigOperators Pointwise
namespace Paper17

theorem compact_nonempty_finset_sum {n : ℕ} {ι : Type*}
    (s : Finset ι) (K : ι → Set (V n))
    (hK : ∀ i ∈ s, IsCompact (K i) ∧ (K i).Nonempty) :
    IsCompact (∑ i ∈ s, K i) ∧ (∑ i ∈ s, K i).Nonempty := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact ⟨isCompact_singleton, Set.singleton_nonempty _⟩
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    have hs := ih (fun j hj => hK j (Finset.mem_insert_of_mem hj))
    exact ⟨(hK i (Finset.mem_insert_self _ _)).1.add hs.1,
      (hK i (Finset.mem_insert_self _ _)).2.add hs.2⟩

theorem supportFunction_finset_sum {n : ℕ} {ι : Type*}
    (s : Finset ι) (K : ι → Set (V n))
    (hK : ∀ i ∈ s, IsCompact (K i) ∧ (K i).Nonempty) (u : V n) :
    supportFunction (∑ i ∈ s, K i) u = ∑ i ∈ s, supportFunction (K i) u := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [supportFunction, dot]
  | @insert i s hi ih =>
    have hs := compact_nonempty_finset_sum s K
      (fun j hj => hK j (Finset.mem_insert_of_mem hj))
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      supportFunction_add (hK i (Finset.mem_insert_self _ _)).1
        (hK i (Finset.mem_insert_self _ _)).2 hs.1 hs.2 u,
      ih (fun j hj => hK j (Finset.mem_insert_of_mem hj))]

theorem delzantSupport_eq_sum_of_carrier {n m : ℕ}
    (P : Fin m → DelzantPolytope n) (R : DelzantPolytope n)
    (w : Fin m → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hcar : R.carrier = ∑ i, w i • (P i).carrier) :
    supportMap (R.val.toPosBody R.property.1) =
      ∑ i, w i • supportMap ((P i).val.toPosBody (P i).property.1) := by
  ext u
  change supportFunction R.carrier u.val = _
  rw [hcar]
  rw [supportFunction_finset_sum Finset.univ (fun i => w i • (P i).carrier)
    (fun i _ => ⟨(P i).val.isCompact.smul _, (P i).val.nonempty.smul_set⟩) u.val]
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  exact supportFunction_smul (P i).val.isCompact (P i).val.nonempty (hw i) u.val

end Paper17
