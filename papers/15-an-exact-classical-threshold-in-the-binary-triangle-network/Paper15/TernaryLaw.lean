import Paper15.SparseLaws

noncomputable section
namespace Paper15
open Finset BigOperators
namespace Law
variable {α : Type*} [Fintype α]

lemma sum_support (q : Law α) (f : α → ℝ) :
    (∑ x : {a // 0 < q a}, q x.val * f x.val) = q.avg f := by
  classical
  symm
  exact Finset.sum_congr_set {a | 0 < q a} (fun x => q x*f x)
    (fun x => q x.val*f x.val) (fun _ _ => rfl) (fun x hx => by
      have hn : ¬0 < q x := hx
      have hz : q x = 0 := le_antisymm (le_of_not_gt hn) (q.nonneg x)
      simp [hz])

/-- A law supported at at most three original values can be represented on
Fin 3 while preserving expectations of every function. -/
theorem exists_ternary (q : Law α) (hs : {x | 0 < q x}.toFinset.card ≤ 3) :
    ∃ (r : Simplex2) (point : Fin 3 → α), ∀ f : α → ℝ,
      (∑ j, r j * f (point j)) = q.avg f := by
  classical
  let S := {x : α // 0 < q x}
  have hcard : Fintype.card S ≤ 3 := by
    calc
      _ = {x | 0 < q x}.toFinset.card := (Set.toFinset_card {x | 0 < q x}).symm
      _ ≤ 3 := hs
  have hne : Nonempty S := by
    by_contra hn
    have hzero (x : α) : q x=0 := by
      have hp : ¬0 < q x := fun hp => hn ⟨⟨x,hp⟩⟩
      exact le_antisymm (le_of_not_gt hp) (q.nonneg x)
    have := q.sum_eq
    simp_rw [hzero] at this
    simp at this
  let s0 : S := Classical.choice hne
  let e : S ↪ Fin 3 := (Fintype.equivFin S).toEmbedding.trans (Fin.castLEEmb hcard)
  let point : Fin 3 → α := fun j => if h : ∃s : S, e s=j then (Classical.choose h).val else s0.val
  have hpoint (s : S) : point (e s) = s.val := by
    dsimp [point]
    rw [dif_pos ⟨s,rfl⟩]
    exact congrArg Subtype.val (e.injective (Classical.choose_spec (show ∃t, e t=e s from ⟨s,rfl⟩)))
  let r : Simplex2 := {
    v := fun j => ∑ s : S, if e s=j then q s.val else 0
    nonneg := fun j => sum_nonneg (fun s _ => by split_ifs <;> first | exact q.nonneg _ | rfl)
    sum_eq := by
      rw [sum_comm]
      simp only [sum_ite_eq,mem_univ,if_true]
      simpa using (q.sum_support (fun _ => 1)).trans (q.avg_one)
  }
  refine ⟨r,point,fun f => ?_⟩
  change (∑ j, (∑ s : S, if e s=j then q s.val else 0)*f (point j)) = _
  simp_rw [sum_mul]
  rw [sum_comm]
  have heq (s : S) : (∑ j : Fin 3, (if e s=j then q s.val else 0)*f (point j)) = q s.val*f s.val := by
    simp_rw [ite_mul,zero_mul]
    simp [hpoint]
  simp_rw [heq]
  exact q.sum_support f

end Law
end Paper15
