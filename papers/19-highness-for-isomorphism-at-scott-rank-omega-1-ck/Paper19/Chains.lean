import Paper19.Core
import Mathlib.Data.List.GetD

namespace Paper19

theorem prefix_getD {α : Type} {a b : List α} (hp : a <+: b)
    (i : ℕ) (d : α) (hi : i < a.length) : a.getD i d = b.getD i d := by
  rw [List.getD_eq_getElem _ d hi,
    List.getD_eq_getElem _ d (hi.trans_le hp.length_le)]
  exact IsPrefix.get_eq hp ⟨i, hi⟩

theorem chain_prefix (a : ℕ → Node) (hp : ∀ k, a k <+: a (k + 1))
    {i j : ℕ} (h : i ≤ j) : a i <+: a j := by
  induction j, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ j hj ih => exact ih.trans (hp j)

/-- Union of a chain of one-step extensions, starting at an arbitrary level. -/
def chainStream (a : ℕ → Node) : Stream := fun i => (a (i + 1)).getD i 0

theorem chainStream_entry (a : ℕ → Node) {n : ℕ}
    (hlen : ∀ k, (a k).length = n + k) (hp : ∀ k, a k <+: a (k + 1))
    (k i : ℕ) (hi : i < (a k).length) : chainStream a i = (a k).getD i 0 := by
  have hi' : i < (a (i + 1)).length := by rw [hlen]; omega
  rcases le_total k (i + 1) with h | h
  · exact (prefix_getD (chain_prefix a hp h) i 0 hi).symm
  · exact prefix_getD (chain_prefix a hp h) i 0 hi'

theorem chainStream_prefix (a : ℕ → Node) {n : ℕ}
    (hlen : ∀ k, (a k).length = n + k) (hp : ∀ k, a k <+: a (k + 1)) (k : ℕ) :
    List.ofFn (fun i : Fin (n + k) => chainStream a i) = a k := by
  apply List.ext_getElem
  · simpa using (hlen k).symm
  · intro i hi hi'
    rw [List.getElem_ofFn, chainStream_entry a hlen hp k i hi',
      List.getD_eq_getElem _ 0 hi']

theorem chainStream_path (S : Tree) (a : ℕ → Node) {n : ℕ}
    (hlen : ∀ k, (a k).length = n + k) (hp : ∀ k, a k <+: a (k + 1))
    (hm : ∀ k, S.mem (a k)) : S.IsPath (chainStream a) := by
  intro m
  have h := chainStream_prefix a hlen hp m
  have hpre : List.ofFn (fun i : Fin m => chainStream a i) <+:
      List.ofFn (fun i : Fin (n + m) => chainStream a i) := by
    have ht : (List.ofFn (fun i : Fin (n + m) => chainStream a i)).take m =
        List.ofFn (fun i : Fin m => chainStream a i) := by
      apply List.ext_getElem
      · simp
      · intros; simp
    rw [← ht]; exact List.take_prefix _ _
  rw [h] at hpre
  exact S.mem_prefix (hm m) hpre

end Paper19
