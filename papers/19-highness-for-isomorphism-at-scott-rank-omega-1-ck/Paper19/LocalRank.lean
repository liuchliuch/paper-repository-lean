import Paper19.Rank
import Paper19.NormalForm

namespace Paper19

/-- Forest of dead level-n subtrees with one extra root. Only the root and
its descendants are used in this ordinal presentation. -/
def LocalRel (T : Tree) (n : ℕ) : Option Node → Option Node → Prop
  | some τ, some σ => SChild T σ τ
  | some σ, none => σ ∈ deadLevel (STree T) n
  | none, _ => False

theorem local_some_accessible {T : Tree} {n : ℕ} {σ : Node}
    (hs : Acc (fun τ σ => SChild T σ τ) σ) : Acc (LocalRel T n) (some σ) := by
  induction hs with
  | intro σ hs ih =>
    refine Acc.intro _ ?_
    intro y hy
    cases y with
    | none => exact False.elim hy
    | some τ => exact ih τ hy

theorem local_rank_ge {T : Tree} {n : ℕ} {σ : Node}
    (hs : Acc (fun τ σ => SChild T σ τ) σ) :
    ∀ hl : Acc (LocalRel T n) (some σ), hs.rank ≤ hl.rank := by
  induction hs with
  | intro σ hs ih =>
    intro hl
    rw [Acc.rank_eq]
    apply Ordinal.iSup_le
    intro τ
    have hrel : LocalRel T n (some τ.val) (some σ) := τ.property
    exact (Order.succ_le_succ (ih τ.val τ.property (hl.inv hrel))).trans
      (Order.succ_le_iff.mpr (hl.rank_lt_of_rel hrel))

theorem local_root_accessible (T : Tree) (n : ℕ) : Acc (LocalRel T n) none := by
  refine Acc.intro _ ?_
  intro y hy
  cases y with
  | none => exact False.elim hy
  | some σ => exact local_some_accessible (dead_accessible hy.1 hy.2.2)

noncomputable def localBound (T : Tree) (n : ℕ) : Ordinal :=
  (local_root_accessible T n).rank

/-- Genuine ordinal upper bound on every dead node at the given level. -/
theorem lemma3_ordinal_bound (T : Tree) (n : ℕ) (σ : Node)
    (hd : σ ∈ deadLevel (STree T) n) :
    ∀ hs : Acc (fun τ σ => SChild T σ τ) σ, hs.rank < localBound T n := by
  intro hs
  have hr : LocalRel T n (some σ) none := hd
  exact (local_rank_ge hs ((local_root_accessible T n).inv hr)).trans_lt
    ((local_root_accessible T n).rank_lt_of_rel hr)

/-- Equation (7) with actual lift ranks and the local ordinal bound. -/
theorem theta_iff_extendible_support {T : Tree} {n : ℕ} {F : Finset Node}
    (hF : GMem T n F) :
    HeightGE (fun y x : Dom T => IsChildG x y) (.vec n F) (localBound T n) ↔
      ∀ σ ∈ F, σ ∈ extLevel (STree T) n := by
  classical
  constructor
  · intro hh σ hσ
    refine ⟨(hF σ hσ).1, (hF σ hσ).2, ?_⟩
    by_contra hd
    obtain ⟨hs, hl, hr⟩ := lemma6_dead_rank hF hσ hd
    have hlt := lemma3_ordinal_bound T n σ ⟨(hF σ hσ).1, (hF σ hσ).2, hd⟩ hs
    exact not_lt_of_ge (hh hl) (hr.trans_lt hlt)
  · intro he ha
    have hlift := hasInfiniteLiftG_of_subset_ext he
    have hn : ¬Acc (fun y x : Dom T => IsChildG x y) (.vec n F) :=
      not_acc_iff_exists_descending_chain.mpr hlift
    exact False.elim (hn ha)

end Paper19
