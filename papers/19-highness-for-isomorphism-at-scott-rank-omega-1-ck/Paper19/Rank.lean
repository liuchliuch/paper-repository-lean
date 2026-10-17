import Paper19.LiftTree
import Mathlib.SetTheory.Ordinal.Rank
import Mathlib.Order.WellFounded

namespace Paper19

/-- One-step extension in the constructed tree. -/
def SChild (T : Tree) (σ τ : Node) : Prop :=
  (STree T).mem τ ∧ τ.length = σ.length + 1 ∧ τ.take σ.length = σ

theorem SChild.prefix {T : Tree} {σ τ : Node} (h : SChild T σ τ) : σ <+: τ := by
  rw [← h.2.2]; exact List.take_prefix _ _

theorem SChild.mem_left {T : Tree} {σ τ : Node} (h : SChild T σ τ) :
    (STree T).mem σ := (STree T).mem_prefix h.1 h.prefix

def SBelow (T : Tree) (σ : Node) : Set Node :=
  {τ | (STree T).mem τ ∧ σ <+: τ}

theorem dead_accessible {T : Tree} {σ : Node} (hm : (STree T).mem σ)
    (hd : ¬(STree T).IsExtendible σ) : Acc (fun τ σ => SChild T σ τ) σ := by
  classical
  by_contra hn
  obtain ⟨a, ha0, ha⟩ := not_acc_iff_exists_descending_chain.mp hn
  have hlen (k : ℕ) : (a k).length = σ.length + k := by
    induction k with
    | zero => simp [ha0]
    | succ k ih => rw [(ha k).2.1, ih]; omega
  have hp (k : ℕ) : a k <+: a (k + 1) := (ha k).prefix
  have hmem (k : ℕ) : (STree T).mem (a k) := (ha k).mem_left
  apply hd
  refine ⟨chainStream a, chainStream_path (STree T) a hlen hp hmem, ?_⟩
  simpa [ha0] using (chainStream_prefix a hlen hp 0).symm

/-- Rank at least α, including infinite rank. Accessible nodes use their actual
ordinal rank; at an inaccessible node the universal quantifier is vacuous. -/
def HeightGE {α : Type} (r : α → α → Prop) (x : α) (o : Ordinal) : Prop :=
  ∀ h : Acc r x, o ≤ h.rank

theorem heightGE_zero {α : Type} (r : α → α → Prop) (x : α) : HeightGE r x 0 :=
  fun _ => zero_le _

theorem heightGE_succ {α : Type} {r : α → α → Prop} {x : α} {o : Ordinal} :
    HeightGE r x (Order.succ o) ↔ ∃ y, r y x ∧ HeightGE r y o := by
  classical
  constructor
  · intro h
    by_contra hn
    have hc : ∀ y, r y x → ∃ a : Acc r y, a.rank < o := by
      intro y hy
      have hn' : ¬ HeightGE r y o := fun hh => hn ⟨y, hy, hh⟩
      simpa [HeightGE, not_forall, not_le] using hn'
    let a : Acc r x := Acc.intro x (fun y hy => (hc y hy).choose)
    have hr : a.rank ≤ o := by
      rw [a.rank_eq]
      apply Ordinal.iSup_le
      intro y
      exact Order.succ_le_iff.mpr (by
        simpa using (hc y.val y.property).choose_spec)
    exact (not_lt_of_ge hr) ((Order.lt_succ o).trans_le (h a))
  · rintro ⟨y, hy, hh⟩ a
    exact Order.succ_le_iff.mpr ((hh (a.inv hy)).trans_lt (a.rank_lt_of_rel hy))

theorem heightGE_mono {α : Type} {r : α → α → Prop} {x : α} {a b : Ordinal}
    (hab : a ≤ b) (h : HeightGE r x b) : HeightGE r x a :=
  fun hx => hab.trans (h hx)

theorem heightGE_limit {α : Type} {r : α → α → Prop} {x : α}
    {L : Ordinal} {Ls : ℕ → Ordinal} (hle : ∀ j, Ls j ≤ L)
    (hcof : ∀ b < L, ∃ j, b < Ls j) :
    HeightGE r x L ↔ ∀ j, HeightGE r x (Ls j) := by
  constructor
  · exact fun h j => heightGE_mono (hle j) h
  · intro h hx
    by_contra hn
    obtain ⟨j, hj⟩ := hcof hx.rank (lt_of_not_ge hn)
    exact (not_lt_of_ge (h j hx)) hj

def RankAtLeast (T : Tree) (σ : Node) (o : Ordinal) : Prop :=
  (STree T).mem σ ∧ HeightGE (fun τ σ => SChild T σ τ) σ o

theorem rankAtLeast_zero (T : Tree) {σ : Node} (h : (STree T).mem σ) :
    RankAtLeast T σ 0 := ⟨h, heightGE_zero _ _⟩

theorem rankAtLeast_succ {T : Tree} {σ : Node} {o : Ordinal} :
    RankAtLeast T σ (Order.succ o) ↔ ∃ τ, SChild T σ τ ∧ RankAtLeast T τ o := by
  constructor
  · rintro ⟨hm, hh⟩
    obtain ⟨τ, ht, hr⟩ := heightGE_succ.mp hh
    exact ⟨τ, ht, ht.1, hr⟩
  · rintro ⟨τ, ht, hm, hr⟩
    exact ⟨ht.mem_left, heightGE_succ.mpr ⟨τ, ht, hr⟩⟩

/-- The rank comparison in Lemma 6. It proves accessibility and compares
actual ordinal ranks simultaneously by induction on the selected tree node. -/
theorem lift_accessible_rank {T : Tree} {σ : Node}
    (hs : Acc (fun τ σ => SChild T σ τ) σ) :
    ∀ (n : ℕ) (F : Finset Node), σ ∈ F → GMem T n F →
      ∃ hF : Acc (fun y x : Dom T => IsChildG x y) (.vec n F), hF.rank ≤ hs.rank := by
  induction hs with
  | intro σ hs ih =>
    intro n F hσ hF
    have hc : ∀ y : Dom T, IsChildG (.vec n F) y →
        ∃ hy : Acc (fun y x : Dom T => IsChildG x y) y,
          hy.rank < (Acc.intro (r := fun τ σ => SChild T σ τ) σ hs).rank := by
      intro y hchild
      obtain ⟨m, F', E, hx, hy, hp, hF', hE⟩ := hchild
      cases hx
      subst y
      obtain ⟨τ, hτ, hlen, hpre, hm⟩ := exists_child_of_mem_proj hp hE hσ
      have htake : τ.take σ.length = σ := by
        have hn := (hF σ hσ).2
        rw [hn]
        have := List.prefix_iff_eq_take.mp hpre
        simpa [hn] using this.symm
      have ht : SChild T σ τ := ⟨hm, by rw [(hF σ hσ).2]; exact hlen, htake⟩
      obtain ⟨he, hre⟩ := ih τ ht (n + 1) E hτ hE
      exact ⟨he, hre.trans_lt ((Acc.intro (r := fun τ σ => SChild T σ τ) σ hs).rank_lt_of_rel ht)⟩
    let a : Acc (fun y x : Dom T => IsChildG x y) (.vec n F) :=
      Acc.intro _ (fun y hy => (hc y hy).choose)
    refine ⟨a, ?_⟩
    rw [a.rank_eq]
    apply Ordinal.iSup_le
    intro y
    exact Order.succ_le_iff.mpr (by simpa using (hc y.val y.property).choose_spec)

theorem lemma6_dead_rank {T : Tree} {n : ℕ} {F : Finset Node} {σ : Node}
    (hF : GMem T n F) (hσ : σ ∈ F) (hd : ¬(STree T).IsExtendible σ) :
    ∃ (hs : Acc (fun τ σ => SChild T σ τ) σ)
      (hF : Acc (fun y x : Dom T => IsChildG x y) (.vec n F)), hF.rank ≤ hs.rank := by
  have hs := dead_accessible (hF σ hσ).1 hd
  obtain ⟨h, hr⟩ := lift_accessible_rank hs n F hσ hF
  exact ⟨hs, h, hr⟩

end Paper19
