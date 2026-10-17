import CounterFreeHDA.Pomset
import Mathlib.Data.Finset.Sort

/-! Induced deletion of actual events, with explicitly selected ordered
interfaces. This construction is used for corners and persistent deletion. -/

namespace CounterFreeHDA

universe u

namespace Induced

variable {Lab : Type u} (P : PomsetData Lab) (keep : Fin P.n → Prop) [DecidablePred keep]

abbrev Event := {e : Fin P.n // keep e}

noncomputable def index : Event P keep ≃ Fin (Fintype.card (Event P keep)) := Fintype.equivFin _

noncomputable def data
    (S : Finset (Fin P.srcLen)) (T : Finset (Fin P.tgtLen))
    (hS : ∀ i ∈ S, keep (P.src i)) (hT : ∀ i ∈ T, keep (P.tgt i)) : PomsetData Lab where
  n := Fintype.card (Event P keep)
  lab e := P.lab ((index P keep).symm e).val
  prec e f := P.prec ((index P keep).symm e).val ((index P keep).symm f).val
  eord e f := P.eord ((index P keep).symm e).val ((index P keep).symm f).val
  srcLen := S.card
  tgtLen := T.card
  src i := index P keep ⟨P.src (S.orderEmbOfFin rfl i), hS _ (S.orderEmbOfFin_mem rfl i)⟩
  tgt i := index P keep ⟨P.tgt (T.orderEmbOfFin rfl i), hT _ (T.orderEmbOfFin_mem rfl i)⟩
  src_inj := by
    intro i j h
    have h' := congrArg Subtype.val ((index P keep).injective h)
    exact (S.orderEmbOfFin rfl).injective (P.src_inj h')
  tgt_inj := by
    intro i j h
    have h' := congrArg Subtype.val ((index P keep).injective h)
    exact (T.orderEmbOfFin rfl).injective (P.tgt_inj h')

noncomputable def includeEvent
    (S : Finset (Fin P.srcLen)) (T : Finset (Fin P.tgtLen))
    (hS : ∀ i ∈ S, keep (P.src i)) (hT : ∀ i ∈ T, keep (P.tgt i)) :
    Fin (data P keep S T hS hT).n ↪ Fin P.n :=
  ⟨fun e => ((index P keep).symm e).val, Subtype.val_injective.comp (index P keep).symm.injective⟩

/-- Induced deletion preserves all actual interval-pomset conditions. -/
theorem isIntervalPom (hP : IsIntervalPom P)
    (S : Finset (Fin P.srcLen)) (T : Finset (Fin P.tgtLen))
    (hS : ∀ i ∈ S, keep (P.src i)) (hT : ∀ i ∈ T, keep (P.tgt i)) :
    IsIntervalPom (data P keep S T hS hT) := by
  let e : Fin (data P keep S T hS hT).n ↪ Fin P.n := includeEvent P keep S T hS hT
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x; exact hP.prec_irrefl (e x)
  · intro x y z hxy hyz; exact hP.prec_trans hxy hyz
  · intro x; exact hP.eord_irrefl (e x)
  · intro x hx
    have lift : ∀ {a b}, Relation.TransGen (data P keep S T hS hT).eord a b →
        Relation.TransGen P.eord (e a) (e b) := by
      intro a b hab
      induction hab with
      | single h => exact .single h
      | tail _ h ih => exact ih.tail h
    exact hP.eord_acyclic _ (lift hx)
  · intro x y hxy
    exact hP.trichotomy (e x) (e y) (fun h => hxy (e.injective h))
  · intro x hx y hy
    obtain ⟨i,rfl⟩ := hx
    change P.prec (e y) _ at hy
    simp only [data, Equiv.symm_apply_apply] at hy
    exact hP.src_minimal _ ⟨_,rfl⟩ _ hy
  · intro x hx y hy
    obtain ⟨i,rfl⟩ := hx
    change P.prec _ (e y) at hy
    simp only [data, Equiv.symm_apply_apply] at hy
    exact hP.tgt_maximal _ ⟨_,rfl⟩ _ hy
  · intro i j
    change P.eord _ _ ↔ i.val < j.val
    simp only [data, Equiv.symm_apply_apply]
    rw [hP.src_eord]
    exact (S.orderEmbOfFin rfl).strictMono.lt_iff_lt
  · intro i j
    change P.eord _ _ ↔ i.val < j.val
    simp only [data, Equiv.symm_apply_apply]
    rw [hP.tgt_eord]
    exact (T.orderEmbOfFin rfl).strictMono.lt_iff_lt
  · obtain ⟨s,t,hrep⟩ := hP.interval_rep
    exact ⟨s ∘ e,t ∘ e,fun x y => hrep _ _⟩

end Induced

namespace Corners

variable {Lab : Type u} (P : PomsetData Lab)
variable (α : Fin P.srcLen → Status) (β : Fin P.tgtLen → Status)

def Compatible : Prop := ∀ i j, P.src i = P.tgt j → α i ≤ β j

def Deleted (e : Fin P.n) : Prop :=
  (∃ i, P.src i = e ∧ α i = Status.one) ∨ (∃ j, P.tgt j = e ∧ β j = Status.zero)

noncomputable def source : Finset (Fin P.srcLen) := by
  classical
  exact Finset.univ.filter (fun i => α i = Status.star)

noncomputable def target : Finset (Fin P.tgtLen) := by
  classical
  exact Finset.univ.filter (fun j => β j = Status.star)

theorem source_kept (hc : Compatible P α β) {i : Fin P.srcLen}
    (hi : i ∈ source P α) : ¬ Deleted P α β (P.src i) := by
  classical
  have hi' : α i = Status.star := (Finset.mem_filter.mp hi).2
  rintro (⟨j,hj,hα⟩ | ⟨j,hj,hβ⟩)
  · have hji := P.src_inj hj
    subst j
    rw [hi'] at hα
    exact (by decide : Status.star ≠ Status.one) hα
  · have h := hc i j hj.symm
    rw [hi',hβ] at h
    exact (by decide : ¬ Status.star ≤ Status.zero) h

theorem target_kept (hc : Compatible P α β) {j : Fin P.tgtLen}
    (hj : j ∈ target P β) : ¬ Deleted P α β (P.tgt j) := by
  classical
  have hj' : β j = Status.star := (Finset.mem_filter.mp hj).2
  rintro (⟨i,hi,hα⟩ | ⟨i,hi,hβ⟩)
  · have h := hc i j hi
    rw [hα,hj'] at h
    exact (by decide : ¬ Status.one ≤ Status.star) h
  · have hij := P.tgt_inj hi
    subst i
    rw [hj'] at hβ
    exact (by decide : Status.star ≠ Status.zero) hβ

/-- The actual corner P[α,β], with deleted events removed and new interfaces. -/
noncomputable def data (hc : Compatible P α β) : PomsetData Lab := by
  classical
  exact Induced.data P (fun e => ¬ Deleted P α β e) (source P α) (target P β)
    (fun _ hi => source_kept P α β hc hi) (fun _ hj => target_kept P α β hc hj)

/-- The compatibility condition suffices; no well-formedness of the desired
corner is assumed. -/
theorem isIntervalPom (hP : IsIntervalPom P) (hc : Compatible P α β) :
    IsIntervalPom (data P α β hc) := by
  classical
  exact Induced.isIntervalPom P _ hP _ _ _ _

noncomputable def pomset (P : IntervalPom Lab) (α : Fin P.srcLen → Status)
    (β : Fin P.tgtLen → Status) (hc : Compatible P.val α β) : IntervalPom Lab :=
  ⟨data P.val α β hc, isIntervalPom P.val α β P.property hc⟩

end Corners
end CounterFreeHDA
