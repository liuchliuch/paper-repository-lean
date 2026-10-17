import CounterFreeHDA.InducedEmbedding

namespace CounterFreeHDA.Corners
universe u
variable {Lab : Type u} (P : PomsetData Lab)
    (α : Fin P.srcLen → Status) (β : Fin P.tgtLen → Status)

def SourceDeleted (e : Fin P.n) : Prop := ∃ i, P.src i = e ∧ α i = Status.one
def TargetDeleted (e : Fin P.n) : Prop := ∃ i, P.tgt i = e ∧ β i = Status.zero

variable (hc : Compatible P α β)

include hc in
theorem deletions_disjoint {e : Fin P.n} (hs : SourceDeleted P α e) (ht : TargetDeleted P β e) : False := by
  obtain ⟨i,hi,hα⟩ := hs
  obtain ⟨j,hj,hβ⟩ := ht
  have h := hc i j (hi.trans hj.symm)
  rw [hα,hβ] at h
  exact (by decide : ¬ Status.one ≤ Status.zero) h

noncomputable def inclusion : Fin (data P α β hc).n ↪ Fin P.n := by
  classical
  exact Induced.includeEvent P (fun e => ¬ Deleted P α β e) (source P α) (target P β)
    (fun _ hi => source_kept P α β hc hi) (fun _ hj => target_kept P α β hc hj)

noncomputable def retain (e : Fin P.n) (he : ¬ Deleted P α β e) : Fin (data P α β hc).n := by
  classical
  exact Induced.index P (fun e => ¬ Deleted P α β e) ⟨e,he⟩

@[simp] theorem inclusion_retain (e : Fin P.n) (he : ¬ Deleted P α β e) :
    inclusion P α β hc (retain P α β hc e he) = e := by
  classical
  exact congrArg Subtype.val ((Induced.index P (fun e => ¬ Deleted P α β e)).symm_apply_apply _)

theorem inclusion_kept (e : Fin (data P α β hc).n) : ¬ Deleted P α β (inclusion P α β hc e) := by
  classical
  exact Induced.include_kept P (fun e => ¬ Deleted P α β e) _ _ _ _ e

@[simp] theorem retain_inclusion (e : Fin (data P α β hc).n) :
    retain P α β hc (inclusion P α β hc e) (inclusion_kept P α β hc e) = e := by
  apply (inclusion P α β hc).injective
  exact inclusion_retain P α β hc _ _

@[simp] theorem inclusion_source (i : Fin (source P α).card) :
    inclusion P α β hc ((data P α β hc).src i) = P.src ((source P α).orderEmbOfFin rfl i) := by
  classical
  exact Induced.include_source P (fun e => ¬ Deleted P α β e) _ _ _ _ i

@[simp] theorem inclusion_target (i : Fin (target P β).card) :
    inclusion P α β hc ((data P α β hc).tgt i) = P.tgt ((target P β).orderEmbOfFin rfl i) := by
  classical
  exact Induced.include_target P (fun e => ¬ Deleted P α β e) _ _ _ _ i

end CounterFreeHDA.Corners
