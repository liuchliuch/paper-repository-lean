import CounterFreeHDA.TypedGlueEvents
import CounterFreeHDA.GluingDeletion

namespace CounterFreeHDA.Cubical.Arrow
universe u
open TrackGlue
variable {Lab : Type u} {k : ℕ} {U V W : Cube Lab k}

def keepTargetEvents (A : Arrow U V) (D : Finset (Fin V.dim)) (e : Fin A.pom.n) : Prop :=
  ¬ ∃ i ∈ D, A.targetEvent i = e

instance keepTargetEventsDecidable (A : Arrow U V) (D : Finset (Fin V.dim)) : DecidablePred (A.keepTargetEvents D) := by
  intro e
  unfold keepTargetEvents
  infer_instance

/-- Exactly those source positions identified with a deleted target event. -/
def pullTargetDeletion (B : Arrow V W) (D : Finset (Fin W.dim)) : Finset (Fin V.dim) :=
  Finset.univ.filter (fun i => ∃ j ∈ D, B.sourceEvent i = B.targetEvent j)

theorem mem_pullTargetDeletion (B : Arrow V W) (D : Finset (Fin W.dim)) (i : Fin V.dim) :
    i ∈ B.pullTargetDeletion D ↔ ∃ j ∈ D, B.sourceEvent i = B.targetEvent j := by
  simp only [pullTargetDeletion,Finset.mem_filter,Finset.mem_univ,true_and]

theorem keepTarget_source (B : Arrow V W) (D : Finset (Fin W.dim)) (i : Fin V.dim) :
    B.keepTargetEvents D (B.sourceEvent i) ↔ i ∉ B.pullTargetDeletion D := by
  rw [mem_pullTargetDeletion]
  unfold keepTargetEvents
  exact not_congr (exists_congr fun j => and_congr Iff.rfl eq_comm)

theorem keepTarget_target (B : Arrow V W) (D : Finset (Fin W.dim)) (i : Fin W.dim) :
    B.keepTargetEvents D (B.targetEvent i) ↔ i ∉ D := by
  constructor
  · intro h hi
    exact h ⟨i,hi,rfl⟩
  · rintro hi ⟨j,hj,hji⟩
    have he := B.pom.val.tgt_inj hji
    have hv : j = i := Fin.ext (congrArg (fun x : Fin B.pom.tgtLen => x.val) he)
    exact hi (hv ▸ hj)

/-- Deleting target events from an actual product restricts exactly to
source-pulled target deletion in the prefix and target deletion in the suffix. -/
noncomputable def targetDeletionPlan (A : Arrow U V) (B : Arrow V W) (D : Finset (Fin W.dim)) :
    Deletion.Plan (A.matching B) where
  keepA := A.keepTargetEvents (B.pullTargetDeletion D)
  keepB := B.keepTargetEvents D
  keepG := (A.comp B).keepTargetEvents D
  left_iff e := by
    apply not_congr
    constructor
    · rintro ⟨j,hj,he⟩
      obtain ⟨i,hi,hij⟩ := (A.event_overlap B e (B.targetEvent j)).mp
        (he.symm.trans (A.comp_targetEvent B j))
      exact ⟨i,(B.mem_pullTargetDeletion D i).mpr ⟨j,hj,hij⟩,hi⟩
    · rintro ⟨i,hi,he⟩
      obtain ⟨j,hj,hij⟩ := (B.mem_pullTargetDeletion D i).mp hi
      exact ⟨j,hj,(A.comp_targetEvent B j).trans
        ((congrArg (rightEvent (A.matching B)) hij.symm).trans
          ((A.seam_event B i).symm.trans (congrArg (leftEvent (A.matching B)) he)))⟩
  right_iff e := by
    apply not_congr
    constructor
    · rintro ⟨i,hi,he⟩
      exact ⟨i,hi,((index (A.matching B)).injective.comp (GluedE.rightMap_inj _ _ _))
        ((A.comp_targetEvent B i).symm.trans he)⟩
    · rintro ⟨i,hi,he⟩
      exact ⟨i,hi,(A.comp_targetEvent B i).trans (congrArg (rightEvent (A.matching B)) he)⟩

end CounterFreeHDA.Cubical.Arrow
