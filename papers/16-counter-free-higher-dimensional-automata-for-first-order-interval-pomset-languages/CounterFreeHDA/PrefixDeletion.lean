import CounterFreeHDA.ResidualWitnesses
import CounterFreeHDA.ResidualAction
import CounterFreeHDA.CornerDeletion

namespace CounterFreeHDA.Deletion
universe u
variable {Lab : Type u} {P : PomsetData Lab}

/-- Retaining every event is a full event/order/interface isomorphism. -/
noncomputable def noDeletionIso (hP : IsIntervalPom P) (keep : Fin P.n → Prop) [DecidablePred keep]
    (hk : ∀ e, keep e) : PomsetIso (data P keep) P := by
  let E : Fin (data P keep).n ≃ Fin P.n := Equiv.ofBijective (inclusion P keep)
    ⟨(inclusion P keep).injective,fun e => ⟨retain P keep e (hk e),inclusion_retain P keep e (hk e)⟩⟩
  exact PomsetIso.ofEventEquiv (isIntervalPom P keep hP) hP E (fun _ => rfl) (fun _ _ => Iff.rfl)
    (fun _ _ => Iff.rfl) (fun e => (inSrc_iff P keep e).symm) (fun e => (inTgt_iff P keep e).symm)

end CounterFreeHDA.Deletion

namespace CounterFreeHDA.Appendix.Residual
open Cubical Compare

def deletionStatus (U : UCube) (D : Finset (Fin U.dim)) (i : Fin U.dim) : Status :=
  if i ∈ D then Status.zero else Status.star

noncomputable def deletionFace (U : UCube) (D : Finset (Fin U.dim)) :
    Cubical.Face (Cubical.Face.activeCube U (deletionStatus U D)) U := Cubical.Face.ofStatuses U (deletionStatus U D)

theorem deletionStatus_zero (U : UCube) (D : Finset (Fin U.dim)) (i : Fin U.dim) :
    deletionStatus U D i = Status.zero ↔ i ∈ D := by
  by_cases hi : i ∈ D <;> simp [deletionStatus,hi,Status.star,Status.zero]

theorem empty_source_compatible {U V : UCube} (P : Prefix U) (β : Cubical.Face V U) :
    P.toArrow.Compatible (Cubical.Face.ident Completion.emptyCube) β := by
  intro i
  exact Fin.elim0 i

/-- Delete exactly the named active target events from the actual prefix. -/
noncomputable def deletedPrefix {U : UCube} (P : Prefix U) (D : Finset (Fin U.dim)) :
    Prefix (Cubical.Face.activeCube U (deletionStatus U D)) :=
  P.toArrow.corner P.width (Cubical.Face.ident Completion.emptyCube) (deletionFace U D)
    (empty_source_compatible P (deletionFace U D))

def targetAt {U : UCube} (P : Prefix U) (i : Fin U.dim) : Fin P.pom.n :=
  P.pom.tgt (Fin.cast P.toArrow.tgt_len.symm i)

def targetKeep {U : UCube} (P : Prefix U) (D : Finset (Fin U.dim)) (e : Fin P.pom.n) : Prop :=
  ¬ ∃ i ∈ D, targetAt P i = e

instance targetKeepDecidable {U : UCube} (P : Prefix U) (D : Finset (Fin U.dim)) : DecidablePred (targetKeep P D) := by
  intro e
  unfold targetKeep
  infer_instance

theorem targetKeep_target {U : UCube} (P : Prefix U) (D : Finset (Fin U.dim)) (i : Fin U.dim) :
    targetKeep P D (targetAt P i) ↔ i ∉ D := by
  constructor
  · intro h hi
    exact h ⟨i,hi,rfl⟩
  · rintro hi ⟨j,hj,hji⟩
    have he := P.pom.val.tgt_inj hji
    have hv : j = i := Fin.ext (congrArg (fun x : Fin P.pom.tgtLen => x.val) he)
    exact hi (hv ▸ hj)

theorem target_deleted_iff {U : UCube} (P : Prefix U) (D : Finset (Fin U.dim)) (e : Fin P.pom.n) :
    Corners.Deleted P.pom.val
      (P.toArrow.sourceFace (Cubical.Face.ident Completion.emptyCube)).status
      (P.toArrow.targetFace (deletionFace U D)).status e ↔ ∃ i ∈ D, targetAt P i = e := by
  refine (Arrow.corner_deleted_iff P.toArrow (Cubical.Face.ident Completion.emptyCube) (deletionFace U D) e).trans ?_
  constructor
  · rintro (⟨i,_,_⟩ | ⟨i,hi,hs⟩)
    · exact Fin.elim0 i
    · have hD : i ∈ D := (deletionStatus_zero U D i).mp
        ((Cubical.Face.ofStatuses_status U (deletionStatus U D) i).symm.trans hs)
      exact ⟨i,hD,hi⟩
  · rintro ⟨i,hi,he⟩
    exact Or.inr ⟨i,he,(Cubical.Face.ofStatuses_status U (deletionStatus U D) i).trans
      ((deletionStatus_zero U D i).mpr hi)⟩

/-- The profile coordinate is actual induced event deletion with all
inherited interfaces; its description as a corner is proved, not assumed. -/
noncomputable def deletedPrefixIso {U : UCube} (P : Prefix U) (D : Finset (Fin U.dim)) :
    PomsetIso (deletedPrefix P D).pom.val (Deletion.data P.pom.val (targetKeep P D)) := by
  classical
  apply Corners.asDeletionIso P.pom.property
    (P.toArrow.sourceFace (Cubical.Face.ident Completion.emptyCube)).status
    (P.toArrow.targetFace (deletionFace U D)).status
    (P.toArrow.compatible_raw _ _ (empty_source_compatible P (deletionFace U D))) (targetKeep P D)
  · intro e
    exact (target_deleted_iff P D e).not
  · intro i
    exact Fin.elim0 (Fin.cast P.toArrow.src_len i)
  · intro i hi
    let j := Fin.cast P.toArrow.tgt_len i
    have hj : j ∉ D := (targetKeep_target P D j).mp
      (by simpa only [targetAt,j,Fin.cast_cast,Fin.cast_refl,id_eq] using hi)
    exact (Cubical.Face.ofStatuses_status U (deletionStatus U D) j).trans (by simp only [deletionStatus,if_neg hj])

abbrev Profile (U : UCube) := ∀ D : Finset (Fin U.dim), Kind (Cubical.Face.activeCube U (deletionStatus U D))

noncomputable def profile {U : UCube} (P : Prefix U) : Profile U :=
  fun D => wordKind (deletedPrefix P D).representative (0 : Fin 4)

/-- Every coordinate of the actual deletion profile denotes precisely the
canonical suffix residual of the actual prefix with those events removed. -/
theorem profile_semantics {U : UCube} (P : Prefix U) (D : Finset (Fin U.dim)) :
    residualLanguage (Cubical.Face.activeCube U (deletionStatus U D)) (profile P D) =
      prefixResidual (deletedPrefix P D) := (prefixResidual_classification (deletedPrefix P D)).symm

end CounterFreeHDA.Appendix.Residual
