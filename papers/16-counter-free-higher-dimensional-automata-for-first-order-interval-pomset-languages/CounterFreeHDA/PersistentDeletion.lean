import CounterFreeHDA.GluingDeletion
import CounterFreeHDA.EndoSurvival

namespace CounterFreeHDA.EndoPom
universe u
open Cubical Cubical.TrackGlue
variable {Lab : Type u} {k : ℕ} {U : Cube Lab k}

def PersistentSet (P : EndoPom (cubeInterface U)) (R : Finset (Fin U.dim)) : Prop :=
  ∀ i ∈ R, P.Shared i i

/-- Persistent positions survive every actual power, including exponent 0. -/
theorem persistent_pow (P : EndoPom (cubeInterface U)) (n : ℕ) (i : Fin U.dim) (hi : P.Shared i i) :
    (P.pow n).Shared i i := by
  induction n with
  | zero => rfl
  | succ n ih => exact (shared_mul (P.pow n) P i i).mpr ⟨i,ih,hi⟩

def keep (P : EndoPom (cubeInterface U)) (R : Finset (Fin U.dim)) (e : Fin P.pom.n) : Prop :=
  ¬ ∃ i ∈ R, P.pom.src (Fin.cast P.src_len.symm i) = e

noncomputable def deleteData (P : EndoPom (cubeInterface U)) (R : Finset (Fin U.dim)) : PomsetData Lab := by
  classical
  exact Deletion.data P.pom.val (keep P R)

noncomputable def powerMatch (P : EndoPom (cubeInterface U)) (n : ℕ) :
    GlueMatch (P.pow n).pom.val P.pom.val := GlueMatch.ofType ((P.pow n).target.trans P.source.symm)

theorem power_source_left (P : EndoPom (cubeInterface U)) (n : ℕ) (i : Fin U.dim) :
    leftEvent (P.powerMatch n) ((P.pow n).pom.src (Fin.cast (P.pow n).src_len.symm i)) =
      (P.pow (n+1)).pom.src (Fin.cast (P.pow (n+1)).src_len.symm i) := by
  exact congrArg (fun j => leftEvent (P.powerMatch n) ((P.pow n).pom.src j)) (Fin.ext rfl)

theorem power_source_right (P : EndoPom (cubeInterface U)) (n : ℕ) (i : Fin U.dim)
    (hi : P.Shared i i) :
    (P.pow (n+1)).pom.src (Fin.cast (P.pow (n+1)).src_len.symm i) =
      rightEvent (P.powerMatch n) (P.pom.src (Fin.cast P.src_len.symm i)) := by
  calc
    _ = leftEvent (P.powerMatch n) ((P.pow n).pom.src (Fin.cast (P.pow n).src_len.symm i)) := (P.power_source_left n i).symm
    _ = leftEvent (P.powerMatch n) ((P.pow n).pom.tgt (Fin.cast (P.pow n).tgt_len.symm i)) :=
      congrArg (leftEvent (P.powerMatch n)) (P.persistent_pow n i hi)
    _ = rightEvent (P.powerMatch n) (P.pom.src
        (Fin.cast (P.powerMatch n).len_eq (Fin.cast (P.pow n).tgt_len.symm i))) :=
      congrArg (index (P.powerMatch n)) (GluedE.identified (P.pow n).pom.val P.pom.val _ _)
    _ = _ := congrArg (fun j => rightEvent (P.powerMatch n) (P.pom.src j)) (Fin.ext rfl)

/-- The actual deletion predicate restricts identically to the prefix power
and the next copy of P. This is where persistent interface survival is used. -/
noncomputable def powerDeletionPlan (P : EndoPom (cubeInterface U)) (R : Finset (Fin U.dim))
    (hR : P.PersistentSet R) (n : ℕ) : Deletion.Plan (P.powerMatch n) := by
  classical
  exact {
    keepA := keep (P.pow n) R
    keepB := keep P R
    keepG := keep (P.pow (n+1)) R
    left_iff e := by
      apply not_congr
      constructor
      · rintro ⟨i,hi,he⟩
        refine ⟨i,hi,(index (P.powerMatch n)).injective.comp (GluedE.leftMap_inj _ _) ?_⟩
        exact (P.power_source_left n i).trans he
      · rintro ⟨i,hi,he⟩
        exact ⟨i,hi,(P.power_source_left n i).symm.trans (congrArg (leftEvent (P.powerMatch n)) he)⟩
    right_iff e := by
      apply not_congr
      constructor
      · rintro ⟨i,hi,he⟩
        refine ⟨i,hi,((index (P.powerMatch n)).injective.comp (GluedE.rightMap_inj (P.pow n).pom.val P.pom.val (P.powerMatch n).len_eq)) ?_⟩
        exact (P.power_source_right n i (hR i hi)).symm.trans he
      · rintro ⟨i,hi,he⟩
        exact ⟨i,hi,(P.power_source_right n i (hR i hi)).trans (congrArg (rightEvent (P.powerMatch n)) he)⟩ }

/-- Genuine one-step commutation of persistent deletion with actual powers. -/
noncomputable def deletionPowerStepIso (P : EndoPom (cubeInterface U)) (R : Finset (Fin U.dim))
    (hR : P.PersistentSet R) (n : ℕ) :
    PomsetIso (glueData (deleteData (P.pow n) R) (deleteData P R) (P.powerDeletionPlan R hR n).glueMatch)
      (deleteData (P.pow (n+1)) R) :=
  (P.powerDeletionPlan R hR n).iso (P.pow n).pom.property P.pom.property

end CounterFreeHDA.EndoPom
