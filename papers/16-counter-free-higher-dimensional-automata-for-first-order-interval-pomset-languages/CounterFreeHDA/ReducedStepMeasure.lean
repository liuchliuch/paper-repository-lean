import CounterFreeHDA.DeletionCorners
import CounterFreeHDA.EffectiveStepLabel

namespace CounterFreeHDA.Appendix.Residual
open Cubical Compare

def reducedDim (U : UCube) (D : Finset (Fin U.dim)) : ℕ := (Finset.univ.filter (fun i => i ∉ D)).card

theorem activeCube_deletion_dim (U : UCube) (D : Finset (Fin U.dim)) :
    (Cubical.Face.activeCube U (deletionStatus U D)).dim = reducedDim U D := by
  change (Finset.univ.filter (fun i => deletionStatus U D i = Status.star)).card = _
  congr 1
  ext i
  simp only [Finset.mem_filter,deletionStatus_star]

def keptEvents (B : Arrow U V) (D : Finset (Fin V.dim)) : ℕ :=
  (Finset.univ.filter (B.keepTargetEvents D)).card

theorem deletedArrow_size (B : BoundedArrow U V) (D : Finset (Fin V.dim)) :
    (deletedArrow B D).pom.n = keptEvents B.toArrow D := by
  have hc := Fintype.card_congr (deletedArrowIso B D).toEquiv
  simp only [Fintype.card_fin] at hc
  change (deletedArrow B D).pom.n = Fintype.card {e : Fin B.pom.n // B.toArrow.keepTargetEvents D e} at hc
  exact hc.trans (Fintype.card_subtype _)

theorem deletedArrow_measure (B : BoundedArrow U V) (D : Finset (Fin V.dim)) :
    stMeasure (deletedArrow B D).pom.val =
      2 * keptEvents B.toArrow D - reducedDim U (B.toArrow.pullTargetDeletion D) - reducedDim V D := by
  change 2 * (deletedArrow B D).pom.n - (deletedArrow B D).pom.srcLen - (deletedArrow B D).pom.tgtLen = _
  rw [deletedArrow_size,(deletedArrow B D).toArrow.src_len,(deletedArrow B D).toArrow.tgt_len,
    activeCube_deletion_dim,activeCube_deletion_dim]

attribute [local instance] Effective.faceFintype Effective.faceDecidableEq Effective.lowerDecidable Effective.upperDecidable
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

/-- Removing active target events from one elementary start leaves either
an identity or one elementary start, as witnessed by the exact ST measure. -/
theorem reduced_start_measure : ∀ (U V : UCube) (f : Cubical.Face U V) (hl : f.Lower) (hd : V.dim = U.dim+1),
    ∀ D : Finset (Fin V.dim),
      2 * keptEvents (Effective.stepLabel (Step.start f hl hd)) D -
        reducedDim U ((Effective.stepLabel (Step.start f hl hd)).pullTargetDeletion D) - reducedDim V D =
      reducedDim V D - reducedDim U ((Effective.stepLabel (Step.start f hl hd)).pullTargetDeletion D) ∧
      reducedDim U ((Effective.stepLabel (Step.start f hl hd)).pullTargetDeletion D) ≤ reducedDim V D ∧
      reducedDim V D ≤ reducedDim U ((Effective.stepLabel (Step.start f hl hd)).pullTargetDeletion D)+1 := by
  let dec : Decidable (∀ (U V : UCube) (f : Cubical.Face U V) (hl : f.Lower) (hd : V.dim = U.dim+1),
    ∀ D : Finset (Fin V.dim),
      2 * keptEvents (Effective.stepLabel (Step.start f hl hd)) D - reducedDim U ((Effective.stepLabel (Step.start f hl hd)).pullTargetDeletion D) - reducedDim V D =
        reducedDim V D - reducedDim U ((Effective.stepLabel (Step.start f hl hd)).pullTargetDeletion D) ∧
      reducedDim U ((Effective.stepLabel (Step.start f hl hd)).pullTargetDeletion D) ≤ reducedDim V D ∧
      reducedDim V D ≤ reducedDim U ((Effective.stepLabel (Step.start f hl hd)).pullTargetDeletion D)+1) := by
    refine @Fintype.decidableForallFintype _ _ (fun U => ?_) inferInstance
    refine @Fintype.decidableForallFintype _ _ (fun V => ?_) inferInstance
    refine @Fintype.decidableForallFintype _ _ (fun f => ?_) (Effective.faceFintype U V)
    infer_instance
  exact of_decide_eq_true (by rfl : @decide _ dec = true)

theorem reduced_stop_measure : ∀ (U V : UCube) (f : Cubical.Face U V) (hu : f.Upper) (hd : V.dim = U.dim+1),
    ∀ D : Finset (Fin U.dim),
      2 * keptEvents (Effective.stepLabel (Step.stop f hu hd)) D - reducedDim V ((Effective.stepLabel (Step.stop f hu hd)).pullTargetDeletion D) - reducedDim U D = 1 ∧
      reducedDim V ((Effective.stepLabel (Step.stop f hu hd)).pullTargetDeletion D) = reducedDim U D+1 := by
  let dec : Decidable (∀ (U V : UCube) (f : Cubical.Face U V) (hu : f.Upper) (hd : V.dim = U.dim+1),
    ∀ D : Finset (Fin U.dim),
      2 * keptEvents (Effective.stepLabel (Step.stop f hu hd)) D - reducedDim V ((Effective.stepLabel (Step.stop f hu hd)).pullTargetDeletion D) - reducedDim U D = 1 ∧
      reducedDim V ((Effective.stepLabel (Step.stop f hu hd)).pullTargetDeletion D) = reducedDim U D+1) := by
    refine @Fintype.decidableForallFintype _ _ (fun U => ?_) inferInstance
    refine @Fintype.decidableForallFintype _ _ (fun V => ?_) inferInstance
    refine @Fintype.decidableForallFintype _ _ (fun f => ?_) (Effective.faceFintype U V)
    infer_instance
  exact of_decide_eq_true (by rfl : @decide _ dec = true)

end CounterFreeHDA.Appendix.Residual
