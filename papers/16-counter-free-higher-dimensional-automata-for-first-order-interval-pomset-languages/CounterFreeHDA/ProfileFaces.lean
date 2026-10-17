import CounterFreeHDA.LiveProfiles

namespace CounterFreeHDA.Appendix.Residual
open Cubical Compare

def lowerDeleted {U V : UCube} (f : Cubical.Face U V) (D : Finset (Fin U.dim)) : Finset (Fin V.dim) :=
  Finset.univ.filter (fun j => f.sub j = Sum.inr false ∨ ∃ i ∈ D, f.sub j = Sum.inl i)

def lowerCode {U V : UCube} (f : Cubical.Face U V) (c : Code V) : Code U := fun D => c (lowerDeleted f D)

attribute [local instance] Effective.faceFintype Effective.faceDecidableEq Effective.lowerDecidable Effective.upperDecidable
set_option maxRecDepth 40000
set_option maxHeartbeats 12000000

/-- Lower profile faces are coordinate restrictions, and on the exhaustive
live tuples they are exactly the displayed completion's actual lower faces. -/
theorem lower_profile_faces : ∀ (U V : UCube) (f : Cubical.Face U V) (hf : f.Lower)
    (i : Fin (Completion.profileSize V.1)), ∃ j : Fin (Completion.profileSize U.1),
      lowerCode f (templateCode V i) = templateCode U j ∧
      Completion.completionHDA.face f (Completion.indexCell V i) = Completion.indexCell U j := by
  let dec : Decidable (∀ (U V : UCube) (f : Cubical.Face U V) (hf : f.Lower)
      (i : Fin (Completion.profileSize V.1)), ∃ j : Fin (Completion.profileSize U.1),
        lowerCode f (templateCode V i) = templateCode U j ∧
        Completion.completionHDA.face f (Completion.indexCell V i) = Completion.indexCell U j) := by
    refine @Fintype.decidableForallFintype _ _ (fun U => ?_) inferInstance
    refine @Fintype.decidableForallFintype _ _ (fun V => ?_) inferInstance
    refine @Fintype.decidableForallFintype _ _ (fun f => ?_) (Effective.faceFintype U V)
    infer_instance
  exact of_decide_eq_true (by rfl : @decide _ dec = true)

/-- Upper profile faces are actual termination updates and agree with every
elementary upper face of the concrete completion HDA. -/
theorem upper_profile_faces : ∀ (U V : UCube) (f : Cubical.Face U V) (hf : f.Upper) (hd : V.dim = U.dim+1)
    (i : Fin (Completion.profileSize V.1)), ∃ j : Fin (Completion.profileSize U.1),
      updateCode (.stop f hf hd) (templateCode V i) = templateCode U j ∧
      Completion.completionHDA.face f (Completion.indexCell V i) = Completion.indexCell U j := by
  let dec : Decidable (∀ (U V : UCube) (f : Cubical.Face U V) (hf : f.Upper) (hd : V.dim = U.dim+1)
      (i : Fin (Completion.profileSize V.1)), ∃ j : Fin (Completion.profileSize U.1),
        updateCode (.stop f hf hd) (templateCode V i) = templateCode U j ∧
        Completion.completionHDA.face f (Completion.indexCell V i) = Completion.indexCell U j) := by
    refine @Fintype.decidableForallFintype _ _ (fun U => ?_) inferInstance
    refine @Fintype.decidableForallFintype _ _ (fun V => ?_) inferInstance
    refine @Fintype.decidableForallFintype _ _ (fun f => ?_) (Effective.faceFintype U V)
    infer_instance
  exact of_decide_eq_true (by rfl : @decide _ dec = true)

def ActualProfile (U : UCube) := {c : Code U // ∃ P : Prefix U, profileCode P = c}

/-- Full canonical profile reachability includes every actual prefix profile,
including all dead profiles; starts use lower-coordinate restriction and stops
use the proved actual prefix-extension update. -/
inductive FullProfileRun : {U V : UCube} → Word U V → ActualProfile U → ActualProfile V → Prop where
  | nil {U} (x : ActualProfile U) : FullProfileRun (.nil U) x x
  | start {U V W} (f : Cubical.Face U V) (hf : f.Lower) (hd : V.dim = U.dim+1)
      {p : Word V W} {x : ActualProfile U} {z : ActualProfile V} {y : ActualProfile W} :
      x.val = lowerCode f z.val → FullProfileRun p z y → FullProfileRun (.cons (.start f hf hd) p) x y
  | stop {U V W} (f : Cubical.Face V U) (hf : f.Upper) (hd : U.dim = V.dim+1)
      {p : Word V W} {x : ActualProfile U} {z : ActualProfile V} {y : ActualProfile W} :
      z.val = updateCode (.stop f hf hd) x.val → FullProfileRun p z y → FullProfileRun (.cons (.stop f hf hd) p) x y

/-- A dead profile cannot return to the live sub-HDA, even when every
actual dead deletion profile is retained in the full completion. -/
theorem dead_no_return {U V : UCube} {p : Word U V} {x : ActualProfile U} {y : ActualProfile V}
    (h : FullProfileRun p x y) (hx : ¬ liveCode U x.val) : ¬ liveCode V y.val := by
  induction h with
  | nil => exact hx
  | @start U V W f hf hd p x z y he hr ih =>
    apply ih
    intro hz
    obtain ⟨P,hP⟩ := z.property
    obtain ⟨i,hi⟩ := live_profile_exhaustive P (hP.symm ▸ hz)
    obtain ⟨j,hj,_⟩ := lower_profile_faces U V f hf i
    apply hx
    have hxt : x.val = templateCode U j := he.trans (by rw [← hP,hi]; exact hj)
    rw [hxt]
    exact templateCode_live U j
  | @stop U V W f hf hd p x z y he hr ih =>
    apply ih
    unfold liveCode at hx ⊢
    push_neg at hx ⊢
    rw [he,update_empty,hx,code_dead_step (.stop f hf hd)]

end CounterFreeHDA.Appendix.Residual
