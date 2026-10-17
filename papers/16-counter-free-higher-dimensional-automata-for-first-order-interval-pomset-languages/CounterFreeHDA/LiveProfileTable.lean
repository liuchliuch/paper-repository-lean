import CounterFreeHDA.ProfileCodes

namespace CounterFreeHDA.Appendix.Residual
open Cubical Compare

def templateCode (U : UCube) (i : Fin (Completion.profileSize U.1)) : Code U := fun D =>
  match U.1,i with
  | ⟨0,_⟩,i => ⟨i.val,by have hi := i.isLt; change i.val < 3 at hi; omega⟩
  | ⟨1,_⟩,i => if D = ∅ then ![0,1,2,2] i else ![0,1,1,2] i
  | ⟨2,_⟩,i => if D = ∅ then ![0,1,1] i else if D.card = 1 then ![0,2,2] i else ![0,1,2] i
  | ⟨n+3,h⟩,_ => False.elim (by omega)

def liveCode (U : UCube) (c : Code U) : Prop := c ∅ ≠ embedKind (dead U.1)

instance liveCodeDecidable (U : UCube) (c : Code U) : Decidable (liveCode U c) := inferInstanceAs (Decidable (c ∅ ≠ embedKind (dead U.1)))

attribute [local instance] Effective.faceFintype Effective.faceDecidableEq Effective.lowerDecidable Effective.upperDecidable
set_option maxRecDepth 30000
set_option maxHeartbeats 12000000

theorem templateCode_injective : ∀ U : UCube, Function.Injective (templateCode U) := by unfold Function.Injective; decide

theorem templateCode_live : ∀ (U : UCube) (i : Fin (Completion.profileSize U.1)), liveCode U (templateCode U i) := by decide

theorem update_start_live : ∀ (U V : UCube) (f : Cubical.Face U V) (hl : f.Lower) (hd : V.dim = U.dim+1)
    (i : Fin (Completion.profileSize U.1)),
    liveCode V (updateCode (.start f hl hd) (templateCode U i)) →
      ∃ j : Fin (Completion.profileSize V.1), updateCode (.start f hl hd) (templateCode U i) = templateCode V j := by
  let dec : Decidable (∀ (U V : UCube) (f : Cubical.Face U V) (hl : f.Lower) (hd : V.dim = U.dim+1)
      (i : Fin (Completion.profileSize U.1)),
      liveCode V (updateCode (.start f hl hd) (templateCode U i)) →
        ∃ j : Fin (Completion.profileSize V.1), updateCode (.start f hl hd) (templateCode U i) = templateCode V j) := by
    refine @Fintype.decidableForallFintype _ _ (fun U => ?_) inferInstance
    refine @Fintype.decidableForallFintype _ _ (fun V => ?_) inferInstance
    refine @Fintype.decidableForallFintype _ _ (fun f => ?_) (Effective.faceFintype U V)
    infer_instance
  exact of_decide_eq_true (by rfl : @decide _ dec = true)

theorem update_stop_live : ∀ (U V : UCube) (f : Cubical.Face U V) (hu : f.Upper) (hd : V.dim = U.dim+1)
    (i : Fin (Completion.profileSize V.1)),
      ∃ j : Fin (Completion.profileSize U.1), updateCode (.stop f hu hd) (templateCode V i) = templateCode U j := by
  let dec : Decidable (∀ (U V : UCube) (f : Cubical.Face U V) (hu : f.Upper) (hd : V.dim = U.dim+1)
      (i : Fin (Completion.profileSize V.1)),
        ∃ j : Fin (Completion.profileSize U.1), updateCode (.stop f hu hd) (templateCode V i) = templateCode U j) := by
    refine @Fintype.decidableForallFintype _ _ (fun U => ?_) inferInstance
    refine @Fintype.decidableForallFintype _ _ (fun V => ?_) inferInstance
    refine @Fintype.decidableForallFintype _ _ (fun f => ?_) (Effective.faceFintype U V)
    infer_instance
  exact of_decide_eq_true (by rfl : @decide _ dec = true)

theorem pull_empty {U V : UCube} (B : Arrow U V) : B.pullTargetDeletion ∅ = ∅ := by
  ext i
  simp only [Arrow.pullTargetDeletion,Finset.mem_filter,Finset.mem_univ,Finset.notMem_empty,false_and,exists_false,and_false]

theorem update_empty {U V : UCube} (s : Step U V) (c : Code U) :
    updateCode s c ∅ = codeTransition U.dim V.dim (c ∅) := by
  simp only [updateCode,pull_empty]
  have h : ∀ U : UCube, reducedDim U ∅ = U.dim := by
    intro U
    simp only [reducedDim,Finset.notMem_empty,not_false_eq_true,Finset.filter_true,Finset.card_univ,Fintype.card_fin]
  rw [h,h]

theorem code_dead_step {U V : UCube} (s : Step U V) :
    codeTransition U.dim V.dim (embedKind (dead U.1)) = embedKind (dead V.1) := by
  have h : ∀ (U V : UCube) (f : Cubical.Face U V) (hl : f.Lower) (hd : V.dim = U.dim+1),
      codeTransition U.dim V.dim (embedKind (dead U.1)) = embedKind (dead V.1) ∧
      codeTransition V.dim U.dim (embedKind (dead V.1)) = embedKind (dead U.1) := by
    let dec : Decidable (∀ (U V : UCube) (f : Cubical.Face U V) (hl : f.Lower) (hd : V.dim = U.dim+1),
        codeTransition U.dim V.dim (embedKind (dead U.1)) = embedKind (dead V.1) ∧
        codeTransition V.dim U.dim (embedKind (dead V.1)) = embedKind (dead U.1)) := by
      refine @Fintype.decidableForallFintype _ _ (fun U => ?_) inferInstance
      refine @Fintype.decidableForallFintype _ _ (fun V => ?_) inferInstance
      refine @Fintype.decidableForallFintype _ _ (fun f => ?_) (Effective.faceFintype U V)
      infer_instance
    exact of_decide_eq_true (by rfl : @decide _ dec = true)
  cases s with
  | start f hl hd => exact (h _ _ f hl hd).1
  | stop f hu hd =>
    let g := Cubical.Face.ofEmbedding f.positionEmbedding (fun i => f.labels (f.position_spec i)) false
    exact (h _ _ g (Cubical.Face.ofEmbedding_lower _ _) hd).2

def executeCode : {U V : UCube} → Word U V → Code U → Code V
  | _,_,.nil _,c => c
  | _,_,.cons s p,c => executeCode p (updateCode s c)

/-- Dead prefixes remain dead; every live prefix extension has one of the
ten displayed profile tuples, in every actual event position. -/
theorem execute_templates {U V : UCube} (p : Word U V) (c : Code U)
    (hc : ¬ liveCode U c ∨ ∃ i, c = templateCode U i) :
    ¬ liveCode V (executeCode p c) ∨ ∃ j, executeCode p c = templateCode V j := by
  induction p with
  | nil => exact hc
  | cons s p ih =>
    apply ih
    rcases hc with hc | ⟨i,rfl⟩
    · left
      unfold liveCode at *
      push_neg at hc ⊢
      rw [update_empty,hc,code_dead_step s]
    · cases s with
      | start f hl hd =>
        by_cases h : liveCode _ (updateCode (.start f hl hd) (templateCode _ i))
        · exact Or.inr (update_start_live _ _ f hl hd i h)
        · exact Or.inl h
      | stop f hu hd => exact Or.inr (update_stop_live _ _ f hu hd i)

end CounterFreeHDA.Appendix.Residual
