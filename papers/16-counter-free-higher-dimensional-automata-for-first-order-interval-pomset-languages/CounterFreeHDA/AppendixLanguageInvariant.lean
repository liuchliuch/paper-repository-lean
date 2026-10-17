import CounterFreeHDA.CompletionRelations

namespace CounterFreeHDA.Appendix.Compare
open Cubical
abbrev UCube := Cube Unit 2
abbrev Subset (n : ℕ) := Fin n → Bool

def mask (n b : ℕ) : Subset n := fun i => b.testBit i.val

def action (r : BRel n m) (x : Subset n) : Subset m := fun j => decide (∃ i, x i = true ∧ r i j = true)

def invariantTable : (a : Fin 3) → Finset (Subset (size a) × Subset (Completion.profileSize a))
  | ⟨0,_⟩ => {(mask 2 0,mask 3 0),(mask 2 1,mask 3 1),(mask 2 2,mask 3 2),
      (mask 2 3,mask 3 4),(mask 2 3,mask 3 5),(mask 2 3,mask 3 6)}
  | ⟨1,_⟩ => {(mask 3 0,mask 4 0),(mask 3 1,mask 4 1),(mask 3 2,mask 4 2),
      (mask 3 6,mask 4 6),(mask 3 6,mask 4 8),(mask 3 6,mask 4 10),
      (mask 3 7,mask 4 8),(mask 3 7,mask 4 9),(mask 3 7,mask 4 14)}
  | ⟨2,_⟩ => {(mask 3 0,mask 3 0),(mask 3 1,mask 3 1),(mask 3 6,mask 3 2),
      (mask 3 6,mask 3 4),(mask 3 7,mask 3 4),(mask 3 7,mask 3 5),(mask 3 7,mask 3 6)}
  | ⟨n+3,h⟩ => False.elim (by omega)

def Invariant (U : UCube) (x : Subset (size U.1)) (y : Subset (Completion.profileSize U.1)) : Prop :=
  (x,y) ∈ invariantTable U.1

instance invariantDecidable (U : UCube) (x : Subset (size U.1)) (y : Subset (Completion.profileSize U.1)) :
    Decidable (Invariant U x y) := inferInstanceAs (Decidable ((x,y) ∈ invariantTable U.1))

instance originalEmptySizeNeZero : NeZero (size Completion.emptyCube.1) := by
  change NeZero 2
  infer_instance
instance completedEmptySizeNeZero : NeZero (Completion.profileSize Completion.emptyCube.1) := by
  change NeZero 3
  infer_instance

attribute [local instance] Effective.faceFintype Effective.faceDecidableEq Effective.lowerDecidable Effective.upperDecidable
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

/-- Exhaustively verify the 22 reachable subset pairs against the actual
lower face maps at both possible event positions. -/
theorem start_invariant : ∀ (U V : UCube) (f : Cubical.Face U V), f.Lower → V.dim = U.dim+1 →
    ∀ x y, Invariant U x y → Invariant V (action (Actual.startRel f) x) (action (Completion.startRel f) y) := by
  let dec : Decidable (∀ (U V : UCube) (f : Cubical.Face U V), f.Lower → V.dim = U.dim+1 →
      ∀ x y, Invariant U x y → Invariant V (action (Actual.startRel f) x) (action (Completion.startRel f) y)) := by
    refine @Fintype.decidableForallFintype _ _ (fun U => ?_) inferInstance
    refine @Fintype.decidableForallFintype _ _ (fun V => ?_) inferInstance
    refine @Fintype.decidableForallFintype _ _ (fun f => ?_) (Effective.faceFintype U V)
    infer_instance
  exact of_decide_eq_true (by rfl : @decide _ dec = true)

/-- The same finite invariant is closed under every actual upper face. -/
theorem stop_invariant : ∀ (U V : UCube) (f : Cubical.Face U V), f.Upper → V.dim = U.dim+1 →
    ∀ x y, Invariant V x y → Invariant U (action (Actual.stopRel f) x) (action (Completion.stopRel f) y) := by
  let dec : Decidable (∀ (U V : UCube) (f : Cubical.Face U V), f.Upper → V.dim = U.dim+1 →
      ∀ x y, Invariant V x y → Invariant U (action (Actual.stopRel f) x) (action (Completion.stopRel f) y)) := by
    refine @Fintype.decidableForallFintype _ _ (fun U => ?_) inferInstance
    refine @Fintype.decidableForallFintype _ _ (fun V => ?_) inferInstance
    refine @Fintype.decidableForallFintype _ _ (fun f => ?_) (Effective.faceFintype U V)
    infer_instance
  exact of_decide_eq_true (by rfl : @decide _ dec = true)

def originalExecute : {U V : UCube} → Word U V → Subset (size U.1) → Subset (size V.1)
  | _,_,.nil _,x => x
  | _,_,.cons s p,x => originalExecute p (action (Actual.stepRel s) x)

def completedExecute : {U V : UCube} → Word U V → Subset (Completion.profileSize U.1) → Subset (Completion.profileSize V.1)
  | _,_,.nil _,x => x
  | _,_,.cons s p,x => completedExecute p (action (Completion.stepRel s) x)

theorem execute_invariant {U V : UCube} (p : Word U V) (x : Subset (size U.1))
    (y : Subset (Completion.profileSize U.1)) (h : Invariant U x y) :
    Invariant V (originalExecute p x) (completedExecute p y) := by
  induction p with
  | nil U => exact h
  | cons s p ih =>
    apply ih
    cases s with
    | start f hl hd => exact start_invariant _ _ f hl hd x y h
    | stop f hu hd => exact stop_invariant _ _ f hu hd x y h

theorem initial_invariant : Invariant Completion.emptyCube (mask 2 1) (mask 3 1) := by decide

theorem accepting_invariant : ∀ (x : Subset 2) (y : Subset 3), Invariant Completion.emptyCube x y →
    (x 0 = true ↔ y 0 = true ∨ y 2 = true) := by decide

end CounterFreeHDA.Appendix.Compare
