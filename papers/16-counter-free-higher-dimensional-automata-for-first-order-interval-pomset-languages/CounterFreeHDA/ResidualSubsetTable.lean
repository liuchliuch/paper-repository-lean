import CounterFreeHDA.ResidualSemantics

namespace CounterFreeHDA.Appendix.Residual
open Cubical Compare

def residualSize : Fin 3 → ℕ := ![4,4,3]
instance residualSizeNeZero (a : Fin 3) : NeZero (residualSize a) := ⟨by fin_cases a <;> decide⟩
abbrev Kind (U : UCube) := Fin (residualSize U.1)

def subsetClasses : (a : Fin 3) → Finset (Subset (size a) × Fin (residualSize a))
  | ⟨0,_⟩ => {(mask 2 1,0),(mask 2 2,1),(mask 2 3,2),(mask 2 0,3)}
  | ⟨1,_⟩ => {(mask 3 1,0),(mask 3 2,1),(mask 3 6,2),(mask 3 7,2),(mask 3 0,3)}
  | ⟨2,_⟩ => {(mask 3 1,0),(mask 3 6,1),(mask 3 7,1),(mask 3 0,2)}
  | ⟨n+3,h⟩ => False.elim (by omega)

def Represents (U : UCube) (x : Subset (size U.1)) (r : Kind U) : Prop := (x,r) ∈ subsetClasses U.1
instance representsDecidable (U : UCube) (x : Subset (size U.1)) (r : Kind U) : Decidable (Represents U x r) :=
  inferInstanceAs (Decidable ((x,r) ∈ subsetClasses U.1))

def representative : (a : Fin 3) → Fin (residualSize a) → Subset (size a)
  | ⟨0,_⟩ => ![mask 2 1,mask 2 2,mask 2 3,mask 2 0]
  | ⟨1,_⟩ => ![mask 3 1,mask 3 2,mask 3 6,mask 3 0]
  | ⟨2,_⟩ => ![mask 3 1,mask 3 6,mask 3 0]
  | ⟨n+3,h⟩ => False.elim (by omega)

def startKind : (a b : Fin 3) → Fin (residualSize a) → Fin (residualSize b)
  | ⟨0,_⟩,⟨1,_⟩ => ![0,2,2,3]
  | ⟨1,_⟩,⟨2,_⟩ => ![0,2,1,2]
  | _,b => fun _ => 0

def stopKind : (a b : Fin 3) → Fin (residualSize a) → Fin (residualSize b)
  | ⟨1,_⟩,⟨0,_⟩ => ![1,0,2,3]
  | ⟨2,_⟩,⟨1,_⟩ => ![1,2,3]
  | _,b => fun _ => 0

def stepKind : {U V : UCube} → Step U V → Kind U → Kind V
  | U,V,.start _ _ _ => startKind U.1 V.1
  | U,V,.stop _ _ _ => stopKind U.1 V.1

attribute [local instance] Effective.faceFintype Effective.faceDecidableEq Effective.lowerDecidable Effective.upperDecidable
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

/-- The semantic residual classes and their elementary start action are
verified against actual lower face maps, including both event positions. -/
theorem represents_start : ∀ (U V : UCube) (f : Cubical.Face U V), f.Lower → V.dim = U.dim+1 →
    ∀ x r, Represents U x r → Represents V (action (Actual.startRel f) x) (startKind U.1 V.1 r) := by
  let dec : Decidable (∀ (U V : UCube) (f : Cubical.Face U V), f.Lower → V.dim = U.dim+1 →
      ∀ x r, Represents U x r → Represents V (action (Actual.startRel f) x) (startKind U.1 V.1 r)) := by
    refine @Fintype.decidableForallFintype _ _ (fun U => ?_) inferInstance
    refine @Fintype.decidableForallFintype _ _ (fun V => ?_) inferInstance
    refine @Fintype.decidableForallFintype _ _ (fun f => ?_) (Effective.faceFintype U V)
    infer_instance
  exact of_decide_eq_true (by rfl : @decide _ dec = true)

theorem represents_stop : ∀ (U V : UCube) (f : Cubical.Face U V), f.Upper → V.dim = U.dim+1 →
    ∀ x r, Represents V x r → Represents U (action (Actual.stopRel f) x) (stopKind V.1 U.1 r) := by
  let dec : Decidable (∀ (U V : UCube) (f : Cubical.Face U V), f.Upper → V.dim = U.dim+1 →
      ∀ x r, Represents V x r → Represents U (action (Actual.stopRel f) x) (stopKind V.1 U.1 r)) := by
    refine @Fintype.decidableForallFintype _ _ (fun U => ?_) inferInstance
    refine @Fintype.decidableForallFintype _ _ (fun V => ?_) inferInstance
    refine @Fintype.decidableForallFintype _ _ (fun f => ?_) (Effective.faceFintype U V)
    infer_instance
  exact of_decide_eq_true (by rfl : @decide _ dec = true)

def wordKind : {U V : UCube} → Word U V → Kind U → Kind V
  | _,_,.nil _,r => r
  | _,_,.cons s p,r => wordKind p (stepKind s r)

theorem execute_represents {U V : UCube} (p : Word U V) (x : Subset (size U.1)) (r : Kind U)
    (h : Represents U x r) : Represents V (originalExecute p x) (wordKind p r) := by
  induction p with
  | nil U => exact h
  | cons s p ih =>
    apply ih
    cases s with
    | start f hl hd => exact represents_start _ _ f hl hd x r h
    | stop f hu hd => exact represents_stop _ _ f hu hd x r h

theorem representative_represents : ∀ (U : UCube) (r : Kind U), Represents U (representative U.1 r) r := by decide

theorem represents_initial : Represents Completion.emptyCube (mask 2 1) (0 : Fin 4) := by decide

theorem represents_acceptance : ∀ (x : Subset 2) (r : Fin 4), Represents Completion.emptyCube x r →
    (x 0 = true ↔ r = 0 ∨ r = 2) := by decide

end CounterFreeHDA.Appendix.Residual
