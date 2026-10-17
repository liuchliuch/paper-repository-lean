import Paper37.CachedOperations
import Paper37.CachedQueries

/-! A concrete arithmetic/load interpreter for the cached occupied-type DP.
It certifies the actual summands and their finite fifth-degree schedule. -/
namespace Paper37.CachedRefinedOperations
open Finset Paper37.DP Paper37.Envelope Paper37.ContinuationDP
open Paper37.AdaptiveDP Paper37.RefinedContinuation Paper37.CachedDP
open Paper37.CachedRefinedDP

abbrev Index := Paper37.CachedOperations.Index

/-- The occupied-coordinate address computes its increment explicitly. -/
inductive OccupiedAddress where
  | lit : ℕ → OccupiedAddress
  | epsilon : ℕ → ℕ → OccupiedAddress
  | sub : OccupiedAddress → OccupiedAddress → OccupiedAddress

def OccupiedAddress.eval : OccupiedAddress → ℕ
  | .lit n => n
  | .epsilon a b => if 0<a+b then 1 else 0
  | .sub a b => a.eval-b.eval

def OccupiedAddress.work : OccupiedAddress → ℕ
  | .lit _ => 0
  | .epsilon _ _ => 3
  | .sub a b => a.work+b.work+1

/-- Indexed scalar instructions, including the feasibility tests in E.5/E.6. -/
inductive Instruction (N : ℕ) where
  | feasible : ℕ → ℕ → ℕ → ℕ → ℕ → Instruction N
  | choose : Fin (N+1) → Index → Instruction N
  | power : Index → Instruction N
  | unmarked : Index → Index → OccupiedAddress → Instruction N
  | marked : Index → Index → OccupiedAddress → Instruction N
  | gate : ℕ → ℕ → ℕ → Instruction N
  | add : Instruction N
  | mul : Instruction N

def Instruction.work {N : ℕ} : Instruction N → ℕ
  | .feasible _ _ _ _ _ => 6
  | .choose _ b => b.work+3
  | .power v => v.work+3
  | .unmarked k u j | .marked k u j => k.work+u.work+j.work+4
  | .gate _ _ _ => 2
  | .add | .mul => 1

def Instruction.exec {N : ℕ} (c : Cache N) (old : RefinedLayer N) : Instruction N → List ℕ → List ℕ
  | .feasible ad d b u j, st => (if d*b≤u ∧ (if 0<ad+b then 1 else 0)≤j then 1 else 0)::st
  | .choose k b, st => chooseAt c k b.eval::st
  | .power v, st => powerAt c v.eval::st
  | .unmarked k u j, st => (refinedLayerAt old k.eval u.eval j.eval).1::st
  | .marked k u j, st => (refinedLayerAt old k.eval u.eval j.eval).2::st
  | .gate A d b, st => (if A<d then b else 0)::st
  | .add, x::y::st => (y+x)::st
  | .mul, x::y::st => (y*x)::st
  | _, _ => []

def execute {N : ℕ} (c : Cache N) (old : RefinedLayer N) : List (Instruction N) → List ℕ → List ℕ
  | [], st => st
  | i::is, st => execute c old is (i.exec c old st)

def programWork {N : ℕ} (p : List (Instruction N)) : ℕ := (p.map Instruction.work).sum

def gKernel {N : ℕ} (ad d : ℕ) (k u j : Fin (N+1)) (b : ℕ) : List (Instruction N) :=
  [.feasible ad d b u.val j.val,
   .choose k (.lit b), .power (.add (.lit ad) (.lit b)), .mul,
   .unmarked (.sub (.lit k.val) (.lit b)) (.sub (.lit u.val) (.mul (.lit d) (.lit b)))
     (.sub (.lit j.val) (.epsilon ad b)), .mul, .mul]

def sKernel {N : ℕ} (ad A d : ℕ) (k u j : Fin (N+1)) (b : ℕ) : List (Instruction N) :=
  [.feasible ad d b u.val j.val,
   .choose k (.lit b), .power (.add (.lit ad) (.lit b)), .mul,
   .marked (.sub (.lit k.val) (.lit b)) (.sub (.lit u.val) (.mul (.lit d) (.lit b)))
     (.sub (.lit j.val) (.epsilon ad b)),
   .gate A d b,
   .unmarked (.sub (.lit k.val) (.lit b)) (.sub (.lit u.val) (.mul (.lit d) (.lit b)))
     (.sub (.lit j.val) (.epsilon ad b)), .mul, .add, .mul, .mul]

lemma gKernel_eval {N : ℕ} (c : Cache N) (old : RefinedLayer N) (ad d : ℕ)
    (k u j : Fin (N+1)) (b : ℕ) :
    execute c old (gKernel ad d k u j b) [] =
      [if d*b≤u.val ∧ (if 0<ad+b then 1 else 0)≤j.val then
        chooseAt c k b*powerAt c (ad+b)*
          (refinedLayerAt old (k.val-b) (u.val-d*b) (j.val-(if 0<ad+b then 1 else 0))).1 else 0] := by
  by_cases h : d*b≤u.val ∧ (if 0<ad+b then 1 else 0)≤j.val
  · simp [execute, gKernel, Instruction.exec, Paper37.CachedOperations.Index.eval,
      OccupiedAddress.eval, h]
  · simp [execute, gKernel, Instruction.exec, Paper37.CachedOperations.Index.eval,
      OccupiedAddress.eval, h]

lemma sKernel_eval {N : ℕ} (c : Cache N) (old : RefinedLayer N) (ad A d : ℕ)
    (k u j : Fin (N+1)) (b : ℕ) :
    execute c old (sKernel ad A d k u j b) [] =
      [if d*b≤u.val ∧ (if 0<ad+b then 1 else 0)≤j.val then
        chooseAt c k b*powerAt c (ad+b)*
          ((refinedLayerAt old (k.val-b) (u.val-d*b) (j.val-(if 0<ad+b then 1 else 0))).2 +
            (if A<d then b else 0)*
              (refinedLayerAt old (k.val-b) (u.val-d*b) (j.val-(if 0<ad+b then 1 else 0))).1) else 0] := by
  by_cases h : d*b≤u.val ∧ (if 0<ad+b then 1 else 0)≤j.val
  · simp [execute, sKernel, Instruction.exec, Paper37.CachedOperations.Index.eval,
      OccupiedAddress.eval, h]
  · simp [execute, sKernel, Instruction.exec, Paper37.CachedOperations.Index.eval,
      OccupiedAddress.eval, h]

@[simp] lemma gKernel_work {N : ℕ} (ad d : ℕ) (k u j : Fin (N+1)) (b : ℕ) :
    programWork (gKernel ad d k u j b) = 27 := rfl
@[simp] lemma sKernel_work {N : ℕ} (ad A d : ℕ) (k u j : Fin (N+1)) (b : ℕ) :
    programWork (sKernel ad A d k u j b) = 42 := rfl

def interpretedStep (N : ℕ) (c : Cache N) (A : ℕ) (d : Fin N) (old : RefinedLayer N) : RefinedLayer N :=
  let ad := c.observed[d.val+1]
  Vector.ofFn fun k => Vector.ofFn fun u => Vector.ofFn fun j =>
    (∑ b ∈ range (k.val+1), (execute c old (gKernel ad (d.val+1) k u j b) []).headD 0,
     ∑ b ∈ range (k.val+1), (execute c old (sKernel ad A (d.val+1) k u j b) []).headD 0)

set_option maxHeartbeats 800000 in
/-- The concrete primitive interpreter executes the actual cached refinement
step. Guarding avoids any invalid predecessor count or occupied coordinate. -/
theorem interpretedStep_correct (N : ℕ) (c : Cache N) (A : ℕ) (d : Fin N) (old : RefinedLayer N) :
    interpretedStep N c A d old = cachedRefinedStep N c A d old := by
  apply Vector.ext
  intro k hk
  apply Vector.ext
  intro u hu
  apply Vector.ext
  intro j hj
  simp only [interpretedStep, cachedRefinedStep, cachedRefinedEntry, Vector.getElem_ofFn]
  apply Prod.ext
  · dsimp only
    apply sum_congr rfl
    intro b hb
    rw [gKernel_eval]
    simp only [List.headD_cons]
    unfold refinedLayerAt
    rw [dif_pos (by omega : k-b<N+1), dif_pos (by omega : u-(d.val+1)*b<N+1),
      dif_pos (by omega : j-(if 0<c.observed[d.val+1]+b then 1 else 0)<N+1)]
    rfl
  · dsimp only
    apply sum_congr rfl
    intro b hb
    rw [sKernel_eval]
    simp only [List.headD_cons]
    unfold refinedLayerAt
    rw [dif_pos (by omega : k-b<N+1), dif_pos (by omega : u-(d.val+1)*b<N+1),
      dif_pos (by omega : j-(if 0<c.observed[d.val+1]+b then 1 else 0)<N+1)]
    rfl

/-- The concrete interpreter is iterated through the same rolling schedule. -/
def interpretedRun (N : ℕ) (c : Cache N) (A : ℕ) : ℕ → RefinedLayer N
  | 0 => Vector.ofFn fun k => Vector.ofFn fun u => Vector.ofFn fun j =>
      (if k.val=0 ∧ u.val=0 ∧ j.val=0 then 1 else 0,0)
  | d+1 => if hd : d<N then
      interpretedStep N c A ⟨d,hd⟩ (interpretedRun N c A d)
    else interpretedRun N c A d

theorem interpretedRun_eq (N : ℕ) (c : Cache N) (A d : ℕ) :
    interpretedRun N c A d = cachedRefinedRun N c A d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [interpretedRun,cachedRefinedRun]
    split_ifs <;> simp only [ih,interpretedStep_correct]

theorem interpretedRun_correct (N : ℕ) (a : ℕ → ℕ) (A d : ℕ) (hd : d≤N)
    (ha : ∀ i≤N,a i≤N) :
    interpretedRun N (makeCache N a) A d = refinedRun N a A d := by
  rw [interpretedRun_eq,cachedRefinedRun_correct N a A d hd ha]

/-- The finite scalar schedule includes the feasibility programs, accumulation,
address calculations, observed reads, bounds and stores. -/
def kernelWork (N L : ℕ) : ℕ :=
  ∑ _d ∈ range L, (1 + ∑ k ∈ range (N+1), ∑ _u ∈ range (N+1), ∑ _j ∈ range (N+1),
    (8 + ∑ _b ∈ range (k+1), (27+42+2)))

lemma kernelWork_eq (N L : ℕ) :
    kernelWork N L = L + 8*L*(N+1)^3 + 71*refinedUpdateCount N L := by
  unfold kernelWork refinedUpdateCount
  simp only [sum_const, card_range, smul_eq_mul, Nat.cast_id]
  simp only [sum_add_distrib, ← mul_sum, ← sum_mul]
  simp [pow_succ, Nat.mul_assoc] <;> ring

lemma kernelWork_quintic (N L : ℕ) (hL : L≤N) : kernelWork N L ≤ 80*(N+1)^5 := by
  rw [kernelWork_eq]
  have hlin : N+1≤(N+1)^5 := le_self_pow₀ (by omega) (by decide)
  have hpow : (N+1)^4≤(N+1)^5 := Nat.pow_le_pow_right (by omega) (by decide)
  have hp : L*(N+1)^3≤(N+1)^4 := by
    calc
      _ ≤ (N+1)*(N+1)^3 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  have hu := refinedUpdateCount_quintic N L hL
  nlinarith

def coreWork (N L : ℕ) (z : List Bool) : ℕ :=
  Paper37.CachedOperations.preprocessingWork N z + kernelWork N L + 2*(N+1)^3

theorem coreWork_quintic (N L : ℕ) (z : List Bool) (hL : L≤N) (hz : z.length≤N) :
    coreWork N L z ≤ 200*(N+1)^5 := by
  have hpre := Paper37.CachedOperations.coreWork_quartic N 0 z (by omega) hz
  unfold Paper37.CachedOperations.coreWork at hpre
  have hp4 : (N+1)^4≤(N+1)^5 := Nat.pow_le_pow_right (by omega) (by decide)
  have hp3 : (N+1)^3≤(N+1)^5 := Nat.pow_le_pow_right (by omega) (by decide)
  have hk := kernelWork_quintic N L hL
  unfold coreWork
  nlinarith

theorem batch_coreWork_sextic (N L q C : ℕ) (z : List Bool) (hL : L≤N)
    (hz : z.length≤N) (hq : q≤C*(N+1)) :
    q*coreWork N L z ≤ 200*C*(N+1)^6 := by
  calc
    _ ≤ (C*(N+1))*(200*(N+1)^5) := Nat.mul_le_mul hq (coreWork_quintic N L z hL hz)
    _ = _ := by ring

end Paper37.CachedRefinedOperations
