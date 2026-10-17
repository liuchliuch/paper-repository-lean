import Paper37.CachedDP

/-! A concrete indexed arithmetic/load interpreter for the cached DP kernels.
The certified instruction schedule includes address arithmetic. Cache building
and output-pair formation are accounted for separately. -/
namespace Paper37.CachedOperations
open Finset Paper37.DP Paper37.ContinuationDP Paper37.CachedDP

/-- Small index expressions; arithmetic is explicitly represented as syntax. -/
inductive Index where
  | lit : ℕ → Index
  | add : Index → Index → Index
  | sub : Index → Index → Index
  | mul : Index → Index → Index
  | div : Index → Index → Index
  | min : Index → Index → Index

def Index.eval : Index → ℕ
  | .lit n => n
  | .add a b => a.eval+b.eval
  | .sub a b => a.eval-b.eval
  | .mul a b => a.eval*b.eval
  | .div a b => a.eval/b.eval
  | .min a b => Nat.min a.eval b.eval

def Index.work : Index → ℕ
  | .lit _ => 0
  | .add a b | .sub a b | .mul a b | .div a b | .min a b => a.work+b.work+1

/-- Indexed integer instructions. Loads include the range comparisons used by
safe cache/layer lookup. These are RAM primitives; their bit implementation is
kept separate from the algorithm-specific instruction schedule. -/
inductive Instruction (N : ℕ) where
  | choose : Fin (N+1) → Index → Instruction N
  | power : Index → Instruction N
  | unmarked : Index → Index → Instruction N
  | marked : Index → Index → Instruction N
  | gate : ℕ → ℕ → ℕ → Instruction N
  | add : Instruction N
  | mul : Instruction N
  | div : Instruction N

def Instruction.work {N : ℕ} : Instruction N → ℕ
  | .choose _ b => b.work+3
  | .power c => c.work+3
  | .unmarked k u | .marked k u => k.work+u.work+3
  | .gate _ _ _ => 2
  | .add | .mul | .div => 1

def Instruction.exec {N : ℕ} (c : Cache N) (old : Layer N) : Instruction N → List ℕ → List ℕ
  | .choose k b, stack => chooseAt c k b.eval :: stack
  | .power v, stack => powerAt c v.eval :: stack
  | .unmarked k u, stack => (layerAt old k.eval u.eval).1 :: stack
  | .marked k u, stack => (layerAt old k.eval u.eval).2 :: stack
  | .gate A d b, stack => (if A<d then b else 0) :: stack
  | .add, x::y::stack => (y+x)::stack
  | .mul, x::y::stack => (y*x)::stack
  | .div, x::y::stack => (y/x)::stack
  | _, _ => []

def execute {N : ℕ} (c : Cache N) (old : Layer N) : List (Instruction N) → List ℕ → List ℕ
  | [], stack => stack
  | i::is, stack => execute c old is (i.exec c old stack)

def programWork {N : ℕ} (p : List (Instruction N)) : ℕ := (p.map Instruction.work).sum

/-- The executable G summand has three indexed loads and two multiplications. -/
def gKernel {N : ℕ} (ad d : ℕ) (k u : Fin (N+1)) (b : ℕ) : List (Instruction N) :=
  [.choose k (.lit b),.power (.add (.lit ad) (.lit b)),.mul,
    .unmarked (.sub (.lit k.val) (.lit b)) (.sub (.lit u.val) (.mul (.lit d) (.lit b))),.mul]

/-- The S summand adds its old marked entry to the newly gated marks. -/
def sKernel {N : ℕ} (ad A d : ℕ) (k u : Fin (N+1)) (b : ℕ) : List (Instruction N) :=
  [.choose k (.lit b),.power (.add (.lit ad) (.lit b)),.mul,
    .marked (.sub (.lit k.val) (.lit b)) (.sub (.lit u.val) (.mul (.lit d) (.lit b))),
    .gate A d b,
    .unmarked (.sub (.lit k.val) (.lit b)) (.sub (.lit u.val) (.mul (.lit d) (.lit b))),
    .mul,.add,.mul]

lemma gKernel_eval {N : ℕ} (c : Cache N) (old : Layer N) (ad d : ℕ)
    (k u : Fin (N+1)) (b : ℕ) :
    execute c old (gKernel ad d k u b) [] =
      [chooseAt c k b*powerAt c (ad+b)*(layerAt old (k.val-b) (u.val-d*b)).1] := by
  rfl

lemma sKernel_eval {N : ℕ} (c : Cache N) (old : Layer N) (ad A d : ℕ)
    (k u : Fin (N+1)) (b : ℕ) :
    execute c old (sKernel ad A d k u b) [] =
      [chooseAt c k b*powerAt c (ad+b)*
        ((layerAt old (k.val-b) (u.val-d*b)).2 +
          (if A<d then b else 0)*(layerAt old (k.val-b) (u.val-d*b)).1)] := by
  rfl

@[simp] lemma gKernel_work {N : ℕ} (ad d : ℕ) (k u : Fin (N+1)) (b : ℕ) :
    programWork (gKernel ad d k u b) = 15 := rfl

@[simp] lemma sKernel_work {N : ℕ} (ad A d : ℕ) (k u : Fin (N+1)) (b : ℕ) :
    programWork (sKernel ad A d k u b) = 25 := rfl

/-- The same materialized step, executed through the certified primitive kernels. -/
def interpretedStep (N : ℕ) (c : Cache N) (A : ℕ) (d : Fin N) (old : Layer N) : Layer N :=
  let ad := c.observed[d.val+1]
  Vector.ofFn fun k => Vector.ofFn fun u =>
    (∑ b ∈ range (min k.val (u.val/(d.val+1))+1),
      (execute c old (gKernel ad (d.val+1) k u b) []).headD 0,
     ∑ b ∈ range (min k.val (u.val/(d.val+1))+1),
      (execute c old (sKernel ad A (d.val+1) k u b) []).headD 0)

/-- The primitive kernels execute the actual cached DP summands, rather than
an unrelated operation schedule. -/
theorem interpretedStep_correct (N : ℕ) (c : Cache N) (A : ℕ) (d : Fin N) (old : Layer N) :
    interpretedStep N c A d old = cachedStep N c A d old := by
  apply Vector.ext
  intro k hk
  apply Vector.ext
  intro u hu
  simp only [interpretedStep,cachedStep,Vector.getElem_ofFn]
  apply Prod.ext
  · dsimp only
    apply sum_congr rfl
    intro b hb
    rw [gKernel_eval]
    simp only [List.headD_cons]
    unfold layerAt
    rw [dif_pos (by omega : k-b<N+1),dif_pos (by omega : u-(d.val+1)*b<N+1)]
    rfl
  · dsimp only
    apply sum_congr rfl
    intro b hb
    rw [sKernel_eval]
    simp only [List.headD_cons]
    unfold layerAt
    rw [dif_pos (by omega : k-b<N+1),dif_pos (by omega : u-(d.val+1)*b<N+1)]
    rfl

/-- One cell's loop bound is computed once from explicit index arithmetic. -/
def boundIndex (d k u : ℕ) : Index := .add (.min (.lit k) (.div (.lit u) (.lit d))) (.lit 1)

@[simp] lemma boundIndex_eval (d k u : ℕ) : (boundIndex d k u).eval = min k (u/d)+1 := rfl
@[simp] lemma boundIndex_work (d k u : ℕ) : (boundIndex d k u).work = 3 := rfl

/-- Complete kernel/setup schedule: one observed cache read per layer; each
cell computes its loop bound, stores two outputs, and accumulates both sums. -/
def kernelWork (N L : ℕ) : ℕ :=
  ∑ d ∈ range L, (1 + ∑ k ∈ range (N+1), ∑ u ∈ range (N+1),
    ((boundIndex (d+1) k u).work+2 +
      ∑ b ∈ range (min k (u/(d+1))+1),
        (15+25+2)))

lemma kernelWork_eq (N L : ℕ) :
    kernelWork N L = L + 5*L*(N+1)^2 + 42*updateCount N L := by
  unfold kernelWork updateCount
  simp only [boundIndex_work,sum_const,card_range,smul_eq_mul,Nat.cast_id]
  simp only [sum_add_distrib,← mul_sum,← sum_mul]
  simp [pow_two,Nat.mul_assoc] <;> ring

/-- The explicitly tracked scalar cache operations and interpreted kernels. -/
def queryWork (N L : ℕ) (z : List Bool) : ℕ :=
  chooseCacheAdds N + powerCacheMuls N + observedCacheComparisons N z +
    kernelWork N L + 2*(N+1)^2

/-- An upper instruction schedule for all cache builders and input traversals.
The Pascal body charges its addition, two reads, comparison, subtraction and
write. Linear powers charge multiplication/control. Each histogram traversal
charges equality, optional increment and list control. The final linear term
covers the finite number of actual prefix parse/map/age traversals. -/
def preprocessingWork (N : ℕ) (z : List Bool) : ℕ :=
  6*chooseCacheAdds N + 2*(N+1)^2 + 3*powerCacheMuls N + 2*(2*N+1) +
    3*observedCacheComparisons N z + (N+1) + 12*z.length

/-- Core execution includes the concrete cache builders, the certified
primitive recurrence kernels and initialization of the pair-valued layer. -/
def coreWork (N L : ℕ) (z : List Bool) : ℕ :=
  preprocessingWork N z + kernelWork N L + 2*(N+1)^2

lemma kernelWork_quartic (N L : ℕ) (hL : L≤N) : kernelWork N L ≤ 48*(N+1)^4 := by
  rw [kernelWork_eq]
  have hlin : N+1≤(N+1)^4 := le_self_pow₀ (by omega) (by decide)
  have hpow : (N+1)^3≤(N+1)^4 := Nat.pow_le_pow_right (by omega) (by decide)
  have hp : L*(N+1)^2≤(N+1)^3 := by
    calc
      _ ≤ (N+1)*(N+1)^2 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  have hu := updateCount_quartic N L hL
  nlinarith

/-- All core primitive schedules for one queried prefix have the fourth-degree
bound after explicitly charging cache preprocessing and parsed-count scans. -/
theorem coreWork_quartic (N L : ℕ) (z : List Bool) (hL : L≤N) (hz : z.length≤N) :
    coreWork N L z ≤ 100*(N+1)^4 := by
  have hlin : N+1≤(N+1)^4 := le_self_pow₀ (by omega) (by decide)
  have hpow2 : (N+1)^2≤(N+1)^4 := Nat.pow_le_pow_right (by omega) (by decide)
  have hpow3 : (N+1)^3≤(N+1)^4 := Nat.pow_le_pow_right (by omega) (by decide)
  have hpowers : (2*N+1)^2≤4*(N+1)^4 := by
    calc
      _ ≤ (2*(N+1))^2 := Nat.pow_le_pow_left (by omega) _
      _ = 4*(N+1)^2 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hpow2
  have hc := chooseCacheAdds_le N
  have hp := powerCacheMuls_le N
  have ho := observedCacheComparisons_le N z hz
  have hk := kernelWork_quartic N L hL
  unfold coreWork preprocessingWork
  nlinarith

/-- A specified linear-size batch uses the very same per-query cached program.
This statement counts precisely the supplied queries, not all possible prefixes. -/
theorem batch_coreWork_quintic (N L q C : ℕ) (z : List Bool) (hL : L≤N)
    (hz : z.length≤N) (hq : q≤C*(N+1)) :
    q*coreWork N L z ≤ 100*C*(N+1)^5 := by
  calc
    _ ≤ (C*(N+1))*(100*(N+1)^4) := Nat.mul_le_mul hq (coreWork_quartic N L z hL hz)
    _ = _ := by ring

/-- Execute every recurrence layer through the instruction interpreter. -/
def interpretedRun (N : ℕ) (c : Cache N) (A : ℕ) : ℕ → Layer N
  | 0 => Vector.ofFn fun k => Vector.ofFn fun u => (if k.val=0 ∧ u.val=0 then 1 else 0,0)
  | d+1 => if hd : d<N then interpretedStep N c A ⟨d,hd⟩ (interpretedRun N c A d) else interpretedRun N c A d

lemma interpretedRun_eq_cachedRun (N : ℕ) (c : Cache N) (A d : ℕ) :
    interpretedRun N c A d = cachedRun N c A d := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [interpretedRun,cachedRun,ih,interpretedStep_correct]

/-- The instruction interpreter computes the exact independently specified DP. -/
theorem interpretedRun_correct (N : ℕ) (a : ℕ → ℕ) (A d : ℕ) (hd : d≤N)
    (ha : ∀i≤N,a i≤N) : interpretedRun N (makeCache N a) A d = run N a A d := by
  rw [interpretedRun_eq_cachedRun,cachedRun_correct N a A d hd ha]

end Paper37.CachedOperations
