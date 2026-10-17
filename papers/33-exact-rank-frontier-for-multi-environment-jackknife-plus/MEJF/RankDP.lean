import MEJF.RandomizedProbability
import Mathlib.Data.List.Sort
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Finset.Lattice.Union
import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.Tactic.Tauto

/-! The polynomial rank-score dynamic program. Landau's published theorem is
an explicit full input, never a local axiom or an assumed optimization conclusion. -/
namespace MEJF.RankDP
open Finset TournamentOptimization
noncomputable section
attribute [local instance] Classical.propDecidable

/-- All lower prefix inequalities for an increasing score list. -/
def prefixLower (xs : List ℕ) : Prop := ∀ k ≤ xs.length, k.choose 2 ≤ (xs.take k).sum

lemma prefixLower_snoc (xs : List ℕ) (r : ℕ) :
    prefixLower (xs ++ [r]) ↔ prefixLower xs ∧
      (xs.length+1).choose 2 ≤ xs.sum+r := by
  have ht (k : ℕ) (hk : k ≤ xs.length) : (xs ++ [r]).take k = xs.take k := by
    simp [List.take_append, Nat.sub_eq_zero_of_le hk]
  constructor
  · intro h
    constructor
    · intro k hk
      simpa only [ht k hk] using h k (by simp; omega)
    · simpa [prefixLower] using h (xs.length+1) (by simp)
  · rintro ⟨h,hfull⟩ k hk
    by_cases hkle : k ≤ xs.length
    · simpa only [ht k hkle] using h k hkle
    · have hk' : k ≤ xs.length+1 := by simpa using hk
      have heq : k = xs.length+1 := by omega
      subst k
      simpa using hfull

/-- Descending prefixes, so the recursion adjoins the new largest score at the
front. Reversing gives exactly the increasing prefixes in Landau's statement. -/
def valid (N : ℕ) : List ℕ → Prop
  | [] => True
  | r :: xs => r < N ∧ (∀ x ∈ xs, x ≤ r) ∧ valid N xs ∧
      (xs.length+1).choose 2 ≤ r+xs.sum

lemma valid_iff (N : ℕ) (xs : List ℕ) :
    valid N xs ↔ xs.Pairwise (fun a b => b ≤ a) ∧
      (∀ x ∈ xs, x < N) ∧ prefixLower xs.reverse := by
  induction xs with
  | nil => simp [valid, prefixLower]
  | cons r xs ih =>
      simp only [valid, List.pairwise_cons, List.forall_mem_cons, List.reverse_cons,
        prefixLower_snoc, List.length_reverse, List.sum_reverse, ih, Nat.add_comm r xs.sum]
      tauto

/-- Landau's full score characterization, with a descending list reversed for
its increasing-prefix inequalities. Source: H. G. Landau (1953), DOI
10.1007/BF02476378, paper reference [12]. It is an explicit quantified input. -/
def LandauInput (N : ℕ) : Prop :=
  ∀ xs : List ℕ, xs.Pairwise (fun a b => b ≤ a) →
    ((∃ T : Tour N, (List.ofFn (degree T)).Perm xs) ↔
      xs.length = N ∧ (∀ x ∈ xs, x < N) ∧ prefixLower xs.reverse ∧ xs.sum = N.choose 2)

/-- Exhaustive finite prefix set used only to state the DP's semantics. -/
def paths (N : ℕ) : ℕ → ℕ → ℕ → Finset (List ℕ)
  | 0, _, s => if s = 0 then {[]} else ∅
  | k+1, r, s => (range (r+1)).biUnion fun q =>
      if q < N ∧ q ≤ s ∧ (k+1).choose 2 ≤ s then
        (paths N k q (s-q)).image (List.cons q)
      else ∅

lemma mem_paths (N k r s : ℕ) (xs : List ℕ) :
    xs ∈ paths N k r s ↔ xs.length = k ∧ xs.sum = s ∧
      valid N xs ∧ (∀ x ∈ xs, x ≤ r) := by
  induction k generalizing r s xs with
  | zero =>
      cases xs with
      | nil => by_cases hs : s=0 <;> simp [paths, valid, hs, eq_comm]
      | cons x xs => simp [paths]; split_ifs <;> simp
  | succ k ih =>
      constructor
      · intro h
        simp only [paths, mem_biUnion, mem_range] at h
        obtain ⟨q,hq,h⟩ := h
        split_ifs at h with hg
        · obtain ⟨ys,hys,rfl⟩ := mem_image.mp h
          obtain ⟨hlen,hsum,hvalid,hcap⟩ := (ih q (s-q) ys).mp hys
          refine ⟨by simp [hlen], ?_, ?_, ?_⟩
          · simp only [List.sum_cons]; omega
          · exact ⟨hg.1,hcap,hvalid,by rw [hlen,hsum]; omega⟩
          · intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · omega
            · exact (hcap x hx).trans (by omega)
        · simp at h
      · rintro ⟨hlen,hsum,hvalid,hcap⟩
        cases xs with
        | nil => simp at hlen
        | cons q ys =>
            obtain ⟨hqN,hyscap,hysvalid,hprefix⟩ := hvalid
            have hlenys : ys.length = k := by simpa using hlen
            have hysum : ys.sum = s-q := by simp only [List.sum_cons] at hsum; omega
            have hq : q ≤ r := hcap q (by simp)
            have hqs : q ≤ s := by simp only [List.sum_cons] at hsum; omega
            have hg : q < N ∧ q ≤ s ∧ (k+1).choose 2 ≤ s :=
              ⟨hqN,hqs,by simpa [hlenys,←hsum] using hprefix⟩
            simp only [paths, mem_biUnion, mem_range]
            refine ⟨q,by omega,?_⟩
            rw [if_pos hg]
            exact mem_image.mpr ⟨ys,(ih q (s-q) ys).mpr ⟨hlenys,hysum,hysvalid,hyscap⟩,rfl⟩

/-- One real payoff is added to an optional value, with bottom representing an
infeasible prefix. Addition preserves the finite maximum, including empty sets. -/
lemma add_sup {α : Type*} (a : ℝ) (s : Finset α) (f : α → WithBot ℝ) :
    (a : WithBot ℝ) + s.sup f = s.sup (fun x => (a : WithBot ℝ) + f x) := by
  exact comp_sup_eq_sup_comp_of_is_total (fun v : WithBot ℝ => (a : WithBot ℝ)+v)
    (fun _ _ h => add_le_add_left h _) (by simp)

/-- The scalar DP recurrence. The finite supremum over `0,...,r` is a prefix
maximum and is tabulated by the constant-cost recurrence proved below. -/
def eval (N : ℕ) (phi : ℕ → ℝ) : ℕ → ℕ → ℕ → WithBot ℝ
  | 0, _, s => if s = 0 then 0 else ⊥
  | k+1, r, s => (range (r+1)).sup fun q =>
      if q < N ∧ q ≤ s ∧ (k+1).choose 2 ≤ s then
        (phi q : WithBot ℝ) + eval N phi k q (s-q)
      else ⊥

def score (phi : ℕ → ℝ) (xs : List ℕ) : WithBot ℝ := ((xs.map phi).sum : ℝ)

/-- Exact semantic correctness: the scalar DP computes the largest payoff of
all feasible sorted prefixes, and bottom iff no prefix exists. -/
theorem eval_correct (N : ℕ) (phi : ℕ → ℝ) (k r s : ℕ) :
    eval N phi k r s = (paths N k r s).sup (score phi) := by
  induction k generalizing r s with
  | zero => by_cases hs : s=0 <;> simp [eval,paths,hs,score]
  | succ k ih =>
      simp only [eval,paths,sup_biUnion]
      apply sup_congr rfl
      intro q _
      split_ifs with hg
      · rw [ih, add_sup, sup_image]
        apply sup_congr rfl
        intro xs _
        simp [Function.comp_def, score, WithBot.coe_add]
      · simp

/-- A single cell after the first degree is obtained from the previous prefix
maximum and one predecessor value, rather than rescanning every predecessor. -/
theorem eval_prefix_step (N : ℕ) (phi : ℕ → ℝ) (k r s : ℕ) :
    eval N phi (k+1) (r+1) s = max (eval N phi (k+1) r s)
      (if r+1 < N ∧ r+1 ≤ s ∧ (k+1).choose 2 ≤ s then
        (phi (r+1) : WithBot ℝ)+eval N phi k (r+1) (s-(r+1)) else ⊥) := by
  simp only [eval,range_add_one,sup_insert,mem_range,lt_self_iff_false,not_false_eq_true]
  exact sup_comm _ _

/-- The full source constraints of (6.21) are exactly the final DP domain. -/
lemma final_domain (N : ℕ) (hN : 1 ≤ N) (xs : List ℕ) :
    xs ∈ paths N N (N-1) (N.choose 2) ↔
      xs.Pairwise (fun a b => b ≤ a) ∧ xs.length = N ∧
        (∀ x ∈ xs, x < N) ∧ prefixLower xs.reverse ∧ xs.sum = N.choose 2 := by
  rw [mem_paths, valid_iff]
  constructor
  · rintro ⟨hl,hs,⟨hp,hb,hpre⟩,_⟩
    exact ⟨hp,hl,hb,hpre,hs⟩
  · rintro ⟨hp,hl,hb,hpre,hs⟩
    exact ⟨hl,hs,⟨hp,hb,hpre⟩,fun x hx => by have := hb x hx; omega⟩

/-- A permutation of the actual degree list preserves every additive payoff. -/
lemma perm_score {N : ℕ} (phi : ℕ → ℝ) (T : Tour N) (xs : List ℕ)
    (h : (List.ofFn (degree T)).Perm xs) :
    score phi xs = ((∑ u, phi (degree T u) : ℝ) : WithBot ℝ) := by
  have hh := (h.map phi).sum_eq
  simpa [score,List.map_ofFn,Fin.sum_ofFn] using congrArg (fun x : ℝ => (x : WithBot ℝ)) hh.symm

/-- Under the exact published score characterization, the computed number is
the actual maximum over tournaments, not merely an upper relaxation. -/
theorem eval_eq_maxObjective (F m t : ℕ) (pi : Fin m → ℝ) (hLandau : LandauInput (m+1)) :
    eval (m+1) (RandomizedRanks.payoff F m t pi) (m+1) m ((m+1).choose 2) =
      (maxObjective F m t pi : WithBot ℝ) := by
  rw [eval_correct]
  apply le_antisymm
  · apply Finset.sup_le
    intro xs hx
    obtain ⟨hp,hlen,hbound,hpre,hsum⟩ := (final_domain (m+1) (by omega) xs).mp hx
    obtain ⟨T,hT⟩ := (hLandau xs hp).mpr ⟨hlen,hbound,hpre,hsum⟩
    rw [perm_score _ T xs hT]
    exact_mod_cast le_maxObjective F m t pi T
  · obtain ⟨T,hT⟩ := maxObjective_attained F m t pi
    let xs := (List.ofFn (degree T)).insertionSort (fun a b : ℕ => b ≤ a)
    have hp : xs.Pairwise (fun a b => b ≤ a) := List.sorted_insertionSort _ _
    have hperm : (List.ofFn (degree T)).Perm xs := (List.perm_insertionSort _ _).symm
    obtain ⟨hlen,hbound,hpre,hsum⟩ := (hLandau xs hp).mp ⟨T,hperm⟩
    have hx := (final_domain (m+1) (by omega) xs).mpr ⟨hp,hlen,hbound,hpre,hsum⟩
    have hle := le_sup (f := score (RandomizedRanks.payoff F m t pi)) hx
    rw [perm_score _ T xs hperm] at hle
    change ((objective F m t pi T : ℝ) : WithBot ℝ) ≤ _ at hle
    rw [hT] at hle
    simpa using hle

/-- Number of memoized scalar cells for layers `0,...,N`, degree caps `0,...,N-1`,
and sums `0,...,choose N 2`. Only two adjacent layers need be retained. -/
def cellCount (N : ℕ) : ℕ := (N+1)*N*(N.choose 2+1)
def rollingCells (N : ℕ) : ℕ := 2*N*(N.choose 2+1)
def arithmeticCost (N : ℕ) : ℕ := 8*cellCount N

/-- A tabulation cell uses at most eight unit-cost arithmetic/comparison actions:
the prefix maximum comparison, one payoff addition, one subtraction, and at
most five guard/index operations. The binomial thresholds are precomputed. -/
theorem quartic_cost_bound (N : ℕ) (hN : 1 ≤ N) :
    arithmeticCost N ≤ 32*N^4 ∧ rollingCells N ≤ 4*N^3 := by
  have hc : N.choose 2 ≤ N^2 := Nat.choose_le_pow N 2
  have hN1 : N+1 ≤ 2*N := by omega
  have hc1 : N.choose 2+1 ≤ 2*N^2 := by nlinarith
  dsimp [arithmeticCost,cellCount,rollingCells]
  constructor
  · calc
      8*((N+1)*N*(N.choose 2+1)) ≤ 8*((2*N)*N*(2*N^2)) :=
        Nat.mul_le_mul_left 8 (Nat.mul_le_mul (Nat.mul_le_mul_right N hN1) hc1)
      _ = 32*N^4 := by ring
  · calc
      2*N*(N.choose 2+1) ≤ 2*N*(2*N^2) := Nat.mul_le_mul_left (2*N) hc1
      _ = 4*N^3 := by ring

/-- The inputs are memoized table values. This instrumented cell performs
three guard comparisons, one prefix-maximum comparison, and, only on a feasible
transition, one subtraction and one payoff addition. No recursive call is
charged as a new computation: its table cell precedes this one. -/
def memoCell (N k r s : ℕ) (phi : ℕ → ℝ) (carry previous : WithBot ℝ) : WithBot ℝ × ℕ :=
  if r < N ∧ r ≤ s ∧ (k+1).choose 2 ≤ s then
    (max carry ((phi r : WithBot ℝ)+previous), 6)
  else (max carry ⊥, 4)

theorem memoCell_cost (N k r s : ℕ) (phi : ℕ → ℝ) (carry previous : WithBot ℝ) :
    (memoCell N k r s phi carry previous).2 ≤ 8 := by
  unfold memoCell
  split_ifs <;> simp

theorem memoCell_correct (N k r s : ℕ) (phi : ℕ → ℝ) :
    (memoCell N k (r+1) s phi (eval N phi (k+1) r s)
      (eval N phi k (r+1) (s-(r+1)))).1 = eval N phi (k+1) (r+1) s := by
  rw [eval_prefix_step]
  unfold memoCell
  split_ifs <;> rfl

theorem memoCell_correct_zero (N k s : ℕ) (phi : ℕ → ℝ) :
    (memoCell N k 0 s phi ⊥ (eval N phi k 0 s)).1 = eval N phi (k+1) 0 s := by
  simp only [eval,range_one,sup_singleton]
  unfold memoCell
  split_ifs <;> simp_all

/-- The initial layer performs exactly one equality test per sum state. -/
def initialCell (s : ℕ) : WithBot ℝ × ℕ := (if s=0 then 0 else ⊥,1)

theorem initialCell_correct (N r s : ℕ) (phi : ℕ → ℝ) :
    (initialCell s).1 = eval N phi 0 r s := rfl

theorem initialCell_cost (s : ℕ) : (initialCell s).2 ≤ 8 := by norm_num [initialCell]

/-- The finite lexicographic tabulation grid includes the initial layer. -/
abbrev Grid (N : ℕ) := Fin (N+1) × Fin N × Fin (N.choose 2+1)

theorem grid_card (N : ℕ) : Fintype.card (Grid N) = cellCount N := by
  simp [Grid,cellCount,Nat.mul_assoc]

/-- Summing the instrumented per-cell arithmetic counts over the actual finite
tabulation grid gives the declared total budget. This is a count of the
constant-cost transitions, not a count of an exhaustive sequence enumeration. -/
theorem tabulation_cost (N : ℕ) (phi : ℕ → ℝ)
    (carry previous : Grid N → WithBot ℝ) :
    (∑ a : Grid N,
      (memoCell N a.1.val a.2.1.val a.2.2.val phi (carry a) (previous a)).2) ≤ arithmeticCost N := by
  calc
    _ ≤ ∑ _ : Grid N, 8 := sum_le_sum (fun a _ => memoCell_cost _ _ _ _ _ _ _)
    _ = arithmeticCost N := by simp [Grid,arithmeticCost,cellCount,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]

/-- The actual schedule charges the initial equality test in layer zero and
the constant-cost memoized transition in every later layer. -/
def scheduledCellCost (N : ℕ) (phi : ℕ → ℝ)
    (carry previous : Grid N → WithBot ℝ) (a : Grid N) : ℕ :=
  if a.1.val=0 then (initialCell a.2.2.val).2
  else (memoCell N (a.1.val-1) a.2.1.val a.2.2.val phi (carry a) (previous a)).2

theorem scheduled_tabulation_cost (N : ℕ) (phi : ℕ → ℝ)
    (carry previous : Grid N → WithBot ℝ) :
    (∑ a : Grid N,scheduledCellCost N phi carry previous a) ≤ arithmeticCost N := by
  calc
    _ ≤ ∑ _ : Grid N,8 := by
      apply sum_le_sum
      intro a _
      unfold scheduledCellCost
      split_ifs
      · exact initialCell_cost _
      · exact memoCell_cost _ _ _ _ _ _ _
    _ = arithmeticCost N := by
      simp [Grid,arithmeticCost,cellCount,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]

/-- Unit-cost natural arithmetic expressions used to make the payoff-table
preprocessing count explicit, including division and truncated subtraction. -/
inductive NatExpr where
  | literal : ℕ → NatExpr
  | add : NatExpr → NatExpr → NatExpr
  | sub : NatExpr → NatExpr → NatExpr
  | mul : NatExpr → NatExpr → NatExpr
  | div : NatExpr → NatExpr → NatExpr
  | min : NatExpr → NatExpr → NatExpr

def NatExpr.value : NatExpr → ℕ
  | .literal n => n
  | .add a b => a.value+b.value
  | .sub a b => a.value-b.value
  | .mul a b => a.value*b.value
  | .div a b => a.value/b.value
  | .min a b => Nat.min a.value b.value

def NatExpr.cost : NatExpr → ℕ
  | .literal _ => 0
  | .add a b | .sub a b | .mul a b | .div a b | .min a b => a.cost+b.cost+1

def thresholdProgram (F m t l : ℕ) : NatExpr :=
  .sub (.literal m) (.min (.literal m)
    (.div (.mul (.literal F) (.sub (.literal m)
      (.sub (.add (.literal m) (.literal 1)) (.add (.literal l) (.literal 1)))))
      (.add (.sub (.literal F) (.literal t)) (.literal 1))))

theorem thresholdProgram_correct (F m t l : ℕ) :
    (thresholdProgram F m t l).value = Incidence.threshold F m (m+1-(l+1)) t := rfl

theorem thresholdProgram_cost (F m t l : ℕ) : (thresholdProgram F m t l).cost = 10 := rfl

/-- Each rank term evaluates the displayed threshold program, compares it to
`z`, and adds its weighted indicator to the accumulator. -/
def payoffProgram (F m t : ℕ) (pi : Fin m → ℝ) (z : ℕ) : ℝ × ℕ :=
  (∑ l : Fin m, if (thresholdProgram F m t l.val).value ≤ z then pi l else 0,
   ∑ l : Fin m, ((thresholdProgram F m t l.val).cost+2))

theorem payoffProgram_correct (F m t : ℕ) (pi : Fin m → ℝ) (z : ℕ) :
    (payoffProgram F m t pi z).1 = RandomizedRanks.payoff F m t pi z := rfl

theorem payoffProgram_cost (F m t : ℕ) (pi : Fin m → ℝ) (z : ℕ) :
    (payoffProgram F m t pi z).2 = 12*m := by simp [payoffProgram,thresholdProgram_cost,Nat.mul_comm]

/-- Evaluate the payoff at every possible tournament degree. -/
def payoffTableProgramCost (F m t N : ℕ) (pi : Fin m → ℝ) : ℕ :=
  ∑ z : Fin N, (payoffProgram F m t pi z.val).2

theorem payoffTableProgram_cost (F m t N : ℕ) (pi : Fin m → ℝ) :
    payoffTableProgramCost F m t N pi = 12*N*m := by
  simp [payoffTableProgramCost,payoffProgram_cost]
  ring

/-- Consecutive binomial thresholds are computed by one running addition;
one further unit is allowed for loop-index advancement. -/
def binomialProgram : ℕ → ℕ
  | 0 => 0
  | k+1 => binomialProgram k+k

theorem binomialProgram_correct (k : ℕ) : binomialProgram k = k.choose 2 := by
  induction k with
  | zero => simp [binomialProgram]
  | succ k ih => simp [binomialProgram,ih,Nat.choose_succ_succ,Nat.add_comm]

def preprocessingCost (F m t N : ℕ) (pi : Fin m → ℝ) : ℕ :=
  payoffTableProgramCost F m t N pi+2*N

theorem preprocessing_cost_bound (F m t N : ℕ) (pi : Fin m → ℝ) (hmN : m ≤ N) :
    preprocessingCost F m t N pi ≤ 16*N^2+16*N := by
  rw [preprocessingCost,payoffTableProgram_cost]
  nlinarith

/-- The concrete memoized inputs of the lexicographic evaluation schedule. -/
def tableCarry (N : ℕ) (phi : ℕ → ℝ) (a : Grid N) : WithBot ℝ :=
  if a.2.1.val=0 then ⊥ else eval N phi a.1.val (a.2.1.val-1) a.2.2.val

def tablePrevious (N : ℕ) (phi : ℕ → ℝ) (a : Grid N) : WithBot ℝ :=
  eval N phi (a.1.val-1) a.2.1.val (a.2.2.val-a.2.1.val)

def scheduledCell (N : ℕ) (phi : ℕ → ℝ) (a : Grid N) : WithBot ℝ × ℕ :=
  if a.1.val=0 then initialCell a.2.2.val
  else memoCell N (a.1.val-1) a.2.1.val a.2.2.val phi
    (tableCarry N phi a) (tablePrevious N phi a)

theorem scheduledCell_correct (N : ℕ) (phi : ℕ → ℝ) (a : Grid N) :
    (scheduledCell N phi a).1 = eval N phi a.1.val a.2.1.val a.2.2.val := by
  unfold scheduledCell
  split_ifs with hk
  · simpa [hk] using initialCell_correct N a.2.1.val a.2.2.val phi
  · have hks : a.1.val-1+1=a.1.val := by omega
    by_cases hr : a.2.1.val=0
    · simpa [tableCarry,tablePrevious,hr,hks] using
        memoCell_correct_zero N (a.1.val-1) a.2.2.val phi
    · have hrs : a.2.1.val-1+1=a.2.1.val := by omega
      simpa [tableCarry,tablePrevious,hr,hks,hrs] using
        memoCell_correct N (a.1.val-1) (a.2.1.val-1) a.2.2.val phi

/-- The payoff and binomial threshold tables need only quadratic additional
arithmetic work; this conservative budget includes their divisions and guards. -/
def totalArithmeticCost (N : ℕ) : ℕ := arithmeticCost N + 16*N^2+16*N

theorem total_quartic_cost (N : ℕ) (hN : 1 ≤ N) : totalArithmeticCost N ≤ 64*N^4 := by
  have hc := (quartic_cost_bound N hN).1
  have hNN : N ≤ N^2 := by nlinarith
  have hN4 : N^2 ≤ N^4 := by nlinarith [sq_nonneg (N^2-1 : ℤ)]
  dsimp [totalArithmeticCost]
  nlinarith

/-- Complete arithmetic budget for the correct memoized schedule and the
explicit payoff/binomial preprocessing program. -/
theorem complete_program_cost (F m t N : ℕ) (pi : Fin m → ℝ) (hmN : m ≤ N) (hN : 1 ≤ N) :
    (∑ a : Grid N,(scheduledCell N (RandomizedRanks.payoff F m t pi) a).2) +
      preprocessingCost F m t N pi ≤ 64*N^4 := by
  have hcost : (∑ a : Grid N,(scheduledCell N (RandomizedRanks.payoff F m t pi) a).2) ≤
      arithmeticCost N := by
    have heq (a : Grid N) : (scheduledCell N (RandomizedRanks.payoff F m t pi) a).2 =
        scheduledCellCost N (RandomizedRanks.payoff F m t pi)
          (tableCarry N (RandomizedRanks.payoff F m t pi))
          (tablePrevious N (RandomizedRanks.payoff F m t pi)) a := by
      unfold scheduledCell scheduledCellCost
      split_ifs <;> rfl
    simp_rw [heq]
    exact scheduled_tabulation_cost N
      (RandomizedRanks.payoff F m t pi) (tableCarry N (RandomizedRanks.payoff F m t pi))
      (tablePrevious N (RandomizedRanks.payoff F m t pi))
  have hpre := preprocessing_cost_bound F m t N pi hmN
  have htotal := total_quartic_cost N hN
  dsimp [totalArithmeticCost] at htotal
  omega

/-- The nonboundary dependency is in the previous layer; the prefix-maximum
carry is in the current layer at the immediately preceding degree cap. Thus
the lexicographic `(layer,cap)` schedule computes every cell once. -/
theorem dependency_order (k r : ℕ) :
    Prod.Lex (· < ·) (· < ·) (k,r+1) (k+1,r+1) ∧
    Prod.Lex (· < ·) (· < ·) (k+1,r) (k+1,r+1) := by
  constructor
  · exact Prod.Lex.left _ _ (by omega)
  · exact Prod.Lex.right _ (by omega)

/-- The DP computes the genuine statistical value, with only the classical
Landau score characterization supplied externally as the explicit input. -/
theorem dp_computes_gamma (m n F t : ℕ) (hF : 1 ≤ F) (hFn : F ≤ n)
    (ht : 1 ≤ t ∧ t ≤ F) (pi : RandomizedProbability.RankLaw m)
    (hLandau : LandauInput (m+1)) :
    eval (m+1) (RandomizedRanks.payoff F m t pi.mass) (m+1) m ((m+1).choose 2) =
      ((((m+1 : ℕ) : ℝ) * RandomizedProbability.gammaF m n F t ⟨ht.1,ht.2.trans hFn⟩ pi : ℝ) : WithBot ℝ) := by
  rw [RandomizedProbability.gammaF_eq m n F t hF hFn ht pi]
  have hN : ((m+1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [mul_div_cancel₀ _ hN]
  exact eval_eq_maxObjective F m t pi.mass hLandau

end
end MEJF.RankDP
