import MEJF.HeterogeneousFrontier
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Quadratic arithmetic algorithm for the exact heterogeneous frontier

The input array is already sorted. A RAM table stores all prefix sums; every
cell reads two prefix entries and performs a fixed finite arithmetic program.
Every positive (s,r) cell with 1 ≤ r ≤ s ≤ N is actually tested, and a running
maximum returns the largest feasible s. The result is proved to be the s* in
(6.9), hence also the maximum support size of an actual oriented graph.

The explicit cost model charges one unit for each natural arithmetic primitive,
comparison, Boolean conjunction, table read/write, and loop visit. Naturals are
unit-cost numbers as in the paper's arithmetic-complexity claim; this is not a
bit-complexity claim. Input sorting is outside this after-sorting algorithm.
-/
namespace MEJF.HeterogeneousAlgorithm

open Finset MEJF.HeterogeneousFrontier

structure Computation (α : Type*) where
  value : α
  ops : ℕ

namespace Computation

def ret (x : α) : Computation α := ⟨x,0⟩
def seq (x : Computation α) (f : α → Computation β) : Computation β :=
  ⟨(f x.value).value,x.ops+(f x.value).ops⟩
def add (a b : ℕ) : Computation ℕ := ⟨a+b,1⟩
def sub (a b : ℕ) : Computation ℕ := ⟨a-b,1⟩
def mul (a b : ℕ) : Computation ℕ := ⟨a*b,1⟩
def div (a b : ℕ) : Computation ℕ := ⟨a/b,1⟩
def le (a b : ℕ) : Computation Bool := ⟨decide (a≤b),1⟩
def maximum (a b : ℕ) : Computation ℕ := ⟨max a b,1⟩
def and (a b : Bool) : Computation Bool := ⟨a && b,1⟩
def readMemory (p : ℕ → ℕ) (i : ℕ) : Computation ℕ := ⟨p i,1⟩
def writeMemory (p : ℕ → ℕ) (i a : ℕ) : Computation (ℕ → ℕ) := ⟨Function.update p i a,1⟩
def tick : Computation Unit := ⟨(),1⟩

end Computation
open Computation

/-- Total memory representation of the finite sorted input; out-of-range cells
are never read by the program. -/
def extend {N : ℕ} (v : Fin N → ℕ) (i : ℕ) : ℕ := if hi : i<N then v ⟨i,hi⟩ else 0

def prefixSum (d : ℕ → ℕ) (k : ℕ) : ℕ := ∑ i ∈ range k, d i

/-- A sequential prefix scan with actual addition and table writes. -/
def prefixProgram (d : ℕ → ℕ) : ℕ → Computation (ℕ → ℕ)
  | 0 => ret (fun _ => 0)
  | k+1 => seq (prefixProgram d k) (fun p => seq (readMemory p k) (fun a =>
      seq (readMemory d k) (fun b => seq (add a b) (fun c => seq (add k 1) (fun i =>
      seq (writeMemory p i c) (fun q => seq tick (fun _ => ret q)))))))

lemma prefixProgram_value (d : ℕ → ℕ) (n : ℕ) :
    ∀ k ≤ n, (prefixProgram d n).value k = prefixSum d k := by
  induction n with
  | zero =>
      intro k hk
      have : k = 0 := by omega
      subst k
      simp [prefixProgram,ret,prefixSum]
  | succ n ih =>
      intro k hk
      by_cases hkn : k = n+1
      · subst k
        simp only [prefixProgram,seq,readMemory,add,writeMemory,tick,ret,Function.update_self]
        rw [ih n le_rfl]
        exact (Finset.sum_range_succ d n).symm
      · have hk' : k ≤ n := by omega
        simp only [prefixProgram,seq,readMemory,add,writeMemory,tick,ret]
        rw [Function.update_of_ne hkn]
        exact ih k hk'

@[simp] lemma prefixProgram_ops (d : ℕ → ℕ) (n : ℕ) : (prefixProgram d n).ops = 6*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [prefixProgram,seq,readMemory,add,writeMemory,tick,ret,ih]
      omega

/-- One constraint cell. It computes P[s]-P[s-r] and the actual capacity,
including the binomial coefficient by r(r-1)/2. -/
def cell (p : ℕ → ℕ) (N s r : ℕ) : Computation Bool :=
  seq (sub s r) (fun lo => seq (readMemory p s) (fun a => seq (readMemory p lo) (fun b =>
  seq (sub a b) (fun total => seq (sub r 1) (fun rm => seq (mul r rm) (fun c =>
  seq (div c 2) (fun pairs => seq (sub N r) (fun nr => seq (mul r nr) (fun cross =>
  seq (add pairs cross) (fun cap => le total cap))))))))))

@[simp] lemma cell_ops (p : ℕ → ℕ) (N s r : ℕ) : (cell p N s r).ops = 11 := rfl

lemma cell_value (p : ℕ → ℕ) (N s r : ℕ) :
    (cell p N s r).value = decide (p s-p (s-r) ≤ capacity N r) := by
  simp only [cell,seq,sub,readMemory,mul,div,add,le,capacity,Nat.choose_two_right]

/-- Test every r=1,...,k in one candidate support-size row. The r=0 cell is
always valid and requires no arithmetic. -/
def row (p : ℕ → ℕ) (N s : ℕ) : ℕ → Computation Bool
  | 0 => ret true
  | k+1 => seq (row p N s k) (fun a => seq (add k 1) (fun r =>
      seq (cell p N s r) (fun b => seq (Computation.and a b) (fun c =>
      seq tick (fun _ => ret c)))))

@[simp] lemma row_ops (p : ℕ → ℕ) (N s k : ℕ) : (row p N s k).ops = 14*k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [row,seq,add,cell_ops,Computation.and,tick,ret,ih]
      omega

lemma row_value (p : ℕ → ℕ) (N s k : ℕ) :
    (row p N s k).value = true ↔ ∀ r, 1 ≤ r → r ≤ k → p s-p (s-r) ≤ capacity N r := by
  induction k with
  | zero => simp [row,ret]; omega
  | succ k ih =>
      simp only [row,seq,add,Computation.and,tick,ret,Bool.and_eq_true,cell_value,decide_eq_true_eq,ih]
      constructor
      · rintro ⟨h,hnew⟩ r hr hrk
        by_cases heq : r = k+1
        · simpa [heq] using hnew
        · exact h r hr (by omega)
      · intro h
        exact ⟨fun r hr hrk => h r hr (by omega),h (k+1) (by omega) le_rfl⟩

/-- The running maximum scans every support-size row; it never replaces the
program by a feasibility oracle or by the claimed maximum. -/
def search (p : ℕ → ℕ) (N : ℕ) : ℕ → Computation ℕ
  | 0 => ret 0
  | k+1 => seq (search p N k) (fun best => seq (add k 1) (fun s =>
      seq (row p N s s) (fun ok => seq (maximum best (if ok then s else 0)) (fun next =>
      seq tick (fun _ => ret next)))))

lemma search_value (p : ℕ → ℕ) (N k : ℕ) :
    (search p N k).value = (range (k+1)).sup (fun s => if (row p N s s).value then s else 0) := by
  induction k with
  | zero => simp [search,ret]
  | succ k ih =>
      simp only [search,seq,add,maximum,tick,ret,ih]
      conv_rhs => rw [Finset.range_add_one,Finset.sup_insert]
      exact Nat.max_comm _ _

lemma search_ops (p : ℕ → ℕ) (N k : ℕ) : (search p N k).ops = 7*k*(k+1)+3*k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [search,seq,add,maximum,tick,ret,row_ops,ih]
      ring

/-- The full arithmetic program after sorted input is provided. -/
def computeAfterSorting {N : ℕ} (v : Fin N → ℕ) : Computation ℕ :=
  seq (prefixProgram (extend v) N) (fun p => search p N N)

@[simp] theorem computeAfterSorting_ops {N : ℕ} (v : Fin N → ℕ) :
    (computeAfterSorting v).ops = 7*N*N+16*N := by
  simp only [computeAfterSorting,seq,prefixProgram_ops,search_ops]
  ring

/-- Explicit quadratic bound, including table accesses and loop work. -/
theorem computeAfterSorting_quadratic {N : ℕ} (v : Fin N → ℕ) :
    (computeAfterSorting v).ops ≤ 23*(N+1)^2 := by
  rw [computeAfterSorting_ops]
  nlinarith

/-- The usual quadratic bound when the paper's number of environments is
positive; zero environments are also handled by the exact cost formula. -/
theorem computeAfterSorting_ops_le {N : ℕ} (v : Fin N → ℕ) (hN : 1 ≤ N) :
    (computeAfterSorting v).ops ≤ 23*N^2 := by
  rw [computeAfterSorting_ops]
  have hh : N ≤ N*N := by simpa using Nat.mul_le_mul_left N hN
  nlinarith

/-- The relevant suffix sum is obtained by exactly two prefix-table accesses
and one subtraction, with all source indices and multiplicities preserved. -/
lemma prefix_sub_eq_tailSum {N : ℕ} (v : Fin N → ℕ) (s r : ℕ)
    (hs : s ≤ N) (hr : r ≤ s) :
    prefixSum (extend v) s-prefixSum (extend v) (s-r) = tailSum v s r hs hr := by
  have hsplit := Finset.sum_range_add (extend v) (s-r) r
  rw [Nat.sub_add_cancel hr] at hsplit
  have htail : (∑ k ∈ range r, extend v (s-r+k)) = tailSum v s r hs hr := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k _
    have hindex : s-r+k.val < N := by have := k.isLt; omega
    simp only [extend,dif_pos hindex,tailIndex]
  unfold prefixSum
  rw [hsplit,htail]
  omega

lemma row_sortedCell {N : ℕ} (v : Fin N → ℕ) (s : ℕ) (hs : s ≤ N) :
    (row (prefixProgram (extend v) N).value N s s).value = true ↔ SortedCell v s := by
  rw [row_value]
  constructor
  · intro h
    refine ⟨hs,fun r hr => ?_⟩
    by_cases hr0 : r = 0
    · subst r
      simp [tailSum,capacity]
    · have htest := h r (by omega) hr
      rw [prefixProgram_value _ _ s hs,prefixProgram_value _ _ (s-r) (by omega),
        prefix_sub_eq_tailSum v s r hs hr] at htest
      exact htest
  · rintro ⟨hs',h⟩ r hr1 hr
    rw [prefixProgram_value _ _ s hs,prefixProgram_value _ _ (s-r) (by omega),
      prefix_sub_eq_tailSum v s r hs hr]
    exact h r hr

/-- The explicit program computes the original s* of (6.9), not a surrogate. -/
theorem computeAfterSorting_correct {N : ℕ} (w : Fin N → ℕ) :
    (computeAfterSorting (MEJF.OrderStatistics.stat w)).value = sStar w := by
  classical
  rw [computeAfterSorting,seq,search_value]
  unfold sStar sortedSizes
  apply le_antisymm
  · apply Finset.sup_le
    intro s hs
    by_cases hrow : (row (prefixProgram (extend (MEJF.OrderStatistics.stat w)) N).value N s s).value = true
    · have hcell := (row_sortedCell _ s (by have hh := mem_range.mp hs; omega : s ≤ N)).mp hrow
      have hmem : s ∈ (range (N+1)).filter (fun s => SortedCell (MEJF.OrderStatistics.stat w) s) :=
        mem_filter.mpr ⟨hs,hcell⟩
      simpa only [hrow,ite_true] using Finset.le_sup (f := id) hmem
    · have hfalse : (row (prefixProgram (extend (MEJF.OrderStatistics.stat w)) N).value N s s).value = false :=
        Bool.eq_false_iff.mpr hrow
      simp only [hfalse,Bool.false_eq_true,ite_false]
      exact Nat.zero_le _
  · apply Finset.sup_le
    intro s hs
    obtain ⟨hsrange,hcell⟩ := mem_filter.mp hs
    have hsN : s ≤ N := by have := mem_range.mp hsrange; omega
    have hrow := (row_sortedCell _ s hsN).mpr hcell
    simpa only [hrow,ite_true] using
      (Finset.le_sup (f := fun s => if (row (prefixProgram (extend (MEJF.OrderStatistics.stat w)) N).value N s s).value then s else 0) hsrange)

/-- Consequently the program computes the largest support of a genuine graph. -/
theorem computeAfterSorting_maximumSupported {N : ℕ} (w : Fin N → ℕ) :
    (computeAfterSorting (MEJF.OrderStatistics.stat w)).value = maximumSupported w := by
  rw [computeAfterSorting_correct,maximumSupported_eq_sStar]

/-- A supplied monotone input is already sorted, so the program can consume it
directly without invoking or charging any sorting procedure. -/
theorem sortedInput_correct {N : ℕ} (v : Fin N → ℕ) (hv : Monotone v) :
    (computeAfterSorting v).value = sStar v ∧
    (computeAfterSorting v).value = maximumSupported v := by
  have hsort : MEJF.OrderStatistics.stat v = v := by
    funext k
    exact MEJF.OrderStatistics.stat_of_monotone v hv k
  constructor
  · simpa only [hsort] using computeAfterSorting_correct v
  · simpa only [hsort] using computeAfterSorting_maximumSupported v

/-- The returned integer is attained by a genuine graph-support set. -/
theorem returned_support_attained {N : ℕ} (w : Fin N → ℕ) :
    ∃ S : Finset (Fin N), S.card = (computeAfterSorting (MEJF.OrderStatistics.stat w)).value ∧
      Supported w S := by
  rw [computeAfterSorting_correct]
  exact sStar_attained w

end MEJF.HeterogeneousAlgorithm
