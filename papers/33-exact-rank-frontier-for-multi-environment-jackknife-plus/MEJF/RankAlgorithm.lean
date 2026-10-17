import MEJF.RankFrontier
import Mathlib.Data.List.Range

/-! A costed arithmetic evaluator for Corollary 3.3. Each natural arithmetic
primitive charges one unit. A loop successor/visit charges one unit too; copying
list cells and pairing do not charge arithmetic work. The result is proved to
be the actual Pareto antichain. Costs are a property of this explicit program,
not of an unimplemented enumeration or the cardinality alone. -/
namespace MEJF.RankAlgorithm
open MEJF.RankFrontier Finset

structure Computation (α : Type*) where
  value : α
  ops : ℕ

namespace Computation

def ret (x : α) : Computation α := ⟨x,0⟩
def seq (x : Computation α) (f : α → Computation β) : Computation β :=
  ⟨(f x.value).value, x.ops+(f x.value).ops⟩

def add (x y : ℕ) : Computation ℕ := ⟨x+y,1⟩
def sub (x y : ℕ) : Computation ℕ := ⟨x-y,1⟩
def mul (x y : ℕ) : Computation ℕ := ⟨x*y,1⟩
def div (x y : ℕ) : Computation ℕ := ⟨x/y,1⟩
def tick : Computation Unit := ⟨(),1⟩

/-- Structural generation of the indices. One successor visit is charged. -/
def indices : ℕ → Computation (List ℕ)
  | 0 => ret []
  | n+1 => seq (indices n) (fun xs => seq tick (fun _ => ret (xs ++ [n])))

@[simp] lemma indices_value (n : ℕ) : (indices n).value = List.range n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [indices,Computation.seq,Computation.ret,tick,ih] using (List.range_succ (n := n)).symm

@[simp] lemma indices_ops (n : ℕ) : (indices n).ops = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [indices,Computation.seq,Computation.ret,tick,ih]

/-- Execute the arithmetic cell program on every generated index. -/
def map (f : α → Computation β) : List α → Computation (List β)
  | [] => ret []
  | x::xs => seq (f x) (fun y => seq (map f xs) (fun ys =>
      seq tick (fun _ => ret (y::ys))))

@[simp] lemma map_value (f : α → Computation β) (xs : List α) :
    (map f xs).value = xs.map (fun x => (f x).value) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [map,Computation.seq,Computation.ret,tick,ih]

lemma map_ops_of_constant (f : α → Computation β) (xs : List α) (c : ℕ)
    (h : ∀ x ∈ xs, (f x).ops = c) : (map f xs).ops = (c+1)*xs.length := by
  induction xs with
  | nil => simp [map,Computation.ret]
  | cons x xs ih =>
      have hx := h x (by simp)
      have hxs := ih (fun y hy => h y (by simp [hy]))
      simp [map,Computation.seq,Computation.ret,tick,hx,hxs,Nat.mul_add]
      omega
end Computation

open Computation

/-- Equation (3.13), evaluated by five charged arithmetic primitives. -/
def outerCell (F q k : ℕ) : Computation (ℕ×ℕ) :=
  seq (add k 1) (fun t => seq (sub t 1) (fun p => seq (mul q p) (fun a =>
    seq (div a F) (fun b => seq (sub q b) (fun ell => ret (t,ell))))))

/-- Equation (3.10), evaluated by seven charged arithmetic primitives. -/
def innerCell (F q k : ℕ) : Computation (ℕ×ℕ) :=
  seq (add k 1) (fun ell => seq (sub q ell) (fun p => seq (add p 1) (fun r =>
    seq (mul F r) (fun a => seq (sub a 1) (fun b => seq (div b q) (fun c =>
      seq (add c 1) (fun t => ret (t,ell))))))))

@[simp] lemma outerCell_value (F q k : ℕ) :
    (outerCell F q k).value = (k+1,outerTop F q (k+1)) := by
  rfl
@[simp] lemma innerCell_value (F q k : ℕ) :
    (innerCell F q k).value = (innerTop F q (k+1),k+1) := by rfl
@[simp] lemma outerCell_ops (F q k : ℕ) : (outerCell F q k).ops = 5 := by rfl
@[simp] lemma innerCell_ops (F q k : ℕ) : (innerCell F q k).ops = 7 := by rfl

/-- The executable arithmetic enumeration; the one branch comparison is charged. -/
def enumerate (F q : ℕ) : Computation (List (ℕ×ℕ)) :=
  seq tick (fun _ => if F ≤ q then
    seq (indices F) (Computation.map (outerCell F q))
  else seq (indices q) (Computation.map (innerCell F q)))

lemma range_succ_image (n : ℕ) : (Finset.range n).image (fun k => k+1) = Icc 1 n := by
  ext t
  simp only [mem_image,mem_range,mem_Icc]
  constructor
  · rintro ⟨k,hk,rfl⟩; omega
  · intro ht; exact ⟨t-1,by omega,by omega⟩

lemma toFinset_range_map (n : ℕ) (f : ℕ → ℕ×ℕ) :
    ((List.range n).map f).toFinset = (Finset.range n).image f := by
  ext p
  simp

/-- Every produced pair is exactly a maximal valid pair, with no plateau copies. -/
theorem enumerate_correct {F q : ℕ} (hF : 0 < F) (hq : 0 < q) :
    (enumerate F q).value.toFinset = paretoRanks F q := by
  classical
  by_cases h : F ≤ q
  · simp only [enumerate,Computation.seq,Computation.ret,tick,if_pos h,indices_value,map_value,
      toFinset_range_map,outerCell_value]
    rw [paretoRanks_eq_outer hF h, ← range_succ_image F,Finset.image_image]
    rfl
  · simp only [enumerate,Computation.seq,Computation.ret,tick,if_neg h,indices_value,map_value,
      toFinset_range_map,innerCell_value]
    rw [paretoRanks_eq_inner hq (by omega), ← range_succ_image q,Finset.image_image]
    rfl

/-- Exact arithmetic cost in the two program branches. -/
theorem enumerate_ops (F q : ℕ) :
    (enumerate F q).ops = if F ≤ q then 7*F+1 else 9*q+1 := by
  unfold enumerate
  by_cases h : F ≤ q
  · simp only [Computation.seq,tick,if_pos h,indices_value,indices_ops]
    rw [map_ops_of_constant _ _ 5 (by intros; rfl),List.length_range]
    omega
  · simp only [Computation.seq,tick,if_neg h,indices_value,indices_ops]
    rw [map_ops_of_constant _ _ 7 (by intros; rfl),List.length_range]
    omega

/-- An explicit uniform linear bound proves the source unit-cost arithmetic
claim `O(min F q)`; the additive one is the initial branch comparison. -/
theorem enumerate_ops_le (F q : ℕ) : (enumerate F q).ops ≤ 9*min F q+1 := by
  rw [enumerate_ops]
  split_ifs with h
  · rw [min_eq_left h]; omega
  · rw [min_eq_right (by omega : q ≤ F)]

/-- Uniform linear bound on the positive source domain, with no additive term. -/
theorem enumerate_linear {F q : ℕ} (hF : 0 < F) (hq : 0 < q) :
    (enumerate F q).ops ≤ 10*min F q := by
  have h := enumerate_ops_le F q
  have hp : 0 < min F q := lt_min hF hq
  omega

end MEJF.RankAlgorithm
