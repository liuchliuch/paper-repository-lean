import Paper15.LPOptimizer
import Paper15.Quadrature
import Mathlib.Algebra.BigOperators.Ring.Finset

noncomputable section
namespace Paper15
open Finset BigOperators

/-- A probability law on an arbitrary finite source alphabet. -/
structure Law (α : Type*) [Fintype α] where
  weight : α → ℝ
  nonneg : ∀ x, 0 ≤ weight x
  sum_eq : ∑ x, weight x = 1

namespace Law
variable {α β : Type*} [Fintype α] [Fintype β]
instance : CoeFun (Law α) (fun _ => α → ℝ) := ⟨Law.weight⟩
def avg (q : Law α) (f : α → ℝ) : ℝ := ∑ x, q x * f x
lemma avg_one (q : Law α) : q.avg (fun _ => 1) = 1 := by simpa [avg] using q.sum_eq
lemma avg_const (q : Law α) (c : ℝ) : q.avg (fun _ => c) = c := by
  simp only [avg, ← sum_mul, q.sum_eq, one_mul]
lemma avg_add (q : Law α) (f g : α → ℝ) :
    q.avg (fun x => f x + g x) = q.avg f + q.avg g := by simp [avg, mul_add, sum_add_distrib]
lemma avg_mul (q : Law α) (c : ℝ) (f : α → ℝ) :
    q.avg (fun x => c * f x) = c * q.avg f := by simp [avg, mul_left_comm, ← mul_sum]
lemma avg_comm (q : Law α) (r : Law β) (f : α → β → ℝ) :
    q.avg (fun x => r.avg (f x)) = r.avg (fun y => q.avg (fun x => f x y)) := by
  simp only [avg, mul_sum]
  rw [sum_comm]
  congr 1
  funext y
  congr 1
  funext x
  ring

def prod (q : Law α) (r : Law β) : Law (α × β) where
  weight p := q p.1 * r p.2
  nonneg p := mul_nonneg (q.nonneg _) (r.nonneg _)
  sum_eq := by simp [Fintype.sum_prod_type, ← mul_sum, ← sum_mul, q.sum_eq, r.sum_eq]
lemma avg_prod (q : Law α) (r : Law β) (f : α × β → ℝ) :
    (q.prod r).avg f = q.avg (fun x => r.avg (fun y => f (x,y))) := by
  simp only [avg, prod, Fintype.sum_prod_type, mul_sum]
  congr 1
  funext x
  congr 1
  funext y
  ring

def pi {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (q : ∀ i, Law (κ i)) : Law (∀ i, κ i) where
  weight x := ∏ i, q i (x i)
  nonneg x := prod_nonneg (fun i _ => (q i).nonneg _)
  sum_eq := by rw [← Fintype.prod_sum]; simp [Law.sum_eq]

lemma avg_pi_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] (q : ∀ i, Law (κ i))
    (i : ι) (f : κ i → ℝ) :
    (Law.pi q).avg (fun x => f (x i)) = (q i).avg f := by
  classical
  let g : ∀ j, κ j → ℝ := fun j x => if h : j = i then q j x * f (h ▸ x) else q j x
  have heq (x : ∀ j, κ j) : (∏ j, q j (x j)) * f (x i) = ∏ j, g j (x j) := by
    rw [← prod_erase_mul _ _ (mem_univ i), ← prod_erase_mul _ _ (mem_univ i)]
    simp only [g, dif_pos rfl]
    rw [mul_assoc]
    congr 1
    apply prod_congr rfl
    intro j hj
    simp only [mem_erase, ne_eq, mem_univ, and_true] at hj
    simp [g, hj]
  simp only [avg, pi]
  simp_rw [heq]
  rw [← Fintype.prod_sum, ← prod_erase_mul _ _ (mem_univ i)]
  have hprod : (∏ j ∈ univ.erase i, ∑ x, g j x) = 1 := by
    apply prod_eq_one
    intro j hj
    have hji : j ≠ i := (mem_erase.mp hj).1
    simpa [g,hji] using (q j).sum_eq
  rw [hprod, one_mul]
  simp [g,avg]

/-- Binary kernel with prescribed conditional mean in [-1,1]. -/
def binary (m : ℝ) (hm : m ∈ Set.Icc (-1:ℝ) 1) : Law Bool where
  weight b := if b then (1+m)/2 else (1-m)/2
  nonneg b := by cases b <;> simp <;> linarith [hm.1,hm.2]
  sum_eq := by simp [Fintype.sum_bool]; ring

def boolSign (b : Bool) : ℝ := if b then 1 else -1
lemma boolSign_legal (b : Bool) : legalSign (boolSign b) := by cases b <;> simp [boolSign,legalSign]
lemma binary_avg (m : ℝ) (hm : m ∈ Set.Icc (-1:ℝ) 1) :
    (binary m hm).avg boolSign = m := by simp [avg,binary,boolSign,Fintype.sum_bool]; ring

end Law
end Paper15
