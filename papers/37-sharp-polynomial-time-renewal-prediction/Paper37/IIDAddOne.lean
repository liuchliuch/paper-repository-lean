import Paper37.KnownSupport
import Paper37.HazardChain

/-! The actual iid count law and its add-one estimation guarantee. -/
noncomputable section
namespace Paper37.IIDAddOne
open scoped BigOperators
open Paper37.Compression Paper37.Compression.Distribution Paper37.KnownSupport

lemma binomialWeight_zero (k : ℕ) (p : ℝ) :
    binomialWeight (k+1) p 0 = (1-p)*binomialWeight k p 0 := by
  simp [binomialWeight,pow_succ]
  ring

lemma binomialWeight_succ (k r : ℕ) (p : ℝ) :
    binomialWeight (k+1) p (r+1) =
      p*binomialWeight k p r+(1-p)*binomialWeight k p (r+1) := by
  by_cases hr : r < k
  · have he : k-r = (k-(r+1))+1 := by omega
    unfold binomialWeight
    rw [Nat.choose_succ_succ]
    push_cast
    rw [he, pow_succ, pow_succ]
    ring
  · by_cases he : r=k
    · subst r
      simp [binomialWeight,pow_succ]
      ring
    · have hkr : k < r := by omega
      simp [binomialWeight, Nat.choose_eq_zero_of_lt hkr,
        Nat.choose_eq_zero_of_lt (show k < r+1 by omega),
        Nat.choose_eq_zero_of_lt (show k+1 < r+1 by omega)]

universe u
abbrev Sample (α : Type u) := Paper37.Compression.History.{u,u} α

def iidLaw {α : Type*} [Fintype α] (p : Distribution α) : (k : ℕ) → Distribution (Sample α k)
  | 0 => point PUnit.unit
  | k+1 => joint (iidLaw p k) (fun _ => p)

def count {α : Type*} [Fintype α] [DecidableEq α] (j : α) : (k : ℕ) → Sample α k → ℕ
  | 0,_ => 0
  | k+1,(s,a) => count j k s + if a=j then 1 else 0

lemma count_sum {α : Type*} [Fintype α] [DecidableEq α] (k : ℕ) (s : Sample α k) :
    (∑ j, count j k s) = k := by
  induction k with
  | zero => simp [count]
  | succ k ih =>
    rcases s with ⟨s,a⟩
    simp only [count,Finset.sum_add_distrib,ih]
    simp

def countMass {Ω : Type*} [Fintype Ω] (w : Distribution Ω) (C : Ω → ℕ) (r : ℕ) : ℝ :=
  ∑ ω, if C ω=r then w ω else 0

lemma sum_symbol_indicator {α : Type*} [Fintype α] [DecidableEq α]
    (p : Distribution α) (j : α) (t r : ℕ) :
    (∑ a, p a*(if t+(if a=j then 1 else 0)=r then (1:ℝ) else 0)) =
      p j*(if t+1=r then 1 else 0)+(1-p j)*(if t=r then 1 else 0) := by
  by_cases h1 : t+1=r
  · have h0 : t≠r := by omega
    have he : ∀ a, (t+(if a=j then 1 else 0)=r) ↔ a=j := by
      intro a; by_cases ha : a=j <;> simp [ha,h1,h0]
    simp_rw [he]
    simp [h1,h0]
  · by_cases h0 : t=r
    · have he : ∀ a, (t+(if a=j then 1 else 0)=r) ↔ a≠j := by
        intro a; by_cases ha : a=j <;> simp [ha,h1,h0]
      simp_rw [he]
      simp only [h1,h0,↓reduceIte,mul_zero,zero_add,mul_one]
      have hs : (∑ a, if a=j then p a else 0)+(∑ a, if a≠j then p a else 0)=1 := by
        rw [← Finset.sum_add_distrib]
        convert p.total using 1
        apply Finset.sum_congr rfl
        intro a ha
        by_cases he : a=j <;> simp [he]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hs
      simp_rw [mul_ite,mul_one,mul_zero]
      simp only [show r+1 ≠ r by omega, if_false, zero_add]
      linarith
    · have he : ∀ a, ¬ t+(if a=j then 1 else 0)=r := by
        intro a; by_cases ha : a=j <;> simp [ha,h1,h0]
      simp [he,h1,h0]

lemma countMass_step {α : Type*} [Fintype α] [DecidableEq α]
    (p : Distribution α) (k : ℕ) (j : α) (r : ℕ) :
    countMass (iidLaw p (k+1)) (count j (k+1)) r =
      p j*(∑ s, if count j k s+1=r then iidLaw p k s else 0) +
        (1-p j)*countMass (iidLaw p k) (count j k) r := by
  unfold countMass
  change (∑ z : Sample α k × α,
    if count j k z.1+(if z.2=j then 1 else 0)=r then iidLaw p k z.1*p z.2 else 0) = _
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ s, iidLaw p k s*(∑ a, p a*(if count j k s+(if a=j then 1 else 0)=r then (1:ℝ) else 0)) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      split_ifs <;> simp
    _ = ∑ s, iidLaw p k s*(p j*(if count j k s+1=r then 1 else 0)+
        (1-p j)*(if count j k s=r then 1 else 0)) := by simp_rw [sum_symbol_indicator]
    _ = ∑ s, (p j*(if count j k s+1=r then iidLaw p k s else 0)+
        (1-p j)*(if count j k s=r then iidLaw p k s else 0)) := by
      apply Finset.sum_congr rfl
      intro s hs
      split_ifs <;> ring
    _ = _ := by rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]

/-- A cell count in k iid finite-alphabet observations has exactly the binomial
marginal used in the paper's add-one calculation. -/
theorem iid_count_binomial {α : Type*} [Fintype α] [DecidableEq α]
    (p : Distribution α) (k : ℕ) (j : α) (r : ℕ) :
    countMass (iidLaw p k) (count j k) r = binomialWeight k (p j) r := by
  induction k generalizing r with
  | zero =>
    unfold countMass
    change (∑ s : PUnit, if (0:ℕ)=r then (point PUnit.unit) s else 0) = _
    cases r <;> simp [point,binomialWeight]
  | succ k ih =>
    rw [countMass_step]
    cases r with
    | zero =>
      simp only [Nat.add_eq_zero_iff,Nat.succ_ne_zero,and_false,↓reduceIte,Finset.sum_const_zero,mul_zero,zero_add]
      rw [ih,binomialWeight_zero]
    | succ r =>
      simp only [Nat.add_right_cancel_iff]
      change p j*countMass (iidLaw p k) (count j k) r+
        (1-p j)*countMass (iidLaw p k) (count j k) (r+1) = _
      rw [ih,ih,binomialWeight_succ]

/-- The actual iid add-one estimator has expected categorical KL at most
(B−1)/(k+1), with no count-marginal assumption left in the theorem. -/
theorem iid_addOne_expectedKL_le {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α]
    (p : Distribution α) (k : ℕ) :
    (∑ s, iidLaw p k s*Distribution.kl p
      (addOne k (fun j => count j k s) (count_sum k s))) ≤
        ((Fintype.card α:ℝ)-1)/((k:ℝ)+1) := by
  apply addOne_expectedKL_le p (iidLaw p k) k (fun s j => count j k s) (count_sum k)
  intro j r hr
  exact iid_count_binomial p k j r

end Paper37.IIDAddOne
