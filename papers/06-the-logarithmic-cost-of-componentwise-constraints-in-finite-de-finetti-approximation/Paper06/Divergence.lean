import Paper06.Basic
import Mathlib.Data.EReal.Basic

open Real BigOperators
open scoped Classical

namespace Paper06
namespace FinProb

variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]

/-- Finite absolute continuity. -/
def Supports (p q : FinProb α) : Prop := ∀ x, q.w x = 0 → p.w x = 0

/-- Relative entropy including the infinite value for a support mismatch. -/
noncomputable def kl (p q : FinProb α) : EReal :=
  if Supports p q then (klPos p q : EReal) else ⊤

theorem kl_of_support {p q : FinProb α} (h : Supports p q) :
    kl p q = (klPos p q : EReal) := if_pos h

theorem kl_of_not_support {p q : FinProb α} (h : ¬ Supports p q) :
    kl p q = ⊤ := if_neg h

theorem klPos_nonneg_of_support {p q : FinProb α} (h : Supports p q) :
    0 ≤ klPos p q := by
  have hpq (x : α) : p.w x - q.w x ≤ p.w x * log (p.w x / q.w x) := by
    by_cases hp : p.w x = 0
    · simp only [hp, zero_sub, zero_div, zero_mul]
      exact neg_nonpos.mpr (q.nonneg x)
    · have hp' : 0 < p.w x := lt_of_le_of_ne (p.nonneg x) (Ne.symm hp)
      have hq : q.w x ≠ 0 := fun hq => hp (h x hq)
      have hq' : 0 < q.w x := lt_of_le_of_ne (q.nonneg x) (Ne.symm hq)
      have hl := log_le_sub_one_of_pos (div_pos hq' hp')
      have heq : log (p.w x / q.w x) = - log (q.w x / p.w x) := by
        rw [log_div hp hq, log_div hq hp]
        ring
      have hm := mul_le_mul_of_nonneg_left hl (p.nonneg x)
      have hc : p.w x * (q.w x / p.w x - 1) = q.w x - p.w x := by
        field_simp
      rw [heq]
      rw [hc] at hm
      linarith
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hpq x)
  simpa only [Finset.sum_sub_distrib, p.sum_eq_one, q.sum_eq_one, sub_self] using hs

theorem kl_nonneg (p q : FinProb α) : 0 ≤ kl p q := by
  by_cases h : Supports p q
  · rw [kl_of_support h]
    exact EReal.coe_le_coe (klPos_nonneg_of_support h)
  · rw [kl_of_not_support h]
    exact le_top

/-- Pushforward of a finite probability law. -/
noncomputable def map (p : FinProb α) (f : α → β) : FinProb β where
  w y := ∑ x, if f x = y then p.w x else 0
  nonneg y := Finset.sum_nonneg (fun x _ => by split_ifs; exact p.nonneg x; exact le_rfl)
  sum_eq_one := by
    rw [Finset.sum_comm]
    simpa using p.sum_eq_one

@[simp] theorem map_w (p : FinProb α) (f : α → β) (y : β) :
    (map p f).w y = ∑ x, if f x = y then p.w x else 0 := rfl

theorem supports_map {p q : FinProb α} (h : Supports p q) (f : α → β) :
    Supports (map p f) (map q f) := by
  intro y hy
  have hz : ∀ x, (if f x = y then q.w x else 0) = 0 := by
    intro x
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => by split_ifs; exact q.nonneg x; exact le_rfl)).mp hy x (Finset.mem_univ x)
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : f x = y
  · simp only [hx, if_true] at hz ⊢
    exact h x (by simpa [hx] using hz x)
  · simp [hx]

/-- The log-sum inequality, with only finite absolute continuity required. -/
theorem log_sum {a b : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hsupp : ∀ i, b i = 0 → a i = 0) :
    (∑ i, a i) * log ((∑ i, a i) / (∑ i, b i)) ≤
      ∑ i, a i * log (a i / b i) := by
  let A := ∑ i, a i
  let B := ∑ i, b i
  have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ => ha i)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ => hb i)
  by_cases hA0 : A = 0
  · have hz : ∀ i, a i = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => ha i)).mp hA0 i (Finset.mem_univ i)
    simp [hz]
  have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
  have hB0 : B ≠ 0 := by
    intro hz
    have hbz : ∀ i, b i = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hb i)).mp hz i (Finset.mem_univ i)
    apply hA0
    exact Finset.sum_eq_zero (fun i _ => hsupp i (hbz i))
  have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
  have point (i : ι) :
      a i * log (A / B) + a i - (A / B) * b i ≤ a i * log (a i / b i) := by
    by_cases hai : a i = 0
    · simp only [hai, zero_mul, add_zero, zero_sub]
      exact neg_nonpos.mpr (mul_nonneg (div_nonneg hA hB) (hb i))
    have hai' : 0 < a i := lt_of_le_of_ne (ha i) (Ne.symm hai)
    have hbi : b i ≠ 0 := fun hbi => hai (hsupp i hbi)
    have hbi' : 0 < b i := lt_of_le_of_ne (hb i) (Ne.symm hbi)
    have hr : 0 < (A / B) / (a i / b i) := div_pos (div_pos hApos hBpos) (div_pos hai' hbi')
    have hl := log_le_sub_one_of_pos hr
    rw [log_div (div_ne_zero hA0 hB0) (div_ne_zero hai hbi)] at hl
    have hm := mul_le_mul_of_nonneg_left hl (ha i)
    have hc : a i * ((A / B) / (a i / b i) - 1) = (A / B) * b i - a i := by
      field_simp
    rw [hc] at hm
    nlinarith
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => point i)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum] at hs
  have hc : (A / B) * B = A := div_mul_cancel₀ A hB0
  change A * log (A / B) + A - (A / B) * B ≤ _ at hs
  rw [hc] at hs
  linarith

/-- Data processing under a deterministic map, including zeros in the reference law. -/
theorem klPos_map_le (p q : FinProb α) (h : Supports p q) (f : α → β) :
    klPos (map p f) (map q f) ≤ klPos p q := by
  have hl (y : β) := log_sum
    (a := fun x => if f x = y then p.w x else 0)
    (b := fun x => if f x = y then q.w x else 0)
    (fun x => by dsimp only; split_ifs; exact p.nonneg x; exact le_rfl)
    (fun x => by dsimp only; split_ifs; exact q.nonneg x; exact le_rfl)
    (fun x hx => by dsimp only at hx ⊢; split_ifs at hx ⊢ with he; exact h x hx; rfl)
  have hs := Finset.sum_le_sum (fun y (_ : y ∈ Finset.univ) => hl y)
  change klPos (map p f) (map q f) ≤ _ at hs
  rw [Finset.sum_comm] at hs
  have he (x : α) :
      (∑ y, (if f x = y then p.w x else 0) *
        log ((if f x = y then p.w x else 0) / (if f x = y then q.w x else 0))) =
        p.w x * log (p.w x / q.w x) := by simp
  simpa only [he] using hs

theorem kl_map_le (p q : FinProb α) (f : α → β) :
    kl (map p f) (map q f) ≤ kl p q := by
  by_cases h : Supports p q
  · rw [kl_of_support h, kl_of_support (supports_map h f)]
    exact EReal.coe_le_coe (klPos_map_le p q h f)
  · rw [kl_of_not_support h]
    exact le_top

/-- Joint convexity for finite mixtures; a zero reference weight is harmless. -/
theorem klPos_mixture_le (w : ι → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hw1 : ∑ j, w j = 1) (p q : ι → FinProb α)
    (h : ∀ j, 0 < w j → Supports (p j) (q j)) :
    klPos (mixture w hw hw1 p) (mixture w hw hw1 q) ≤
      ∑ j, w j * klPos (p j) (q j) := by
  have hsupp (x : α) (j : ι) (hz : w j * (q j).w x = 0) :
      w j * (p j).w x = 0 := by
    rcases mul_eq_zero.mp hz with hz | hz
    · simp [hz]
    · by_cases hj : w j = 0
      · simp [hj]
      · rw [h j (lt_of_le_of_ne (hw j) (Ne.symm hj)) x hz, mul_zero]
  have hl (x : α) := log_sum
    (a := fun j => w j * (p j).w x) (b := fun j => w j * (q j).w x)
    (fun j => mul_nonneg (hw j) ((p j).nonneg x))
    (fun j => mul_nonneg (hw j) ((q j).nonneg x)) (hsupp x)
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hl x)
  change klPos (mixture w hw hw1 p) (mixture w hw hw1 q) ≤ _ at hs
  have he (x : α) (j : ι) :
      (w j * (p j).w x) * log ((w j * (p j).w x) / (w j * (q j).w x)) =
        w j * ((p j).w x * log ((p j).w x / (q j).w x)) := by
    by_cases hj : w j = 0
    · simp [hj]
    · rw [mul_div_mul_left _ _ hj]
      ring
  simp only [he] at hs
  rw [Finset.sum_comm] at hs
  simpa only [← Finset.mul_sum, klPos] using hs

theorem supports_mixture (w : ι → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hw1 : ∑ j, w j = 1) (p q : ι → FinProb α)
    (h : ∀ j, 0 < w j → Supports (p j) (q j)) :
    Supports (mixture w hw hw1 p) (mixture w hw hw1 q) := by
  intro x hx
  have hz (j : ι) : w j * (q j).w x = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (hw j) ((q j).nonneg x))).mp hx j (Finset.mem_univ j)
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : w j = 0
  · simp [hj]
  · rw [h j (lt_of_le_of_ne (hw j) (Ne.symm hj)) x ((mul_eq_zero.mp (hz j)).resolve_left hj), mul_zero]

theorem sum_map_mul (p : FinProb α) (f : α → β) (g : β → ℝ) :
    (∑ y, (map p f).w y * g y) = ∑ x, p.w x * g (f x) := by
  simp only [map_w, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp

@[simp] theorem map_id (p : FinProb α) : map p id = p := by
  apply ext
  intro x
  simp [map_w]

@[simp] theorem map_comp {γ : Type*} [Fintype γ]
    (p : FinProb α) (f : α → β) (g : β → γ) :
    map (map p f) g = map p (g ∘ f) := by
  apply ext
  intro z
  simp only [map_w]
  have he (y : β) : (if g y = z then ∑ x, if f x = y then p.w x else 0 else 0) =
      ∑ x, if g y = z then (if f x = y then p.w x else 0) else 0 := by
    split_ifs <;> simp
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single (f x)]
  · simp
  · intro y _ hy
    simp [Ne.symm hy]
  · simp

end FinProb
end Paper06
