import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Rare-event weights (4.1), the explicit exponent bounds (B.1), and the
stage-dependent prefixMass products in Corollary B.3. -/
namespace Paper36.Weights
noncomputable section
open scoped BigOperators

/-- Exactly the squared high-count weight of (4.1). -/
def Wsq (α : ℝ) (H : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 (H - 1), ((H - h + 1 : ℕ) : ℝ)^2 * (α⁻¹)^h

/-- Zero is inserted only to implement the paper's empty-maximum convention. -/
def lowTerm (α : ℝ) (H h : ℕ) : ℝ :=
  if h = 0 then 0 else ((H - h : ℕ) : ℝ) * (α⁻¹)^h

def w (α : ℝ) (H : ℕ) : ℝ :=
  (insert 0 (Finset.Icc 1 (H - 1))).sup' (by simp) (lowTerm α H)

@[simp] theorem Wsq_zero (α : ℝ) : Wsq α 0 = 0 := by simp [Wsq]
@[simp] theorem Wsq_one (α : ℝ) : Wsq α 1 = 0 := by simp [Wsq]
@[simp] theorem w_zero (α : ℝ) : w α 0 = 0 := by simp [w, lowTerm]
@[simp] theorem w_one (α : ℝ) : w α 1 = 0 := by simp [w, lowTerm]

theorem Wsq_nonneg {α : ℝ} (hα : 0 < α) (H : ℕ) : 0 ≤ Wsq α H := by
  unfold Wsq
  exact Finset.sum_nonneg fun _ _ => by positivity

theorem w_nonneg (α : ℝ) (H : ℕ) : 0 ≤ w α H := by
  have h := Finset.le_sup' (lowTerm α H)
    (show 0 ∈ insert 0 (Finset.Icc 1 (H - 1)) by simp)
  simpa [lowTerm, w] using h

private theorem inv_one_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) : 1 ≤ α⁻¹ := by
  rw [inv_eq_one_div]
  apply (le_div_iff₀ hα).2
  simpa using hα1

/-- The final stage alone gives the lower side of (B.1). -/
theorem Wsq_lower {α : ℝ} (hα : 0 < α) {H : ℕ} (hH : 2 ≤ H) :
    4 * (α⁻¹)^(H - 1) ≤ Wsq α H := by
  have hm : H - 1 ∈ Finset.Icc 1 (H - 1) := by simp; omega
  have heq : H - (H - 1) + 1 = 2 := by omega
  have ht := Finset.single_le_sum
    (f := fun h : ℕ => ((H - h + 1 : ℕ) : ℝ)^2 * (α⁻¹)^h)
    (fun _ _ => by positivity) hm
  norm_num [Wsq, heq] at ht
  simpa [Wsq] using ht

/-- The upper high-count weight bound of (B.1), with the horizon factor explicit. -/
theorem Wsq_upper {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (H : ℕ) :
    Wsq α H ≤ (H : ℝ)^3 * (α⁻¹)^(H - 1) := by
  have hi := inv_one_le hα hα1
  have hterm : ∀ h ∈ Finset.Icc 1 (H - 1),
      ((H - h + 1 : ℕ) : ℝ)^2 * (α⁻¹)^h ≤ (H : ℝ)^2 * (α⁻¹)^(H - 1) := by
    intro h hh
    have hhh := Finset.mem_Icc.1 hh
    have hnat : H - h + 1 ≤ H := by omega
    have hcast : ((H - h + 1 : ℕ) : ℝ) ≤ H := by exact_mod_cast hnat
    have hsquare : (((H - h + 1 : ℕ) : ℝ))^2 ≤ (H : ℝ)^2 := by
      have hn0 : (0 : ℝ) ≤ (H - h + 1 : ℕ) := Nat.cast_nonneg _
      have hH0 : (0 : ℝ) ≤ H := Nat.cast_nonneg _
      nlinarith
    exact mul_le_mul hsquare (pow_le_pow_right₀ hi hhh.2)
      (by positivity) (sq_nonneg _)
  unfold Wsq
  calc
    _ ≤ ∑ _h ∈ Finset.Icc 1 (H - 1), (H : ℝ)^2 * (α⁻¹)^(H - 1) :=
      Finset.sum_le_sum hterm
    _ = (H - 1 : ℕ) * ((H : ℝ)^2 * (α⁻¹)^(H - 1)) := by simp
    _ ≤ (H : ℝ) * ((H : ℝ)^2 * (α⁻¹)^(H - 1)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast Nat.sub_le H 1
    _ = _ := by ring

/-- The low-count maximum bound in (B.1). -/
theorem w_upper {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (H : ℕ) :
    w α H ≤ (H : ℝ) * (α⁻¹)^(H - 1) := by
  have hi := inv_one_le hα hα1
  unfold w
  apply Finset.sup'_le
  intro h hh
  rcases Finset.mem_insert.1 hh with rfl | hh
  · simp [lowTerm]
    positivity
  · have hhh := Finset.mem_Icc.1 hh
    have hh0 : h ≠ 0 := by omega
    rw [lowTerm, if_neg hh0]
    exact mul_le_mul (by exact_mod_cast Nat.sub_le H h)
      (pow_le_pow_right₀ hi hhh.2) (by positivity) (Nat.cast_nonneg _)

/-- Polynomial endpoint weights at α=1; no horizon powers are hidden. -/
theorem expectation_endpoint (H : ℕ) :
    Wsq 1 H ≤ (H : ℝ)^3 ∧ w 1 H ≤ H := by
  constructor
  · simpa using Wsq_upper (α := 1) (by norm_num) (by norm_num) H
  · simpa using w_upper (α := 1) (by norm_num) (by norm_num) H

/-- Stage indexing is 1,...,h, exactly as in Corollary B.3. -/
def prefixMass (α : ℕ → ℝ) (h : ℕ) : ℝ := ∏ j ∈ Finset.Icc 1 h, α j

def stageWsq (α : ℕ → ℝ) (H : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 (H - 1), ((H - h + 1 : ℕ) : ℝ)^2 / prefixMass α h

def stageLowTerm (α : ℕ → ℝ) (H h : ℕ) : ℝ :=
  if h = 0 then 0 else ((H - h : ℕ) : ℝ) / prefixMass α h

def stagew (α : ℕ → ℝ) (H : ℕ) : ℝ :=
  (insert 0 (Finset.Icc 1 (H - 1))).sup' (by simp) (stageLowTerm α H)

@[simp] theorem prefixMass_zero (α : ℕ → ℝ) : prefixMass α 0 = 1 := by simp [prefixMass]

theorem prefixMass_pos {α : ℕ → ℝ} {h : ℕ} (hα : ∀ j ∈ Finset.Icc 1 h, 0 < α j) :
    0 < prefixMass α h := Finset.prod_pos hα

/-- Multiplying pointwise envelope-density bounds yields precisely P_h^{-1}. -/
theorem prefixMass_density_domination {α d : ℕ → ℝ} {h : ℕ}
    (hα : ∀ j ∈ Finset.Icc 1 h, 0 < α j)
    (hd : ∀ j ∈ Finset.Icc 1 h, 0 ≤ d j)
    (hcap : ∀ j ∈ Finset.Icc 1 h, d j ≤ (α j)⁻¹) :
    (∏ j ∈ Finset.Icc 1 h, d j) ≤ (prefixMass α h)⁻¹ := by
  rw [prefixMass, ← Finset.prod_inv_distrib]
  exact Finset.prod_le_prod hd hcap

/-- Constant stage masses recover the homogeneous weight without any index shift. -/
@[simp] theorem prefixMass_constant (α : ℝ) (h : ℕ) : prefixMass (fun _ => α) h = α^h := by
  simp [prefixMass]

theorem stageWsq_constant (α : ℝ) (H : ℕ) : stageWsq (fun _ => α) H = Wsq α H := by
  unfold stageWsq Wsq
  apply Finset.sum_congr rfl
  intro h hh
  simp [prefixMass_constant, div_eq_mul_inv, inv_pow]

theorem stagew_constant (α : ℝ) (H : ℕ) : stagew (fun _ => α) H = w α H := by
  unfold stagew w
  congr 1
  funext h
  simp [stageLowTerm, lowTerm, prefixMass_constant, div_eq_mul_inv, inv_pow]

/-- The prefix update explicitly includes the current mass. -/
theorem prefixMass_succ (α : ℕ → ℝ) (h : ℕ) :
    prefixMass α (h + 1) = prefixMass α h * α (h + 1) := by
  exact Finset.prod_Icc_succ_top (by omega) α

theorem prefixMass_step (α : ℕ → ℝ) {h : ℕ} (hh : 1 ≤ h) :
    prefixMass α h = prefixMass α (h - 1) * α h := by
  have heq : h - 1 + 1 = h := by omega
  simpa [heq] using prefixMass_succ α (h - 1)

/-- The local TV coefficient and preceding density cap combine into 1/P_h. -/
theorem stage_low_coefficient (α : ℕ → ℝ) (b : ℝ) {h : ℕ} (hh : 1 ≤ h) :
    (b / α h) / prefixMass α (h - 1) = b / prefixMass α h := by
  rw [prefixMass_step α hh, div_div]
  congr 1
  ring

/-- Squaring the local Hellinger coefficient and multiplying by preceding
occupancy domination yields exactly the high-count 8/P_h coefficient. -/
theorem stage_high_coefficient {α : ℕ → ℝ} (b : ℝ) {h : ℕ} (hh : 1 ≤ h)
    (hα : 0 < α h) :
    (2 * Real.sqrt 2 * b / Real.sqrt (α h))^2 / prefixMass α (h - 1) =
      8 * b^2 / prefixMass α h := by
  rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hα.le, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [prefixMass_step α hh, div_div]
  congr 1 <;> ring

/-- With a nonempty transition index set, the inserted zero is immaterial:
this is literally the maximum in (4.1). -/
theorem w_eq_paper_max {α : ℝ} (hα : 0 < α) {H : ℕ} (hH : 2 ≤ H) :
    w α H = (Finset.Icc 1 (H - 1)).sup'
      (by refine ⟨1, ?_⟩; simp; omega)
      (fun h => ((H - h : ℕ) : ℝ) * (α⁻¹)^h) := by
  have hm : 1 ∈ Finset.Icc 1 (H - 1) := by simp; omega
  have hn : (Finset.Icc 1 (H - 1)).Nonempty := ⟨1, hm⟩
  have hnonneg : 0 ≤ (Finset.Icc 1 (H - 1)).sup' hn
      (fun h => ((H - h : ℕ) : ℝ) * (α⁻¹)^h) := by
    exact (show 0 ≤ ((H - 1 : ℕ) : ℝ) * (α⁻¹)^1 by positivity).trans
      (Finset.le_sup' (fun h : ℕ => ((H - h : ℕ) : ℝ) * (α⁻¹)^h) hm)
  apply le_antisymm
  · unfold w
    apply Finset.sup'_le
    intro h hh
    rcases Finset.mem_insert.1 hh with rfl | hh
    · simpa [lowTerm] using hnonneg
    · have hh0 : h ≠ 0 := by have := (Finset.mem_Icc.1 hh).1; omega
      rw [lowTerm, if_neg hh0]
      exact Finset.le_sup' (fun h : ℕ => ((H - h : ℕ) : ℝ) * (α⁻¹)^h) hh
  · apply Finset.sup'_le
    intro h hh
    have hh0 : h ≠ 0 := by have := (Finset.mem_Icc.1 hh).1; omega
    have ht := Finset.le_sup' (lowTerm α H)
      (show h ∈ insert 0 (Finset.Icc 1 (H - 1)) from Finset.mem_insert_of_mem hh)
    simpa [lowTerm, hh0, w] using ht

/-- The final-stage mass is absent from transition-error weights, as stated in B.3. -/
theorem stageWsq_congr {α β : ℕ → ℝ} {H : ℕ}
    (heq : ∀ j ∈ Finset.Icc 1 (H - 1), α j = β j) :
    stageWsq α H = stageWsq β H := by
  unfold stageWsq
  apply Finset.sum_congr rfl
  intro h hh
  have hp : prefixMass α h = prefixMass β h := by
    apply Finset.prod_congr rfl
    intro j hj
    apply heq
    have hh' := Finset.mem_Icc.1 hh
    have hj' := Finset.mem_Icc.1 hj
    exact Finset.mem_Icc.2 ⟨hj'.1, hj'.2.trans hh'.2⟩
  rw [hp]

/-- The nonnegative weight itself is the square root of the source sum. -/
def W (α : ℝ) (H : ℕ) : ℝ := Real.sqrt (Wsq α H)

theorem W_nonneg (α : ℝ) (H : ℕ) : 0 ≤ W α H := Real.sqrt_nonneg _
theorem W_sq {α : ℝ} (hα : 0 < α) (H : ℕ) : W α H ^ 2 = Wsq α H :=
  Real.sq_sqrt (Wsq_nonneg hα H)
@[simp] theorem W_one (α : ℝ) : W α 1 = 0 := by simp [W]
@[simp] theorem W_zero (α : ℝ) : W α 0 = 0 := by simp [W]

theorem prefixMass_congr {α β : ℕ → ℝ} {h : ℕ}
    (heq : ∀ j ∈ Finset.Icc 1 h, α j = β j) : prefixMass α h = prefixMass β h :=
  Finset.prod_congr rfl heq

/-- Both weights are insensitive to α_H and every later mass. -/
theorem stagew_congr {α β : ℕ → ℝ} {H : ℕ}
    (heq : ∀ j ∈ Finset.Icc 1 (H - 1), α j = β j) : stagew α H = stagew β H := by
  have hfun : ∀ h ∈ insert 0 (Finset.Icc 1 (H - 1)),
      stageLowTerm α H h = stageLowTerm β H h := by
    intro h hh
    rcases Finset.mem_insert.1 hh with rfl | hh
    · simp [stageLowTerm]
    · have hp : prefixMass α h = prefixMass β h := by
        apply prefixMass_congr
        intro j hj
        exact heq j (Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hj).1,
          (Finset.mem_Icc.1 hj).2.trans (Finset.mem_Icc.1 hh).2⟩)
      simp only [stageLowTerm, hp]
  apply le_antisymm
  · unfold stagew
    apply Finset.sup'_le
    intro h hh
    rw [hfun h hh]
    exact Finset.le_sup' (stageLowTerm β H) hh
  · unfold stagew
    apply Finset.sup'_le
    intro h hh
    rw [← hfun h hh]
    exact Finset.le_sup' (stageLowTerm α H) hh

end
end Paper36.Weights
