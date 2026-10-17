import SemidegreeExt.ClosedForm
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic
open Real Filter Topology
namespace SemidegreeExt

/-- The explicit feasibility threshold used in the paper. -/
noncomputable def NAlpha (α : ℝ) : ℕ := Nat.ceil ((1-α)⁻¹)

lemma dense_feasible (α : ℝ) (hα : 0 < α) (hα' : α < 1)
    (n : ℕ) (hn : NAlpha α ≤ n) : 0 < n ∧ Nat.ceil (α*n) < n := by
  have ha : 0 < 1-α := by linarith
  have hN : (1-α)⁻¹ ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hn0 : (0 : ℝ) < n := (inv_pos.mpr ha).trans_le hN
  have hn1 : 1 ≤ (n : ℝ)*(1-α) := (inv_le_iff_one_le_mul₀ ha).mp hN
  have hnNat : 0 < n := by exact_mod_cast hn0
  have hceil : Nat.ceil (α*n) ≤ n-1 := by
    apply Nat.ceil_le.mpr
    have hcast : ((n-1 : ℕ) : ℝ) = n-1 := by rw [Nat.cast_sub (by omega)]; norm_num
    rw [hcast]
    nlinarith
  exact ⟨hnNat, by omega⟩

lemma CReal_normalized (n d : ℕ) (hn : 0 < n) (hd : d < n) :
    CReal n d / n =
      ((2-(n : ℝ)⁻¹) - Real.sqrt ((2-(n : ℝ)⁻¹)^2 -
        4*((d : ℝ)/n)*((d : ℝ)/n+(n : ℝ)⁻¹)))/2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hrad : ((2*(n : ℝ)-1)^2 - 4*(d : ℝ)*(d+1)) / (n : ℝ)^2 =
      (2-(n : ℝ)⁻¹)^2 - 4*((d : ℝ)/n)*((d : ℝ)/n+(n : ℝ)⁻¹) := by
    field_simp
    <;> ring
  have hs : Real.sqrt ((2-(n : ℝ)⁻¹)^2 -
      4*((d : ℝ)/n)*((d : ℝ)/n+(n : ℝ)⁻¹)) =
      Real.sqrt ((2*(n : ℝ)-1)^2-4*(d : ℝ)*(d+1)) / n := by
    rw [← hrad, Real.sqrt_div (discriminant_nonneg n d hd), Real.sqrt_sq hnR.le]
  rw [hs]
  unfold CReal
  field_simp
  <;> ring

/-- Corollary 1.2: the exact integer thresholds have the claimed dense limit. -/
theorem C_dense_limit (α : ℝ) (hα : 0 < α) (hα' : α < 1) :
    Tendsto (fun n : ℕ => (C n (Nat.ceil (α * n)) : ℝ) / n) atTop
      (𝓝 (1 - sqrt (1 - α^2))) := by
  have hncast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hncast
  have hd : Tendsto (fun n : ℕ => (Nat.ceil (α*n) : ℝ) / n) atTop (𝓝 α) :=
    (tendsto_nat_ceil_mul_div_atTop hα.le).comp hncast
  have htwo : Tendsto (fun n : ℕ => 2-(n : ℝ)⁻¹) atTop (𝓝 (2-0 : ℝ)) :=
    tendsto_const_nhds.sub hi
  have hfour : Tendsto (fun n : ℕ => 4*((Nat.ceil (α*n) : ℝ)/n)) atTop (𝓝 (4*α)) :=
    tendsto_const_nhds.mul hd
  have hraw := (htwo.sub (((htwo.pow 2).sub (hfour.mul (hd.add hi))).sqrt)).div_const 2
  have hlim : ((2 : ℝ) - Real.sqrt (2^2 - 4*α*(α+0)))/2 = 1-sqrt (1-α^2) := by
    rw [show (2 : ℝ)^2-4*α*(α+0) = 4*(1-α^2) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
    <;> ring
  have hnorm : Tendsto (fun n : ℕ =>
      ((2-(n : ℝ)⁻¹) - Real.sqrt ((2-(n : ℝ)⁻¹)^2 -
        4*((Nat.ceil (α*n) : ℝ)/n)*((Nat.ceil (α*n) : ℝ)/n+(n : ℝ)⁻¹)))/2)
      atTop (𝓝 (1-sqrt (1-α^2))) := by
    convert hraw using 1 <;> simp only [sub_zero, hlim]
  have hevent : ∀ᶠ n : ℕ in atTop, 0 < n ∧ Nat.ceil (α*n) < n :=
    eventually_atTop.mpr ⟨NAlpha α, fun n hn => dense_feasible α hα hα' n hn⟩
  have hrho : Tendsto (fun n : ℕ => CReal n (Nat.ceil (α*n))/n)
      atTop (𝓝 (1-sqrt (1-α^2))) := by
    apply hnorm.congr'
    filter_upwards [hevent] with n hn
    exact (CReal_normalized n _ hn.1 hn.2).symm
  have hupper : Tendsto (fun n : ℕ => CReal n (Nat.ceil (α*n))/n+(n : ℝ)⁻¹)
      atTop (𝓝 (1-sqrt (1-α^2))) := by simpa using hrho.add hi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hrho hupper
  · filter_upwards [hevent] with n hn
    rw [C_closed_form n _ hn.1 hn.2]
    exact div_le_div_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg _)
  · filter_upwards [hevent] with n hn
    rw [C_closed_form n _ hn.1 hn.2]
    have hceil := (Nat.ceil_lt_add_one (CReal_bounds n _ hn.1 hn.2).1).le
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn.1
    have h := div_le_div_of_nonneg_right hceil hnR.le
    simpa [add_div, one_div] using h
end SemidegreeExt
