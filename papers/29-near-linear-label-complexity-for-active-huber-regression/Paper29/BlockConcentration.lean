import Paper29.ConcentrationMGF
import Paper29.EventTools

noncomputable section
open scoped BigOperators Classical
namespace Paper29.HardDistribution

def blockMass {N : ℕ} (p : ℝ) (y : Fin N → Bool) : ℝ := ∏ k, bitMass p (y k)

def centeredSum {N : ℕ} (p : ℝ) (y : Fin N → Bool) : ℝ := ∑ k, (bit (y k)-p)

theorem blockMass_nonneg {N : ℕ} (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (y : Fin N → Bool) :
    0 ≤ blockMass p y := Finset.prod_nonneg (fun k _ => bitMass_nonneg p hp hp1 _)

theorem blockMass_total (N : ℕ) (p : ℝ) : (∑ y : Fin N → Bool, blockMass p y) = 1 := by
  unfold blockMass
  rw [← Fintype.prod_sum]
  simp only [bitMass_total, Finset.prod_const_one]

/-- Product MGF for the actual independent Bernoulli block, from the scalar
bounded-variable MGF theorem already available in the pinned Mathlib. -/
theorem block_mgf {N : ℕ} (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) :
    (∑ y : Fin N → Bool, blockMass p y * Real.exp (t*centeredSum p y)) ≤
      Real.exp ((N:ℝ)*t^2/8) := by
  have he (y : Fin N → Bool) : blockMass p y * Real.exp (t*centeredSum p y) =
      ∏ k, bitMass p (y k)*Real.exp (t*(bit (y k)-p)) := by
    rw [Finset.prod_mul_distrib, ← Real.exp_sum]
    unfold blockMass centeredSum
    rw [Finset.mul_sum]
  simp_rw [he]
  rw [← Fintype.prod_sum (fun _k : Fin N => fun b : Bool => bitMass p b * Real.exp (t*(bit b-p)))]
  calc
    _ ≤ ∏ _k : Fin N, Real.exp (t^2/8) := by
      apply Finset.prod_le_prod
      · intro k _
        exact Finset.sum_nonneg (fun b _ => mul_nonneg (bitMass_nonneg p hp hp1 b) (Real.exp_pos _).le)
      · intro k _
        exact bernoulli_mgf_bound p hp hp1 t
    _ = _ := by
      rw [← Real.exp_sum]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      congr 1
      ring

/-- Both one-sided Hoeffding estimates, proved on the literal finite block law. -/
theorem block_hoeffding {N : ℕ} (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) :
    Sampling.eventMass (blockMass p) (Finset.univ.filter (fun y : Fin N → Bool =>
      centeredSum p y ≤ -(N:ℝ)*a)) ≤ Real.exp (-2*(N:ℝ)*a^2) ∧
    Sampling.eventMass (blockMass p) (Finset.univ.filter (fun y : Fin N → Bool =>
      (N:ℝ)*a ≤ centeredSum p y)) ≤ Real.exp (-2*(N:ℝ)*a^2) := by
  have htail (t : ℝ) (ht : t = -4*a ∨ t = 4*a)
      (E : Finset (Fin N → Bool))
      (hE : ∀ y ∈ E, 4*(N:ℝ)*a^2 ≤ t*centeredSum p y) :
      Sampling.eventMass (blockMass p) E ≤ Real.exp (-2*(N:ℝ)*a^2) := by
    have hsub : E ⊆ Finset.univ.filter (fun y : Fin N → Bool =>
        Real.exp (4*(N:ℝ)*a^2) ≤ Real.exp (t*centeredSum p y)) := by
      intro y hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Real.exp_le_exp.mpr (hE y hy)⟩
    have hm := Sampling.finite_markov (blockMass p) (fun y : Fin N → Bool => Real.exp (t*centeredSum p y))
      (blockMass_nonneg p hp hp1) (fun _ => (Real.exp_pos _).le)
      (Real.exp (4*(N:ℝ)*a^2)) (Real.exp_pos _)
    have hh := (ProcessTools.eventMass_mono (blockMass p) (blockMass_nonneg p hp hp1) hsub).trans hm
    apply hh.trans
    calc
      _ ≤ Real.exp ((N:ℝ)*t^2/8)/Real.exp (4*(N:ℝ)*a^2) :=
        div_le_div_of_nonneg_right (block_mgf p hp hp1 t) (Real.exp_pos _).le
      _ = _ := by
        rw [← Real.exp_sub]
        congr 1
        rcases ht with rfl | rfl <;> ring
  constructor
  · apply htail (-4*a) (Or.inl rfl) _
    intro y hy
    have hh := (Finset.mem_filter.mp hy).2
    have hm := mul_le_mul_of_nonpos_left hh (show -4*a ≤ 0 by linarith)
    nlinarith only [hm]
  · apply htail (4*a) (Or.inr rfl) _
    intro y hy
    have hh := (Finset.mem_filter.mp hy).2
    have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ 4*a by linarith)
    nlinarith only [hm]

end Paper29.HardDistribution
