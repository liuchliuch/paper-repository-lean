import ELV.BesselLower
import ELV.SignedGram

/-! The actual finite Bessel argument behind Proposition 4.2. -/
noncomputable section
namespace ELV.Bessel
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- Infinitely many orthogonal witnesses cannot all have a fixed nonzero
inner product with one uniformly bounded witness. This is a real Bessel
inequality proof, without a separability assumption on K. -/
theorem orthogonal_no_uniform_bound (f : ℕ → K) (h : K)
    (horth : ∀ i j, i ≠ j → inner ℂ (f i) (f j) = 0)
    (hcross : ∀ i, (1/2 : ℝ) ≤ ‖inner ℂ (f i) h‖)
    (C : ℝ) (hC : 0 < C) (hf : ∀ i, ‖f i‖ ^ 2 ≤ C) (hh : ‖h‖ ^ 2 ≤ C) : False := by
  have hne : ∀ i, f i ≠ 0 := by
    intro i hi
    have hc := hcross i
    rw [hi,inner_zero_left,norm_zero] at hc
    norm_num at hc
  let u : ℕ → K := fun i => ((‖f i‖⁻¹ : ℝ) : ℂ) • f i
  have hu : Orthonormal ℂ u := by
    constructor
    · intro i
      have hn := norm_pos_iff.mpr (hne i)
      simp [u,norm_smul,Complex.norm_real,abs_of_pos hn,inv_mul_cancel₀ hn.ne']
    · intro i j hij
      simp only [u,inner_smul_left,inner_smul_right,horth i j hij,mul_zero]
  have hterm : ∀ i, 1/(4*C) ≤ ‖inner ℂ (u i) h‖ ^ 2 := by
    intro i
    have hn : 0 < ‖f i‖ := norm_pos_iff.mpr (hne i)
    have hc := hcross i
    have hsq : (1/4 : ℝ) ≤ ‖inner ℂ (f i) h‖ ^ 2 := by nlinarith [norm_nonneg (inner ℂ (f i) h)]
    have hid : ‖inner ℂ (u i) h‖ ^ 2 = ‖inner ℂ (f i) h‖ ^ 2 / ‖f i‖ ^ 2 := by
      simp [u,inner_smul_left,norm_mul,mul_pow,Complex.norm_real,inv_pow,div_eq_mul_inv,mul_comm]
    rw [hid]
    apply (div_le_div_iff₀ (by positivity : 0 < 4*C) (sq_pos_of_pos hn)).2
    have hm := mul_nonneg hC.le (sub_nonneg.mpr hsq)
    have hb := hf i
    nlinarith
  obtain ⟨N,hN⟩ := exists_nat_gt (4*C^2)
  have hb := hu.sum_inner_products_le h (s := Finset.range N)
  have hlo : (N : ℝ) / (4*C) ≤ ∑ i ∈ Finset.range N, ‖inner ℂ (u i) h‖ ^ 2 := by
    calc
      _ = ∑ _i ∈ Finset.range N, (1/(4*C) : ℝ) := by simp [div_eq_mul_inv]
      _ ≤ _ := Finset.sum_le_sum (fun i _ => hterm i)
  have hbound : (N : ℝ)/(4*C) ≤ C := hlo.trans (hb.trans hh)
  have hfinal := (div_le_iff₀ (by positivity : 0 < 4*C)).1 hbound
  nlinarith

end ELV.Bessel
