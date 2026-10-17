import Paper22.DensityCompact
import Paper22.UniqueMaximumDescent

/-! The exact density maximizer of the Petz moment and continuity in the input law. -/
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
noncomputable section
namespace Paper22
variable {n d : ℕ}

def petzMomentValue (V : CQChannel n d) (q : Fin n → ℝ) (α : ℝ) : ℝ :=
  (CFC.rpow (petzPowerMixture V q α) (1/α)).trace.re ^ α

def petzMomentCenter (V : CQChannel n d) (q : Fin n → ℝ) (α : ℝ) :
    Matrix (Fin d) (Fin d) ℂ :=
  (CFC.rpow (petzPowerMixture V q α) (1/α)).trace.re⁻¹ •
    CFC.rpow (petzPowerMixture V q α) (1/α)

theorem petzMomentCenter_isDensity (V : CQChannel n d) {q : Fin n → ℝ}
    (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x=1) {α : ℝ} (hα : 0 < α) :
    IsDensity (petzMomentCenter V q α) :=
  normalize_positive_matrix CFC.rpow_nonneg
    (trace_rpow_inv_pos (petzPowerMixture_nonneg V hq0 α)
      (petzPowerMixture_trace_pos V hq0 hq1 hα) hα)

theorem petzMomentValue_upper (V : CQChannel n d) {q : Fin n → ℝ}
    (hq0 : ∀ x, 0 ≤ q x) {α : ℝ} (hα : α ∈ Set.Ioo 0 1)
    {σ : Matrix (Fin d) (Fin d) ℂ} (hσ : IsDensity σ) :
    (∑ x, q x * petzTrace α (V.states x) σ) ≤ petzMomentValue V q α := by
  rw [sum_petzTrace_eq_mixture]
  exact trace_mul_rpow_le_moment (petzPowerMixture_nonneg V hq0 α) hσ hα

theorem petzMomentValue_equality (V : CQChannel n d) {q : Fin n → ℝ}
    (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x=1) {α : ℝ} (hα : α ∈ Set.Ioo 0 1)
    {σ : Matrix (Fin d) (Fin d) ℂ} (hσ : IsDensity σ) :
    (∑ x, q x * petzTrace α (V.states x) σ)=petzMomentValue V q α ↔
      σ=petzMomentCenter V q α := by
  rw [sum_petzTrace_eq_mixture]
  exact (petzMoment_unique_optimizer (petzPowerMixture_nonneg V hq0 α)
    (petzPowerMixture_trace_pos V hq0 hq1 hα.1) hα).2 σ hσ

theorem petzMomentValue_at_center (V : CQChannel n d) {q : Fin n → ℝ}
    (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x=1) {α : ℝ} (hα : α ∈ Set.Ioo 0 1) :
    (∑ x, q x * petzTrace α (V.states x) (petzMomentCenter V q α))=petzMomentValue V q α :=
  (petzMomentValue_equality V hq0 hq1 hα (petzMomentCenter_isDensity V hq0 hq1 hα.1)).mpr rfl

/-- The density maximum changes by at most the l1 distance between input laws. -/
theorem petzMomentValue_sub_le (V : CQChannel n d) {q r : Fin n → ℝ}
    (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x=1) (hr0 : ∀ x, 0 ≤ r x) (hr1 : ∑ x, r x=1)
    {α : ℝ} (hα : α ∈ Set.Ioo 0 1) :
    petzMomentValue V q α-petzMomentValue V r α ≤ ∑ x, |q x-r x| := by
  let σ := petzMomentCenter V q α
  have hσ : IsDensity σ := petzMomentCenter_isDensity V hq0 hq1 hα.1
  have hqeq := petzMomentValue_at_center V hq0 hq1 hα
  have hrle := petzMomentValue_upper V hr0 hα hσ
  have hbound (x : Fin n) : (q x-r x)*petzTrace α (V.states x) σ ≤ |q x-r x| := by
    calc _ ≤ |(q x-r x)*petzTrace α (V.states x) σ| := le_abs_self _
         _ = |q x-r x| * petzTrace α (V.states x) σ := by
           rw [abs_mul,abs_of_nonneg (petzTrace_nonneg α)]
         _ ≤ _ := mul_le_of_le_one_right (abs_nonneg _) (petzTrace_le_one (V.isDensity x) hσ hα)
  calc petzMomentValue V q α-petzMomentValue V r α ≤
        (∑ x, q x*petzTrace α (V.states x) σ)-(∑ x, r x*petzTrace α (V.states x) σ) := by
          change (∑ x, q x*petzTrace α (V.states x) σ)=petzMomentValue V q α at hqeq
          rw [hqeq]
          exact sub_le_sub_left hrle _
       _ = ∑ x, (q x-r x)*petzTrace α (V.states x) σ := by
          simp only [sub_mul,Finset.sum_sub_distrib]
       _ ≤ _ := Finset.sum_le_sum fun x _ => hbound x

theorem petzMomentValue_abs_sub_le (V : CQChannel n d) {q r : Fin n → ℝ}
    (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x=1) (hr0 : ∀ x, 0 ≤ r x) (hr1 : ∑ x, r x=1)
    {α : ℝ} (hα : α ∈ Set.Ioo 0 1) :
    |petzMomentValue V q α-petzMomentValue V r α| ≤ ∑ x, |q x-r x| := by
  have h₁ := petzMomentValue_sub_le V hq0 hq1 hr0 hr1 hα
  have h₂ := petzMomentValue_sub_le V hr0 hr1 hq0 hq1 hα
  simp only [abs_sub_comm (r _) (q _)] at h₂
  exact abs_sub_le_iff.mpr ⟨h₁,h₂⟩

theorem continuousOn_petzMomentValue (V : CQChannel n d) {α : ℝ} (hα : α ∈ Set.Ioo 0 1) :
    ContinuousOn (fun q => petzMomentValue V q α) (probabilitySimplex n) := by
  have hLip : LipschitzWith ⟨(n : ℝ),Nat.cast_nonneg n⟩
      (fun q : {q // q ∈ probabilitySimplex n} => petzMomentValue V q.val α) := by
    apply LipschitzWith.of_dist_le_mul
    intro q r
    change |petzMomentValue V q.val α-petzMomentValue V r.val α| ≤ (n : ℝ)*dist q.val r.val
    rw [dist_eq_norm]
    calc _ ≤ ∑ x, |q.val x-r.val x| := petzMomentValue_abs_sub_le V q.prop.1 q.prop.2 r.prop.1 r.prop.2 hα
         _ ≤ ∑ _ : Fin n, ‖q.val-r.val‖ := Finset.sum_le_sum fun x _ => by
           simpa only [Real.norm_eq_abs,Pi.sub_apply] using norm_le_pi_norm (q.val-r.val) x
         _ = _ := by simp [nsmul_eq_mul]
  exact continuousOn_iff_continuous_restrict.mpr hLip.continuous

end Paper22
end
