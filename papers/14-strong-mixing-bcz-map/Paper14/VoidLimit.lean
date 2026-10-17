import Paper14.VoidProbabilityBound
import Paper14.SievePeriodMean
import Paper14.ScaleLimit

open MeasureTheory Set Function Filter Topology
namespace Paper14
noncomputable section

def primitiveVoidBoundSeq (P : ℕ) (K α : ℝ) (n : ℕ) : ℝ :=
  (K⁻¹)^2+8*(primorial P : ℝ)/betaN (primorial P) ⌊2*(n : ℝ)/K⌋₊ (α/(n : ℝ))+
  2*(α/(n : ℝ))*(⌊2*(n : ℝ)/K⌋₊ : ℝ)*SP P/betaN (primorial P) ⌊2*(n : ℝ)/K⌋₊ (α/(n : ℝ))

/-- The full three-term probability RHS has the exact original limiting
constant in (21), including the unsieved residual coefficient 2/delta_M. -/
theorem primitiveVoidBoundSeq_limit (P : ℕ) {K α : ℝ} (hK : 0 < K) (hα : 0 < α) :
    Tendsto (primitiveVoidBoundSeq P K α) atTop
      (𝓝 ((K⁻¹)^2+4*(primorial P : ℝ)*K/(α*deltaM P)+2*SP P/deltaM P)) := by
  let b : ℕ → ℝ := fun n => betaN (primorial P) ⌊2*(n : ℝ)/K⌋₊ (α/(n : ℝ))
  let c : ℝ := 2*α/K
  have hc : 0 < c := div_pos (mul_pos (by norm_num) hα) hK
  have hb : Tendsto b atTop (𝓝 (c*deltaM P)) := betaN_limit P hK α
  have hq : Tendsto (fun n : ℕ => (α/(n : ℝ))*(⌊2*(n : ℝ)/K⌋₊ : ℝ)) atTop (𝓝 c) := by
    have hh := (sieve_Q_ratio hK).const_mul α
    convert hh using 1
    · funext n
      ring
    · dsimp [c]
      ring
  have hn := (hq.const_mul 2).mul_const (SP P)
  have hbn : c*deltaM P ≠ 0 := (mul_pos hc (deltaM_pos P)).ne'
  have hh := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (K⁻¹)^2) atTop (𝓝 ((K⁻¹)^2))).add
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => 8*(primorial P : ℝ)) atTop (𝓝 (8*(primorial P : ℝ)))).div hb hbn)).add (hn.div hb hbn)
  have hseq : primitiveVoidBoundSeq P K α =
      (fun n => (K⁻¹)^2+8*(primorial P : ℝ)/b n+(2*((α/(n : ℝ))*(⌊2*(n : ℝ)/K⌋₊ : ℝ))*SP P)/b n) := by
    funext n
    dsimp [primitiveVoidBoundSeq,b]
    ring
  have hlim : (K⁻¹)^2+8*(primorial P : ℝ)/(c*deltaM P)+(2*c*SP P)/(c*deltaM P) =
      (K⁻¹)^2+4*(primorial P : ℝ)*K/(α*deltaM P)+2*SP P/deltaM P := by
    dsimp [c]
    field_simp [hK.ne',hα.ne',(deltaM_pos P).ne']
    <;> ring
  rw [hseq]
  simpa only [hlim] using hh

/-- The actual void probability is eventually below any strict upper
bound on the source limiting constant. This is the quantified limsup
statement of (21). -/
theorem primitive_void_eventually_bound (P : ℕ) {K α C : ℝ} (hK : 1 < K)
    (hKM : K ≤ primorial P) (hα : 0 < α)
    (hC : (K⁻¹)^2+4*(primorial P : ℝ)*K/(α*deltaM P)+2*SP P/deltaM P < C) :
    ∀ᶠ n : ℕ in atTop, m {x | ZCount n α x = 0} ≤ ENNReal.ofReal C := by
  have hK0 : 0 < K := zero_lt_one.trans hK
  have hβlim := betaN_limit P hK0 α
  have hβp : 0 < (2*α/K)*deltaM P := mul_pos (div_pos (mul_pos (by norm_num) hα) hK0) (deltaM_pos P)
  have hβ : ∀ᶠ n : ℕ in atTop, 0 < betaN (primorial P) ⌊2*(n : ℝ)/K⌋₊ (α/(n : ℝ)) :=
    hβlim.eventually (Ioi_mem_nhds hβp)
  have hε : ∀ᶠ n : ℕ in atTop, α/(n : ℝ) < 1 := tendsto_alpha_div_nat.eventually (Iio_mem_nhds (by norm_num))
  have hR := (primitiveVoidBoundSeq_limit P hK0 hα).eventually (Iio_mem_nhds hC)
  filter_upwards [hβ,hε,hR] with n hβn hεn hRn
  exact (primitive_void_bound P hK hKM (div_nonneg hα.le (Nat.cast_nonneg _)) hεn hβn).trans
    (ENNReal.ofReal_le_ofReal hRn.le)

end
end Paper14
