import Paper22.PetzMomentCenter
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Equality of the optimized Petz moment and the original Augustin capacity,
proved for the full-rank channels required by the principal theorem. -/
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
noncomputable section
namespace Paper22
variable {n d : ℕ}

theorem probability_weighted_positive {q f : Fin n → ℝ}
    (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x=1) (hf : ∀ x, 0 < f x) :
    0 < ∑ x, q x*f x := by
  have hex : ∃ x, 0 < q x := by
    by_contra hno
    push_neg at hno
    have hsum : (∑ x, q x) ≤ 0 := Finset.sum_nonpos fun x _ => hno x
    linarith
  obtain ⟨x,hx⟩ := hex
  exact (Finset.single_le_sum (fun y _ => mul_nonneg (hq0 y) (hf y).le)
    (Finset.mem_univ x)).trans_lt' (mul_pos hx (hf x))

theorem sum_mul_log2_le_log2_sum {q f : Fin n → ℝ}
    (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x=1) (hf : ∀ x, 0 < f x) :
    (∑ x, q x*log2 (f x)) ≤ log2 (∑ x, q x*f x) := by
  have h := (strictConcaveOn_log_Ioi.concaveOn).le_map_sum
    (t := Finset.univ) (w := q) (p := f) (fun x _ => hq0 x) hq1 (fun x _ => hf x)
  simp only [smul_eq_mul] at h
  simp only [log2_eq_div_log,← mul_div_assoc,← Finset.sum_div]
  exact div_le_div_of_nonneg_right h (Real.log_pos (by norm_num : (1:ℝ)<2)).le

/-- The original order-alpha capacity equals the optimized moment formula.
All reference-state optimization here uses actual density matrices. -/
theorem orderAlphaCapacity_eq_minimum_moment [NeZero d] (V : CQChannel n d)
    (hV : V.FullRank) {q : Fin n → ℝ} (hq : q ∈ probabilitySimplex n)
    {α : ℝ} (hα : α ∈ Set.Ioo 0 1)
    (hmin : ∀ r ∈ probabilitySimplex n, petzMomentValue V q α ≤ petzMomentValue V r α) :
    orderAlphaCapacity V α=(1/(α-1))*log2 (petzMomentValue V q α) := by
  let F := petzMomentValue V q α
  let k : ℝ := 1/(α-1)
  let C := k*log2 F
  let τ := petzMomentCenter V q α
  have hτ : IsDensity τ := petzMomentCenter_isDensity V hq.1 hq.2 hα.1
  have hF : 0 < F := Real.rpow_pos_of_pos
    (trace_rpow_inv_pos (petzPowerMixture_nonneg V hq.1 α)
      (petzPowerMixture_trace_pos V hq.1 hq.2 hα.1) hα.1) α
  have hk : k < 0 := one_div_neg.mpr (sub_neg.mpr hα.2)
  have hcenter : ∀ x, F ≤ petzTrace α (V.states x) τ := petzMoment_minimizer_center V hq hα hmin
  have hupper (p : Fin n → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x=1) :
      orderAlphaInf α V p ≤ C := by
    have hinf : orderAlphaInf α V p ≤ orderAlphaObj α V p τ :=
      csInf_le (orderAlpha_values_bddBelow V hα hp0 hp1) ⟨τ,hτ,rfl⟩
    apply hinf.trans
    calc orderAlphaObj α V p τ ≤ ∑ x, p x*C := by
           apply Finset.sum_le_sum
           intro x _
           apply mul_le_mul_of_nonneg_left _ (hp0 x)
           exact mul_le_mul_of_nonpos_left (log2_le_log2 hF (hcenter x)) hk.le
         _ = C := by rw [← Finset.sum_mul,hp1,one_mul]
  have hlower : C ≤ orderAlphaInf α V q := by
    apply le_csInf (orderAlpha_values_nonempty V α q)
    rintro s ⟨σ,hσ,rfl⟩
    have hpos (x : Fin n) : 0 < petzTrace α (V.states x) σ := petzTrace_pos_of_posDef (hV x) hσ hα
    have hsumpos := probability_weighted_positive hq.1 hq.2 hpos
    have hlog := sum_mul_log2_le_log2_sum hq.1 hq.2 hpos
    have hsum := petzMomentValue_upper V hq.1 hα hσ
    have hlogF : (∑ x, q x*log2 (petzTrace α (V.states x) σ)) ≤ log2 F :=
      hlog.trans (log2_le_log2 hsumpos hsum)
    have hmul := mul_le_mul_of_nonpos_left hlogF hk.le
    calc C ≤ k*(∑ x, q x*log2 (petzTrace α (V.states x) σ)) := hmul
         _ = orderAlphaObj α V q σ := by
           unfold orderAlphaObj petzRenyiRe
           rw [Finset.mul_sum]
           apply Finset.sum_congr rfl
           intro x _
           ring
  have hnonempty : Set.Nonempty {t | ∃ p : Fin n → ℝ, (∀ x, 0 ≤ p x) ∧ (∑ x, p x=1) ∧
      t=orderAlphaInf α V p} := ⟨_,q,hq.1,hq.2,rfl⟩
  have hbounded : BddAbove {t | ∃ p : Fin n → ℝ, (∀ x, 0 ≤ p x) ∧ (∑ x, p x=1) ∧
      t=orderAlphaInf α V p} := by
    refine ⟨C,?_⟩
    rintro t ⟨p,hp0,hp1,rfl⟩
    exact hupper p hp0 hp1
  apply le_antisymm
  · apply csSup_le hnonempty
    rintro t ⟨p,hp0,hp1,rfl⟩
    exact hupper p hp0 hp1
  · exact hlower.trans (le_csSup hbounded ⟨q,hq.1,hq.2,rfl⟩)

theorem exists_input_orderAlphaCapacity_moment [NeZero d] (V : CQChannel n d)
    (hn : 0 < n) (hV : V.FullRank) {α : ℝ} (hα : α ∈ Set.Ioo 0 1) :
    ∃ q ∈ probabilitySimplex n,
      orderAlphaCapacity V α=(1/(α-1))*log2 (petzMomentValue V q α) := by
  obtain ⟨q,hq,hmin⟩ := exists_petzMoment_minimizer V hn hα
  exact ⟨q,hq,orderAlphaCapacity_eq_minimum_moment V hV hq hα hmin⟩

end Paper22
end
