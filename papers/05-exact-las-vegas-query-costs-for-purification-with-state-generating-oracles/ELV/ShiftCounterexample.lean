import ELV.LpReindex
import ELV.RayVectors

/-! Remark 2.2: a concrete infinite-dimensional unitary for which the public
input has no returned-catalyst transduction. -/
noncomputable section
namespace ELV.Query
abbrev CounterLine := lp (fun _ : ℤ => ℂ) 2

def counterOrigin : CounterLine := lp.single 2 0 1

/-- The bilateral shift has no transduction at the public origin, for any
complex output amplitude or square summable private catalyst. -/
theorem bilateralShift_no_transduction :
    ¬ ∃ (τ : ℂ) (w : CounterLine), inner ℂ counterOrigin w = 0 ∧
      bilateralShift (counterOrigin + w) = τ • counterOrigin + w := by
  rintro ⟨τ,w,hw,heq⟩
  have hw0 : w 0 = 0 := by
    simpa [counterOrigin,lp.inner_single_left,RCLike.inner_apply] using hw
  have hc (k : ℤ) : (if k-1 = 0 then (1 : ℂ) else 0) + w (k-1) =
      τ * (if k = 0 then (1 : ℂ) else 0) + w k := by
    have hk := congrArg (fun z : CounterLine => z k) heq
    simpa [bilateralShift_apply,counterOrigin,lp.coeFn_add,lp.coeFn_smul,lp.single_apply,Pi.single_apply,eq_comm] using hk
  have hone (j : ℕ) : w ((j : ℤ)+1) = 1 := by
    induction j with
    | zero =>
      have h := hc 1
      simpa [hw0] using h.symm
    | succ j ih =>
      have h := hc ((j : ℤ)+2)
      have h1 : (j : ℤ)+2-1 ≠ 0 := by omega
      have h2 : (j : ℤ)+2 ≠ 0 := by omega
      rw [if_neg h1,if_neg h2] at h
      simp only [zero_add,mul_zero] at h
      have hj : (j : ℤ)+2-1 = (j : ℤ)+1 := by omega
      rw [hj,ih] at h
      simpa [Nat.cast_add,Nat.cast_one,add_assoc] using h.symm
  have hs : Summable (fun k : ℤ => ‖w k‖ ^ 2) := by
    simpa using (lp.memℓp w).summable (by norm_num : 0 < (2 : ENNReal).toReal)
  have hi : Function.Injective (fun j : ℕ => (j : ℤ)+1) := by
    intro i j h
    exact Int.ofNat.inj (add_right_cancel h)
  have hsum : Summable (fun j : ℕ => ‖w ((j : ℤ)+1)‖ ^ 2) := hs.comp_injective hi
  simp_rw [hone,norm_one,one_pow] at hsum
  have hz := hsum.tendsto_atTop_zero
  have ho : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) := tendsto_const_nhds
  have hn : (0 : ℝ) = 1 := tendsto_nhds_unique hz ho
  norm_num at hn

end ELV.Query
