import Paper08.LowerBound
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Piecewise

noncomputable section
open scoped Real BigOperators
open Set Filter Topology

namespace Paper08.LowerBound

/-- The polynomial bump, extended by zero to the real line. -/
def compactBump (t : ℝ) : ℝ := if t ∈ Icc (0 : ℝ) 1 then Appendix.bump t else 0

/-- Its candidate derivative is extended by zero as well. -/
def compactBumpDeriv (t : ℝ) : ℝ :=
  if t ∈ Icc (0 : ℝ) 1 then deriv Appendix.bump t else 0

lemma hasDerivAt_bump (t : ℝ) : HasDerivAt Appendix.bump (deriv Appendix.bump t) t := by
  have heq : Appendix.bump = fun s : ℝ => 16 * s ^ 2 - 32 * s ^ 3 + 16 * s ^ 4 :=
    funext bump_eq_expand
  rw [deriv_bump_expand, heq]
  exact hasDerivAt_bump_expand t

lemma compactBump_of_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    compactBump t = Appendix.bump t := if_pos ht

lemma compactBump_of_not_mem {t : ℝ} (ht : t ∉ Icc (0 : ℝ) 1) :
    compactBump t = 0 := if_neg ht

lemma compactBump_zero : compactBump 0 = 0 := by simp [compactBump, bump_zero]
lemma compactBump_one : compactBump 1 = 0 := by simp [compactBump, bump_one]
lemma compactBumpDeriv_zero : compactBumpDeriv 0 = 0 := by
  simp [compactBumpDeriv, bump_deriv_zero]
lemma compactBumpDeriv_one : compactBumpDeriv 1 = 0 := by
  simp [compactBumpDeriv, bump_deriv_one]

lemma bump_eq_zero_of_frontier {t : ℝ} (ht : t ∈ frontier (Icc (0 : ℝ) 1)) :
    Appendix.bump t = 0 := by
  simp only [frontier_Icc (by norm_num : (0 : ℝ) ≤ 1), mem_insert_iff,
    mem_singleton_iff] at ht
  rcases ht with rfl | rfl
  · exact bump_zero
  · exact bump_one

lemma bump_deriv_eq_zero_of_frontier {t : ℝ} (ht : t ∈ frontier (Icc (0 : ℝ) 1)) :
    deriv Appendix.bump t = 0 := by
  simp only [frontier_Icc (by norm_num : (0 : ℝ) ≤ 1), mem_insert_iff,
    mem_singleton_iff] at ht
  rcases ht with rfl | rfl
  · exact bump_deriv_zero
  · exact bump_deriv_one

/-- Vanishing first jets make the zero extension differentiable at both faces. -/
lemma hasDerivAt_compactBump (t : ℝ) :
    HasDerivAt compactBump (compactBumpDeriv t) t := by
  by_cases hf : t ∈ frontier (Icc (0 : ℝ) 1)
  · have hzero := bump_eq_zero_of_frontier hf
    have hd := bump_deriv_eq_zero_of_frontier hf
    have hc : compactBump t = 0 := by
      simp only [compactBump]
      split_ifs <;> simp_all
    have hcd : compactBumpDeriv t = 0 := by
      simp only [compactBumpDeriv]
      split_ifs <;> simp_all
    rw [hcd]
    have hi : HasDerivWithinAt compactBump 0 (Icc (0 : ℝ) 1) t := by
      have hi := (hasDerivAt_bump t).hasDerivWithinAt (s := Icc (0 : ℝ) 1)
      rw [hd] at hi
      exact hi.congr (fun x hx => compactBump_of_mem hx) (by rw [hc, hzero])
    have ho : HasDerivWithinAt compactBump 0 (Icc (0 : ℝ) 1)ᶜ t :=
      (hasDerivAt_const t (0 : ℝ)).hasDerivWithinAt.congr
        (fun x hx => compactBump_of_not_mem hx) hc
    have hh := hi.union ho
    rw [union_compl_self, hasDerivWithinAt_univ] at hh
    exact hh
  · by_cases ht : t ∈ Icc (0 : ℝ) 1
    · have hit : t ∈ interior (Icc (0 : ℝ) 1) := by
        by_contra hn
        exact hf ⟨subset_closure ht, hn⟩
      rw [compactBumpDeriv, if_pos ht]
      apply (hasDerivAt_bump t).congr_of_eventuallyEq
      filter_upwards [mem_interior_iff_mem_nhds.mp hit] with x hx
      exact compactBump_of_mem hx
    · rw [compactBumpDeriv, if_neg ht]
      apply (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
      filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds ht] with x hx
      exact compactBump_of_not_mem hx

lemma continuous_compactBumpDeriv : Continuous compactBumpDeriv := by
  unfold compactBumpDeriv
  refine Continuous.if (fun t ht => bump_deriv_eq_zero_of_frontier ht) ?_ continuous_const
  have heq : deriv Appendix.bump = fun t : ℝ => 32 * t - 96 * t ^ 2 + 64 * t ^ 3 :=
    funext deriv_bump_expand
  rw [heq]
  fun_prop

/-- The compactly supported polynomial is genuinely `C¹` on the whole line. -/
theorem contDiff_compactBump : ContDiff ℝ 1 compactBump := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (hasDerivAt_compactBump t).differentiableAt, ?_⟩
  have heq : deriv compactBump = compactBumpDeriv :=
    funext fun t => (hasDerivAt_compactBump t).deriv
  rw [heq]
  exact continuous_compactBumpDeriv

lemma compactBump_nonneg (t : ℝ) : 0 ≤ compactBump t := by
  unfold compactBump
  split_ifs
  · exact Appendix.bump_nonneg t
  · exact le_refl _

lemma compactBump_le_one (t : ℝ) : compactBump t ≤ 1 := by
  unfold compactBump
  split_ifs with h
  · exact Appendix.bump_le_one h
  · norm_num

lemma compactBump_eq_zero_of_not_mem_Ioo {t : ℝ} (ht : t ∉ Ioo (0 : ℝ) 1) :
    compactBump t = 0 := by
  by_cases hc : t ∈ Icc (0 : ℝ) 1
  · rw [compactBump_of_mem hc]
    have he : t = 0 ∨ t = 1 := by
      simp only [mem_Ioo, not_and_or, not_lt] at ht
      rcases ht with h | h
      · exact Or.inl (le_antisymm h hc.1)
      · exact Or.inr (le_antisymm hc.2 h)
    rcases he with rfl | rfl
    · exact bump_zero
    · exact bump_one
  · exact compactBump_of_not_mem hc

lemma compactBump_deriv_abs_le_eight (t : ℝ) : |deriv compactBump t| ≤ 8 := by
  rw [(hasDerivAt_compactBump t).deriv]
  unfold compactBumpDeriv
  split_ifs with h
  · exact bump_deriv_abs_le_eight h
  · norm_num

end Paper08.LowerBound
