import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-! Finite primal CVaR and the compactness argument in Appendix A.
The action probabilities are part of the law to which CVaR is applied. -/
namespace Paper36.Regularity
open Set Finset
noncomputable section

abbrev Law (Ω : Type*) [Fintype Ω] : Type _ := ↥(stdSimplex ℝ Ω)

variable {Ω : Type*} [Fintype Ω]

@[fun_prop] lemma continuous_law_apply (i : Ω) : Continuous (fun P : Law Ω => P i) :=
  (continuous_apply i).comp continuous_subtype_val

lemma law_sum (P : Law Ω) : ∑ i, P i = 1 := P.property.2

def expectation (P : Law Ω) (X : Ω → ℝ) : ℝ := ∑ i, P i * X i

def objective (α : ℝ) (P : Law Ω) (X : Ω → ℝ) (z : ℝ) : ℝ :=
  z + α⁻¹ * expectation P (fun i => max (X i - z) 0)

def compactCVaR (α B : ℝ) (P : Law Ω) (X : Ω → ℝ) : ℝ :=
  sInf ((objective α P X) '' Icc 0 B)

def primalCVaR (α : ℝ) (P : Law Ω) (X : Ω → ℝ) : ℝ :=
  sInf (range (objective α P X))

lemma continuous_objective (α : ℝ) :
    Continuous (fun p : (Law Ω × (Ω → ℝ)) × ℝ =>
      objective α p.1.1 p.1.2 p.2) := by
  unfold objective expectation
  apply continuous_snd.add
  apply continuous_const.mul
  apply continuous_finset_sum
  intro i _
  apply ((continuous_law_apply i).comp (continuous_fst.comp continuous_fst)).mul
  apply Continuous.max
  · exact ((continuous_apply i).comp (continuous_snd.comp continuous_fst)).sub continuous_snd
  · exact continuous_const

lemma exists_compact_minimizer (α B : ℝ) (hB : 0 ≤ B) (P : Law Ω) (X : Ω → ℝ) :
    ∃ z ∈ Icc 0 B, compactCVaR α B P X = objective α P X z := by
  apply isCompact_Icc.exists_sInf_image_eq (Set.nonempty_Icc.mpr hB)
  exact (continuous_objective α).comp (show Continuous (fun z : ℝ => ((P, X), z)) from continuous_const.prodMk continuous_id) |>.continuousOn

lemma compactCVaR_le (α B : ℝ) (hB : 0 ≤ B) (P : Law Ω) (X : Ω → ℝ)
    {z : ℝ} (hz : z ∈ Icc 0 B) : compactCVaR α B P X ≤ objective α P X z := by
  apply csInf_le
  · exact (isCompact_Icc.image ((continuous_objective α).comp (show Continuous (fun z : ℝ => ((P, X), z)) from continuous_const.prodMk continuous_id))).bddBelow
  · exact mem_image_of_mem _ hz

lemma le_compactCVaR (α B : ℝ) (hB : 0 ≤ B) (P : Law Ω) (X : Ω → ℝ)
    {r : ℝ} (hr : ∀ z ∈ Icc 0 B, r ≤ objective α P X z) :
    r ≤ compactCVaR α B P X := by
  apply le_csInf ((Set.nonempty_Icc.mpr hB).image _)
  rintro _ ⟨z, hz, rfl⟩
  exact hr z hz

lemma expectation_mono (P : Law Ω) {X Y : Ω → ℝ} (h : ∀ i, X i ≤ Y i) :
    expectation P X ≤ expectation P Y := by
  exact sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (h i) (P.property.1 i))

@[simp] lemma expectation_const (P : Law Ω) (a : ℝ) :
    expectation P (fun _ => a) = a := by
  simp [expectation, ← sum_mul, law_sum P]

lemma objective_nonneg (α : ℝ) (hα : 0 ≤ α) (P : Law Ω) (X : Ω → ℝ)
    {z : ℝ} (hz : 0 ≤ z) : 0 ≤ objective α P X z := by
  unfold objective expectation
  exact add_nonneg hz (mul_nonneg (inv_nonneg.mpr hα) (Finset.sum_nonneg fun i _ =>
    mul_nonneg (P.property.1 i) (le_max_right _ _)))

lemma compactCVaR_nonneg (α B : ℝ) (hα : 0 ≤ α) (hB : 0 ≤ B)
    (P : Law Ω) (X : Ω → ℝ) : 0 ≤ compactCVaR α B P X := by
  apply le_compactCVaR α B hB
  intro z hz
  exact objective_nonneg α hα P X hz.1

lemma compactCVaR_le_bound (α B : ℝ) (hB : 0 ≤ B) (P : Law Ω) (X : Ω → ℝ)
    (hX : ∀ i, X i ≤ B) : compactCVaR α B P X ≤ B := by
  calc
    _ ≤ objective α P X B := compactCVaR_le α B hB P X ⟨hB, le_rfl⟩
    _ = B := by
      have hx : (fun i => max (X i - B) 0) = (fun _ => 0) := by
        funext i
        exact max_eq_right (sub_nonpos.mpr (hX i))
      simp [objective, hx]

lemma compactCVaR_mono (α B : ℝ) (hα : 0 ≤ α) (hB : 0 ≤ B)
    (P : Law Ω) {X Y : Ω → ℝ} (hXY : ∀ i, X i ≤ Y i) :
    compactCVaR α B P X ≤ compactCVaR α B P Y := by
  obtain ⟨z, hz, heq⟩ := exists_compact_minimizer α B hB P Y
  rw [heq]
  apply (compactCVaR_le α B hB P X hz).trans
  unfold objective
  gcongr
  apply expectation_mono
  intro i
  exact max_le_max (sub_le_sub_right (hXY i) z) le_rfl

lemma objective_below_zero (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (P : Law Ω) (X : Ω → ℝ) (hX : ∀ i, 0 ≤ X i) {z : ℝ} (hz : z ≤ 0) :
    objective α P X 0 ≤ objective α P X z := by
  have hzero : (fun i => max (X i - 0) 0) = X := by
    funext i
    simp [max_eq_left (hX i)]
  have hzX : (fun i => max (X i - z) 0) = fun i => X i - z := by
    funext i
    exact max_eq_left (sub_nonneg.mpr (hz.trans (hX i)))
  have he : expectation P (fun i => X i - z) = expectation P X - z := by
    simp only [expectation, mul_sub, sum_sub_distrib, ← sum_mul, law_sum P, one_mul]
  have hi : 1 ≤ α⁻¹ := (one_le_inv₀ hα).mpr hα1
  simp only [objective, hzero, hzX, he, zero_add]
  nlinarith [mul_nonneg (sub_nonneg.mpr hi) (neg_nonneg.mpr hz)]

lemma objective_above_bound (α B : ℝ) (P : Law Ω) (X : Ω → ℝ)
    (hX : ∀ i, X i ≤ B) {z : ℝ} (hz : B ≤ z) :
    objective α P X B ≤ objective α P X z := by
  have hb : (fun i => max (X i - B) 0) = (fun _ => 0) := by
    funext i
    exact max_eq_right (sub_nonpos.mpr (hX i))
  have hzz : (fun i => max (X i - z) 0) = (fun _ => 0) := by
    funext i
    exact max_eq_right (sub_nonpos.mpr ((hX i).trans hz))
  simpa [objective, hb, hzz] using hz

/-- Restricting the threshold to the loss interval preserves the original primal CVaR. -/
theorem compactCVaR_eq_primalCVaR (α B : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hB : 0 ≤ B) (P : Law Ω) (X : Ω → ℝ) (hX : ∀ i, X i ∈ Icc 0 B) :
    compactCVaR α B P X = primalCVaR α P X := by
  have hlower : ∀ z, compactCVaR α B P X ≤ objective α P X z := by
    intro z
    by_cases hz : z < 0
    · exact (compactCVaR_le α B hB P X ⟨le_rfl, hB⟩).trans
        (objective_below_zero α hα hα1 P X (fun i => (hX i).1) hz.le)
    · by_cases hzB : B < z
      · exact (compactCVaR_le α B hB P X ⟨hB, le_rfl⟩).trans
          (objective_above_bound α B P X (fun i => (hX i).2) hzB.le)
      · exact compactCVaR_le α B hB P X ⟨le_of_not_gt hz, le_of_not_gt hzB⟩
  have hbounded : BddBelow (range (objective α P X)) := ⟨compactCVaR α B P X, by
    rintro _ ⟨z, rfl⟩
    exact hlower z⟩
  apply le_antisymm
  · apply le_csInf (range_nonempty _)
    rintro _ ⟨z, rfl⟩
    exact hlower z
  · obtain ⟨z, hz, heq⟩ := exists_compact_minimizer α B hB P X
    rw [heq]
    exact csInf_le hbounded (mem_range_self z)

/-- Berge's compact minimization, specialized to the finite primal CVaR objective. -/
theorem continuous_compactCVaR (α B : ℝ) :
    Continuous (fun p : Law Ω × (Ω → ℝ) => compactCVaR α B p.1 p.2) := by
  exact isCompact_Icc.continuous_sInf (continuous_objective α)

/-- The actual extreme-value argument underlying Lemma 2.1, with the model support explicit. -/
theorem automatic_uniform_margin {Q : Type*} [TopologicalSpace Q]
    (support : Set Q) (hcompact : IsCompact support) (hne : support.Nonempty)
    (g : Q → ℝ) (hg : ContinuousOn g support) (τ : ℝ)
    (hstrict : ∀ q ∈ support, g q < τ) :
    0 < τ - sSup (g '' support) ∧
      ∀ q ∈ support, τ - sSup (g '' support) ≤ τ - g q := by
  obtain ⟨q, hq, hmax⟩ := hcompact.exists_isMaxOn hne hg
  have heq : sSup (g '' support) = g q := by
    apply csSup_eq_of_forall_le_of_forall_lt_exists_gt (hne.image g)
    · rintro _ ⟨q', hq', rfl⟩
      exact hmax hq'
    · intro w hw
      exact ⟨g q, mem_image_of_mem g hq, hw⟩
  rw [heq]
  exact ⟨sub_pos.mpr (hstrict q hq), fun q' hq' => sub_le_sub_left (hmax hq') τ⟩

end
end Paper36.Regularity
