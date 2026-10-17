import Paper15.Reduction
import Mathlib.Analysis.Convex.KreinMilman

/-!
# Attainment by a sparse optimal law

This supplies the existence step in the linear program used by Lemma 4: it
produces an optimal extreme point, rather than assuming one has been supplied.
-/
noncomputable section
namespace Paper15
open Finset BigOperators Matrix Set

lemma isCompact_LPFeasible {n : ℕ} (A : Matrix (Fin 2) (Fin n) ℝ) (b : Fin 2 → ℝ) :
    IsCompact {x | LPFeasible A b x} := by
  have hnonneg : IsClosed {x : Fin n → ℝ | ∀ i, 0 ≤ x i} :=
    by simpa only [setOf_forall] using
      isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))
  have heq : IsClosed {x : Fin n → ℝ | A *ᵥ x = b} := by
    apply isClosed_eq _ continuous_const
    unfold mulVec dotProduct
    fun_prop
  have hsum : IsClosed {x : Fin n → ℝ | ∑ i, x i = 1} := by
    apply isClosed_eq _ continuous_const
    fun_prop
  have hc : IsCompact (stdSimplex ℝ (Fin n)) := isCompact_stdSimplex _
  exact hc.of_isClosed_subset
    (hnonneg.inter (heq.inter hsum)) (fun x hx => ⟨hx.1, hx.2.2⟩)

/-- Every feasible finite-source LP with normalization and two moment
constraints admits an optimal law with at most three positive weights. -/
theorem exists_sparse_LP_optimizer {n : ℕ} (A : Matrix (Fin 2) (Fin n) ℝ)
    (b : Fin 2 → ℝ) (c : Fin n → ℝ) {x : Fin n → ℝ} (hx : LPFeasible A b x) :
    ∃ y : Fin n → ℝ, LPFeasible A b y ∧ {i | 0 < y i}.toFinset.card ≤ 3 ∧
      ∀ z, LPFeasible A b z → ∑ i, c i * z i ≤ ∑ i, c i * y i := by
  classical
  let K := {y | LPFeasible A b y}
  let l : (Fin n → ℝ) →L[ℝ] ℝ := ∑ i, c i • ContinuousLinearMap.proj i
  have hl (y : Fin n → ℝ) : l y = ∑ i, c i * y i := by
    simp [l, ContinuousLinearMap.sum_apply]
  have hK : IsCompact K := isCompact_LPFeasible A b
  obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn ⟨x, hx⟩ l.continuous.continuousOn
  have hface : IsExposed ℝ K (l.toExposed K) := fun _ => ⟨l, rfl⟩
  have hface_ne : (l.toExposed K).Nonempty := ⟨z, hz, hmax⟩
  obtain ⟨y, hy⟩ := (hface.isCompact hK).extremePoints_nonempty hface_ne
  have hyK : y ∈ K.extremePoints ℝ := hface.isExtreme.extremePoints_subset_extremePoints hy
  have hext : IsLPExtreme A b y := by
    refine ⟨hyK.1, ?_⟩
    intro u v hu hv hmid
    have hm : y ∈ openSegment ℝ u v := by
      rw [hmid]
      refine ⟨(1/2 : ℝ), (1/2 : ℝ), by norm_num, by norm_num, by norm_num, ?_⟩
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.div_apply, Pi.ofNat_apply]
      ring
    obtain ⟨hu', hv'⟩ := (mem_extremePoints.mp hyK).2 u hu v hv hm
    exact hu'.trans hv'.symm
  refine ⟨y, hext.1, isLPExtreme_support_le A b hext, ?_⟩
  intro u hu
  rw [← hl u, ← hl y]
  exact hy.1.2 u hu

end Paper15
