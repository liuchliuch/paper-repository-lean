import Paper08.PrimitiveMomentsQ
import Paper08.Parameters
import Paper08.Algorithm
import Paper08.EfficientSupports
import Paper08.FPTAS
import Paper08.LogRecurrence

/-! # The executable rational algorithm of Section 4

All growing parameters, support candidates, local moments, logarithmic
coefficients, and the final output are computed from rational value queries.
The real factors occur only in the correctness theorems.
-/
open scoped BigOperators
namespace Paper08.FPTASAlgorithm
open PrimitiveMomentsQ

def neighbors {n m : ℕ} (scopes : Fin m → Finset (Fin n)) (e : Fin m) : Finset (Fin m) :=
  Finset.univ.filter fun f => e ≠ f ∧ (scopes e ∩ scopes f).Nonempty

def degreeBound (r c : ℕ) : ℕ := max 1 (r * (c - 1))

def pairs {n m : ℕ} (scopes : Fin m → Finset (Fin n)) (r c s p : ℕ) :=
  (EfficientSupports.supportPairs (neighbors scopes) (degreeBound r c) s).filter
    fun AB => AB.1.card ≤ p

def localCoeff {n m : ℕ} (scopes : Fin m → Finset (Fin n)) (query : Queries scopes)
    (B : Finset (Fin m)) (j s C : ℕ) (τ : ℚ) : ℚ :=
  Moments.rationalLogCoeff (fun i => momentQ scopes query B i s C τ) j

def logApprox {n m : ℕ} (scopes : Fin m → Finset (Fin n)) (query : Queries scopes)
    (r c s C : ℕ) (τ : ℚ) : ℚ :=
  ∑ p ∈ Finset.Icc 1 s, ∑ AB ∈ pairs scopes r c s p,
    (-1 : ℚ) ^ (AB.1.card - AB.2.card) * localCoeff scopes query AB.2 p s C τ

/-- The complete deterministic rational value-query algorithm. -/
def run {n m : ℕ} (fixed : Parameters.Fixed) (scopes : Fin m → Finset (Fin n))
    (query : Queries scopes) (r c : ℕ) (ε : ℚ) : ℚ :=
  if m = 0 then 1 else
    Algorithm.rationalExp (logApprox scopes query r c
      (Parameters.truncationOrder fixed m ε) fixed.C
      (Parameters.primitiveTolerance fixed m ε)) ε

noncomputable section
open Metric

theorem neighbors_eq {n r m : ℕ} (E : FactorFamily n r m) (e : Fin m) :
    neighbors (fun f => (E f).scope) e = (Interaction.graph E).neighborFinset e := by
  classical
  ext f
  simp only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and,
    SimpleGraph.mem_neighborFinset, Interaction.graph, Finset.nonempty_iff_ne_empty]
  constructor
  · rintro ⟨hne, h⟩
    obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr h
    exact ⟨hne, v, (Finset.mem_inter.mp hv).1, (Finset.mem_inter.mp hv).2⟩
  · rintro ⟨hne, v, he, hf⟩
    exact ⟨hne, Finset.nonempty_iff_ne_empty.mp ⟨v, Finset.mem_inter.mpr ⟨he, hf⟩⟩⟩

theorem neighbors_degree {n r m c : ℕ} (E : FactorFamily n r m)
    (hc : FamilyBoundedOccurrence E c) (e : Fin m) :
    (neighbors (fun f => (E f).scope) e).card ≤ degreeBound r c := by
  rw [neighbors_eq]
  exact (Interaction.degree_le E hc e).trans (le_max_right _ _)

theorem pairs_card {n m r c s p : ℕ} (scopes : Fin m → Finset (Fin n)) :
    (pairs scopes r c s p).card ≤ m * (8 * degreeBound r c) ^ s := by
  exact (Finset.card_filter_le _ _).trans
    (EfficientSupports.supportPairs_count _ (le_max_left _ _))

theorem pair_subset {n m r c s p : ℕ} (scopes : Fin m → Finset (Fin n))
    {AB : Finset (Fin m) × Finset (Fin m)} (h : AB ∈ pairs scopes r c s p) :
    AB.2 ⊆ AB.1 ∧ AB.1.card ≤ s := by
  have hmem := Finset.mem_filter.mp h
  have hp := (EfficientSupports.mem_supportPairs _ AB.1 AB.2).mp hmem.1
  exact ⟨hp.2, EfficientSupports.support_card_le _ hp.1⟩

theorem localCoeff_cast {n m : ℕ} (scopes : Fin m → Finset (Fin n)) (query : Queries scopes)
    (B : Finset (Fin m)) (j s C : ℕ) (τ : ℚ) :
    (localCoeff scopes query B j s C τ : ℝ) =
      LogRecurrence.realOutput (fun i => (momentQ scopes query B i s C τ : ℝ)) j := by
  exact Moments.rationalLogCoeff_cast_eq _ _ (LogRecurrence.realOutput_recurrence _) j

/-- The actually computed rational local logarithmic coefficient has the
paper's stability error relative to the actual integral logarithm. -/
theorem localCoeff_error {n r m s C j : ℕ} (E : FactorFamily n r m)
    (O : (e : Fin m) → Oracle.Oracle (E e).scope.card (E e).psi.toFun)
    (B : Finset (Fin m)) (hB : B.card ≤ s) (hj : j ≤ s) (hs : 1 ≤ s)
    {q K R S F : ℝ} (hq : 0 < q) (hqthird : q < 1 / 3) (hK : 0 ≤ K)
    (hR : 1 < R) (hRS : R < S)
    (hE : ∀ e, (E e).RangeOk q) (hLip : ∀ e, (E e).LipOk K)
    (hne : ∀ z ∈ ball (0 : ℂ) S, ZeroFree.Q E B z ≠ 0)
    (hC : 2 ≤ C) (hqC : 2 * q ≤ (C : ℝ)) (hKC : 6 * Real.sqrt r * K ≤ (C : ℝ))
    (hF : 4 * Real.exp (Coeff.kappa R q) ≤ F)
    (τ : ℚ) (hτ : 0 < τ) (hprecision : (4 : ℝ)^s * (τ : ℝ) ≤ (F^s)⁻¹) :
    |(localCoeff (fun e => (E e).scope) (fun e => (O e).query) B j s C τ : ℝ) -
      ModelSupport.logCoeff E B j| ≤ F^s * (4^s * (τ : ℝ)) := by
  rw [localCoeff_cast]
  exact LogRecurrence.model_logCoeff_stability E B hq hR hRS
    (fun e _ => hE e) (fun e _ => hLip e) hne hB hs hj hF hprecision
    (fun i => (momentQ (fun e => (E e).scope) (fun e => (O e).query) B i s C τ : ℝ))
    (by simp) (fun i _ hi => momentQ_error E O B hB hi hs hq.le hqthird hK hE hLip
      hC hqC hKC τ hτ)

end
end Paper08.FPTASAlgorithm
