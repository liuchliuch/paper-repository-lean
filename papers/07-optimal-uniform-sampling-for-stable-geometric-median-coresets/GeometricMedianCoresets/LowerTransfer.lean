import GeometricMedianCoresets.MainLower
import GeometricMedianCoresets.EuclideanMetric
import GeometricMedianCoresets.L1Metric

/-! The one-dimensional construction lies in both Euclidean and ℓ₁ space. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace GeometricMedianCoresets

lemma cost_map {X Y : Type*} (D : Dist X) (E : Dist Y) (f : X → Y)
    (hf : ∀ x y, E.d (f x) (f y) = D.d x y) {n : ℕ} (P : Dataset X n) (z : X) :
    E.cost (fun i => f (P i)) (f z) = D.cost P z := by
  simp only [Dist.cost, hf]

/-- A failure in an isometrically embedded candidate domain is still a failure in the larger one. -/
lemma stable_of_map {X Y : Type*} (D : Dist X) (E : Dist Y) (f : X → Y)
    (hf : ∀ x y, E.d (f x) (f y) = D.d x y) {n m : ℕ}
    (P : Dataset X n) (Q : Dataset X m) {ε η : ℝ}
    (hs : IsStableCoreset E (fun i => f (P i)) (fun i => f (Q i)) ε η) :
    IsStableCoreset D P Q ε η := by
  intro x y hcomp
  have hc : E.cost (fun i => f (Q i)) (f x) ≤ (1 + ε) * E.cost (fun i => f (Q i)) (f y) := by
    simpa only [cost_map D E f hf] using hcomp
  simpa only [cost_map D E f hf] using hs (f x) (f y) hc

lemma lineMap_injective (p : ENNReal) :
    Function.Injective (fun r : ℝ => (WithLp.toLp p (fun _ : Fin 1 => r))) := by
  intro a b hab
  exact congrArg (fun x : PiLp p (fun _ : Fin 1 => ℝ) => x 0) hab

namespace Euclidean

def lineMap (r : ℝ) : Space 1 := WithLp.toLp 2 (fun _ => r)
lemma lineMap_dist (a b : ℝ) : ‖lineMap a - lineMap b‖ = |a - b| := by
  apply (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).1
  simp [lineMap, PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs]

/-- Theorem 1.2(ii), stated on the actual one-dimensional Euclidean space. -/
theorem thm_1_2_ii {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1/100) {m : ℕ} (hm : 0 < m)
    (hmsize : (m:ℝ) ≤ 1 / (24200 * ε ^ 2)) :
    ∃ (n : ℕ) (P : Dataset (Space 1) n), 0 < n ∧ m ≤ n ∧ Function.Injective P ∧
      ((((Finset.univ : Finset (Fin n)).powersetCard m).filter
        (fun I => ¬ IsStableCoreset (normDist (Space 1)) P (indexedSample P I) ε (17 * ε))).card : ℝ) /
        (n.choose m : ℝ) ≥ 2/5 := by
  obtain ⟨n, P, hn, hmn, hinj, hprob⟩ := LowerBound.thm_1_2_ii hε hε' hm hmsize
  refine ⟨n, fun i => lineMap (P i), hn, hmn, (lineMap_injective 2).comp hinj, ?_⟩
  apply hprob.trans
  apply sample_fraction_mono
  intro I _ hfail hstable
  exact hfail (stable_of_map (normDist ℝ) (normDist (Space 1)) lineMap
    (fun x y => lineMap_dist x y) P (indexedSample P I) hstable)
end Euclidean

namespace L1

def lineMap (r : ℝ) : Space 1 := WithLp.toLp 1 (fun _ => r)
lemma lineMap_dist (a b : ℝ) : ‖lineMap a - lineMap b‖ = |a - b| := by
  simp [lineMap, PiLp.norm_eq_of_L1, Real.norm_eq_abs]

/-- The same distinct-point lower bound for Corollary 4.2. -/
theorem lower_bound {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1/100) {m : ℕ} (hm : 0 < m)
    (hmsize : (m:ℝ) ≤ 1 / (24200 * ε ^ 2)) :
    ∃ (n : ℕ) (P : Dataset (Space 1) n), 0 < n ∧ m ≤ n ∧ Function.Injective P ∧
      ((((Finset.univ : Finset (Fin n)).powersetCard m).filter
        (fun I => ¬ IsStableCoreset (normDist (Space 1)) P (indexedSample P I) ε (17 * ε))).card : ℝ) /
        (n.choose m : ℝ) ≥ 2/5 := by
  obtain ⟨n, P, hn, hmn, hinj, hprob⟩ := LowerBound.thm_1_2_ii hε hε' hm hmsize
  refine ⟨n, fun i => lineMap (P i), hn, hmn, (lineMap_injective 1).comp hinj, ?_⟩
  apply hprob.trans
  apply sample_fraction_mono
  intro I _ hfail hstable
  exact hfail (stable_of_map (normDist ℝ) (normDist (Space 1)) lineMap
    (fun x y => lineMap_dist x y) P (indexedSample P I) hstable)
end L1

end GeometricMedianCoresets
