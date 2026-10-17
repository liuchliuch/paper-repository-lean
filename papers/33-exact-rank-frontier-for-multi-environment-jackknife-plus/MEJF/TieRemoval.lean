import MEJF.OrderStatistics
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Tactic.Ring

/-! Generic finite general-position and quantitative perturbation tools for
Proposition 5.3. The concrete list of the prediction-table tie relations is a
separate obligation, not hidden in a definition of general position. -/
namespace MEJF.TieRemoval
open Finset Set
noncomputable section

/-- Every nontrivial affine hyperplane has dense complement. Constant,
nonzero affine constraints are allowed. -/
lemma dense_avoid_affine {J : Type*} [Fintype J] (L : (J → ℝ) →L[ℝ] ℝ) (c : ℝ)
    (h : L ≠ 0 ∨ c ≠ 0) : Dense {u | L u ≠ c} := by
  by_cases hL : L = 0
  · have hc : c ≠ 0 := h.resolve_left (fun hh => hh hL)
    have hs : {u : J → ℝ | L u ≠ c} = Set.univ := by
      ext u
      simp [hL, Ne.symm hc]
    rw [hs]
    exact dense_univ
  · exact (dense_compl_singleton c).preimage (L.isOpenMap_of_ne_zero hL)

/-- A finite collection of nontrivial real affine relations can all be avoided
in every arbitrarily small cube about every prescribed vector. In particular
this applies to finite rational affine relations. -/
theorem exists_avoid_affine {I J : Type*} [Fintype I] [Fintype J]
    (L : I → (J → ℝ) →L[ℝ] ℝ) (c : I → ℝ)
    (h : ∀ i, L i ≠ 0 ∨ c i ≠ 0) (z : J → ℝ) (η : ℝ) (hη : 0 < η) :
    ∃ u : J → ℝ, (∀ j, |u j - z j| < η) ∧ ∀ i, L i u ≠ c i := by
  have hd : Dense (⋂ i, {u : J → ℝ | L i u ≠ c i}) :=
    dense_iInter_of_isOpen
      (fun i => isOpen_ne_fun (L i).continuous continuous_const)
      (fun i => dense_avoid_affine (L i) (c i) (h i))
  obtain ⟨u, hu, hdist⟩ := hd.exists_dist_lt z hη
  refine ⟨u, ?_, ?_⟩
  · intro j
    have hle := dist_le_pi_dist u z j
    rw [Real.dist_eq] at hle
    exact hle.trans_lt (by simpa only [dist_comm] using hdist)
  · simpa only [Set.mem_iInter, Set.mem_setOf_eq] using hu

/-- Change of an absolute residual under independent response and prediction
perturbations. This does not assume a fixed residual sign. -/
lemma residual_perturbation (y y' p p' η : ℝ)
    (hy : |y'-y| ≤ η) (hp : |p'-p| ≤ η) :
    abs (abs (y'-p') - abs (y-p)) ≤ 2*η := by
  have h₁ := abs_abs_sub_abs_le_abs_sub (y'-p') (y-p)
  have h₂ : |(y'-p')-(y-p)| ≤ |y'-y| + |p'-p| := by
    calc
      |(y'-p')-(y-p)| = |(y'-y)-(p'-p)| := by congr 1 <;> ring
      _ ≤ |y'-y| + |p'-p| := by
        simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (y'-y) 0 (p'-p)
  exact h₁.trans (h₂.trans (by linarith))

/-- The inner order-statistic radius changes by at most `2η`. -/
lemma radius_perturbation {n : ℕ} (y y' p p' : Fin n → ℝ)
    (k : Fin n) (η : ℝ) (hy : ∀ j, |y' j-y j| ≤ η)
    (hp : ∀ j, |p' j-p j| ≤ η) :
    |OrderStatistics.stat (fun j => |y' j-p' j|) k -
      OrderStatistics.stat (fun j => |y j-p j|) k| ≤ 2*η :=
  OrderStatistics.stat_lipschitz _ _ k _
    (fun j => residual_perturbation _ _ _ _ η (hy j) (hp j))

/-- Moving a center by `η` and a radius by `2η` moves its lower endpoint by
at most `3η`. -/
lemma lower_candidate_perturbation (p p' r r' η : ℝ)
    (hp : |p'-p| ≤ η) (hr : |r'-r| ≤ 2*η) :
    |(p'-r')-(p-r)| ≤ 3*η := by
  have h : |(p'-r')-(p-r)| ≤ |p'-p| + |r'-r| := by
    calc
      |(p'-r')-(p-r)| = |(p'-p)-(r'-r)| := by congr 1 <;> ring
      _ ≤ |p'-p| + |r'-r| := by
        simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (p'-p) 0 (r'-r)
  exact h.trans (by linarith)

lemma upper_candidate_perturbation (p p' r r' η : ℝ)
    (hp : |p'-p| ≤ η) (hr : |r'-r| ≤ 2*η) :
    |(p'+r')-(p+r)| ≤ 3*η := by
  have h : |(p'+r')-(p+r)| ≤ |p'-p| + |r'-r| := by
    calc
      |(p'+r')-(p+r)| = |(p'-p)+(r'-r)| := by congr 1 <;> ring
      _ ≤ |p'-p| + |r'-r| := abs_add_le _ _
  exact h.trans (by linarith)

/-- The source's unit lower-endpoint failure margin remains strict whenever
`η < 1/4`, including ties anywhere away from the response. -/
lemma unit_failure_margin (L L' y y' η : ℝ) (hη : η < 1/4)
    (hmargin : y+1 ≤ L) (hL : |L'-L| ≤ 3*η) (hy : |y'-y| ≤ η) :
    y' < L' := by
  have h₁ := (abs_le.mp hL).1
  have h₂ := (abs_le.mp hy).2
  linarith

/-- Coordinatewise strict lower misses persist through the two nested
order-statistic stages, assuming the concrete candidate endpoint perturbation
bounds. -/
lemma aggregate_unit_failure_margin {m : ℕ} (A A' : Fin m → ℝ) (k : Fin m)
    (y y' η : ℝ) (hη : η < 1/4)
    (hmargin : y+1 ≤ OrderStatistics.stat A k)
    (hA : ∀ v, |A' v-A v| ≤ 3*η) (hy : |y'-y| ≤ η) :
    y' < OrderStatistics.stat A' k :=
  unit_failure_margin _ _ _ _ η hη hmargin
    (OrderStatistics.stat_lipschitz _ _ k _ hA) hy

end
end MEJF.TieRemoval
