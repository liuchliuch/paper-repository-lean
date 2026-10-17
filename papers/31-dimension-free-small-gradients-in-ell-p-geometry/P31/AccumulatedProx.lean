import P31.PowerGeometry
import P31.ExactProx

/-! The explicit known-data multicenter internal prox used by the stage
solver. It is obtained from the proved coordinate-root map, without access
to f or a Clarkson input. -/
noncomputable section
open scoped BigOperators
namespace P31
variable {ι κ : Type*} [Fintype ι]

def compositeHistoryWeights (s : Finset κ) (w : κ → ℝ) (A m : ℝ) : Option s → ℝ :=
  fun i => i.elim m (fun j => A * w j)

def compositeHistoryCenters (s : Finset κ) (c : κ → ι → ℝ) (center : ι → ℝ) :
    Option s → ι → ℝ := fun i => i.elim center (fun j => c j)

lemma compositeHistoryWeights_nonneg (s : Finset κ) (w : κ → ℝ) (A m : ℝ)
    (hw : ∀ j ∈ s, 0 ≤ w j) (hA : 0 ≤ A) (hm : 0 ≤ m) :
    ∀ i, 0 ≤ compositeHistoryWeights s w A m i := by
  intro i
  cases i with
  | none => exact hm
  | some j => exact mul_nonneg hA (hw j j.property)

lemma compositeHistoryWeights_sum_pos (s : Finset κ) (w : κ → ℝ) (A m : ℝ)
    (hw : ∀ j ∈ s, 0 ≤ w j) (hA : 0 ≤ A) (hm : 0 < m) :
    0 < ∑ i, compositeHistoryWeights s w A m i := by
  classical
  have hn := compositeHistoryWeights_nonneg s w A m hw hA hm.le
  exact hm.trans_le (Finset.single_le_sum (fun i _ => hn i) (Finset.mem_univ none))

/-- A total exact-real internal map: admissible A,m use the unique coordinate
roots; other A,m receive an arbitrary fixed value. Every parameter is known
from the composite transcript. -/
def accumulatedCompositeProx (s : Finset κ) (p : ℝ) (hp : 2 ≤ p)
    (w : κ → ℝ) (c : κ → ι → ℝ) (hw : ∀ j ∈ s, 0 ≤ w j)
    (center : ι → ℝ) (g : ι → ℝ) (A m : ℝ) : ι → ℝ := by
  classical
  exact if h : 0 ≤ A ∧ 0 < m then
    vectorProx p (atomScale p) g (compositeHistoryWeights s w A m)
      (compositeHistoryCenters s c center) hp (atomScale_pos p)
      (compositeHistoryWeights_nonneg s w A m hw h.1 h.2.le)
      (compositeHistoryWeights_sum_pos s w A m hw h.1 h.2)
    else 0

lemma composite_vectorObjective_eq (s : Finset κ) (p : ℝ)
    (w : κ → ℝ) (c : κ → ι → ℝ) (center g x : ι → ℝ) (A m : ℝ) :
    vectorCompositeObjective p (atomScale p) g (compositeHistoryWeights s w A m)
      (compositeHistoryCenters s c center) x =
    coordinateFunctional g x + A * (∑ j ∈ s, w j * powerAtom p (c j) x) +
      m * powerAtom p center x := by
  classical
  have hc : (∑ i, compositeHistoryWeights s w A m i *
        ∑ j, |x j - compositeHistoryCenters s c center i j| ^ p) =
      m * lpPower p (x - center) + ∑ j ∈ s, (A * w j) * lpPower p (x - c j) := by
    simp only [univ_option, Finset.sum_insertNone, compositeHistoryWeights,
      compositeHistoryCenters, Option.elim_none, Option.elim_some]
    change m * lpPower p (x - center) +
      (∑ j : s, (A * w j) * lpPower p (x - c j)) = _
    congr 1
    exact Finset.sum_coe_sort s (fun j => (A * w j) * lpPower p (x - c j))
  rw [vectorCompositeObjective_expansion, hc, coordinateFunctional_apply]
  simp only [powerAtom]
  have hs : (atomScale p / p) * (∑ j ∈ s, (A * w j) * lpPower p (x - c j)) =
      A * (∑ j ∈ s, w j * (atomScale p / p * lpPower p (x - c j))) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [mul_add, hs]
  ring

/-- The known multicenter map really minimizes exactly (5.1), for every
linear term g, nonnegative A and positive m. -/
theorem accumulatedCompositeProx_minimizes (s : Finset κ) (p : ℝ) (hp : 2 ≤ p)
    (w : κ → ℝ) (c : κ → ι → ℝ) (hw : ∀ j ∈ s, 0 ≤ w j)
    (center : ι → ℝ) (g : ι → ℝ) (A m : ℝ) (hA : 0 ≤ A) (hm : 0 < m) :
    ∀ x,
      coordinateFunctional g (accumulatedCompositeProx s p hp w c hw center g A m) +
        A * (∑ j ∈ s, w j * powerAtom p (c j) (accumulatedCompositeProx s p hp w c hw center g A m)) +
        m * powerAtom p center (accumulatedCompositeProx s p hp w c hw center g A m) ≤
      coordinateFunctional g x + A * (∑ j ∈ s, w j * powerAtom p (c j) x) + m * powerAtom p center x := by
  classical
  intro x
  have hn := compositeHistoryWeights_nonneg s w A m hw hA hm.le
  have hsum := compositeHistoryWeights_sum_pos s w A m hw hA hm
  have hmin := (vectorProx_minimizer_iff p (atomScale p) g (compositeHistoryWeights s w A m)
    (compositeHistoryCenters s c center) hp (atomScale_pos p) hn hsum _).mpr rfl x
  rw [composite_vectorObjective_eq, composite_vectorObjective_eq] at hmin
  simpa only [accumulatedCompositeProx, dif_pos (show 0 ≤ A ∧ 0 < m from ⟨hA, hm⟩)] using hmin

end P31
