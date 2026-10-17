import UniformBorderRank.AnchorTensor
import UniformBorderRank.BoundaryExpansion

/-! Lift the dummy-site tensors back to actual original coordinate slices.
The lifting is a local linear map, so it preserves every border-rank bound. -/
noncomputable section
namespace UniformBorderRank
open Finset

/-- Restrict an assignment on all anchor factors to the left anchor. -/
def anchorSliceLeft {N : ℕ} {d : Fin N → ℕ} (L R : Finset (Fin N))
    (gamma : FiniteSites.RetainedIndex d (L ∪ R)) : FiniteSites.RetainedIndex d L :=
  fun i => gamma ⟨i.val, mem_union_left R i.property⟩

/-- Restrict an assignment on all anchor factors to the right anchor. -/
def anchorSliceRight {N : ℕ} {d : Fin N → ℕ} (L R : Finset (Fin N))
    (gamma : FiniteSites.RetainedIndex d (L ∪ R)) : FiniteSites.RetainedIndex d R :=
  fun i => gamma ⟨i.val, mem_union_right L i.property⟩

/-- Extend the unique dummy coordinate constantly at each anchor site, and
identify the remaining coordinates with their original local spaces. -/
def anchorSliceLift {N : ℕ} (d : Fin N → ℕ) (L R : Finset (Fin N))
    (i : Fin N) (x : Fin (d i)) (y : Fin (anchorOutsideDim d L R i)) : ℂ :=
  if hi : i ∈ L ∪ R then 1
    else if Fin.cast (by simp [anchorOutsideDim, hi]) y = x then 1 else 0

lemma anchorSliceLift_weight {N : ℕ} (d : Fin N → ℕ) (L R : Finset (Fin N))
    (w : FiniteSites.TensorIndex d) (u : FiniteSites.TensorIndex (anchorOutsideDim d L R)) :
    (∏ i, anchorSliceLift d L R i (w i) (u i)) =
      if u = outsideAnchorIndex d L R w then 1 else 0 := by
  classical
  have hlocal (i : Fin N) : anchorSliceLift d L R i (w i) (u i) =
      if u i = outsideAnchorIndex d L R w i then 1 else 0 := by
    by_cases hi : i ∈ L ∪ R
    · have hd : anchorOutsideDim d L R i = 1 := by simp [anchorOutsideDim, hi]
      haveI : Subsingleton (Fin (anchorOutsideDim d L R i)) := by rw [hd]; infer_instance
      simp [anchorSliceLift, hi, Subsingleton.elim (u i) (outsideAnchorIndex d L R w i)]
    · simp [anchorSliceLift, outsideAnchorIndex, hi, Fin.ext_iff]
  simp_rw [hlocal]
  simpa only [FiniteSites.contractionWeight, mem_univ, ite_true] using
    FiniteSites.contractionWeight_univ (d := anchorOutsideDim d L R) 0 (outsideAnchorIndex d L R w) u

/-- The tensor map really extends a dummy-site tensor by its value at the
outside coordinates of the original tensor. -/
lemma tensorMap_anchorSliceLift {N : ℕ} (d : Fin N → ℕ) (L R : Finset (Fin N))
    (U : Coeffs (anchorOutsideDim d L R)) (w : FiniteSites.TensorIndex d) :
    tensorMap (anchorSliceLift d L R) U w = U (outsideAnchorIndex d L R w) := by
  classical
  simp [tensorMap, anchorSliceLift_weight]

lemma assemble_anchorSlice {N : ℕ} (d : Fin N → ℕ) (L R : Finset (Fin N))
    (gamma : FiniteSites.RetainedIndex d (L ∪ R)) (w : FiniteSites.TensorIndex d) :
    assembleAnchorIndex d L R (anchorSliceLeft L R gamma) (anchorSliceRight L R gamma)
      (outsideAnchorIndex d L R w) = freezeCoordinates (L ∪ R) gamma w := by
  funext i
  by_cases hiL : i ∈ L
  · simp [assembleAnchorIndex, anchorSliceLeft, freezeCoordinates, hiL]
  · by_cases hiR : i ∈ R
    · simp [assembleAnchorIndex, anchorSliceRight, freezeCoordinates, hiL, hiR]
    · simp [assembleAnchorIndex, outsideAnchorIndex, freezeCoordinates, hiL, hiR]

/-- Every original coefficient slice is exactly a local linear image of
the corresponding actual anchored tensor. -/
theorem anchorTensor_sliceLift_eq {N : ℕ} (d : Fin N → ℕ) (T : Coeffs d)
    (L R : Finset (Fin N)) (gamma : FiniteSites.RetainedIndex d (L ∪ R)) :
    tensorMap (anchorSliceLift d L R)
      (anchorTensor d T L R (anchorSliceLeft L R gamma) (anchorSliceRight L R gamma)) =
        coefficientSlice (L ∪ R) gamma T := by
  ext w
  rw [tensorMap_anchorSliceLift]
  change T (assembleAnchorIndex d L R _ _ _) = T (freezeCoordinates (L ∪ R) gamma w)
  rw [assemble_anchorSlice]

/-- A border-rank bound on an actual anchored tensor gives the same bound
for the original tensor with those anchor coordinates frozen. -/
theorem borderRankLe_coefficientSlice_of_anchorTensor {N : ℕ} (d : Fin N → ℕ) (T : Coeffs d)
    (L R : Finset (Fin N)) (gamma : FiniteSites.RetainedIndex d (L ∪ R)) (B : ℕ)
    (h : borderRankLe
      (anchorTensor d T L R (anchorSliceLeft L R gamma) (anchorSliceRight L R gamma)) B) :
    borderRankLe (coefficientSlice (L ∪ R) gamma T) B := by
  rw [← anchorTensor_sliceLift_eq d T L R gamma]
  exact borderRankLe_tensorMap (anchorSliceLift d L R) h

end UniformBorderRank
