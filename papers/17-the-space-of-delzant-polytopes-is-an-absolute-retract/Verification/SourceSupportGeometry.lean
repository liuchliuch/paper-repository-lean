import Verification.EuclideanMetric

/-! Convexity of the actual positive-body image in the source support space. -/
noncomputable section
open scoped Topology Pointwise
namespace P17Contract

theorem positive_body_support_convex (n : ℕ) :
    Convex ℝ (Set.range (@bodySphericalSupport n)) := by
  rintro _ ⟨K, rfl⟩ _ ⟨L, rfl⟩ a b ha hb hab
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simp only [ha0, hb1, zero_smul, one_smul, zero_add]
    exact ⟨L, rfl⟩
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    simp only [hb0, ha1, zero_smul, one_smul, add_zero]
    exact ⟨K, rfl⟩
  let K' : Paper17.PosBody n := ⟨K.carrier, K.convex, K.isCompact, K.interior_nonempty⟩
  let L' : Paper17.PosBody n := ⟨L.carrier, L.convex, L.isCompact, L.interior_nonempty⟩
  let M := (K'.smul a ha0).add (L'.smul b hb0)
  let M' : PosBody n := ⟨M.carrier, M.convex, M.isCompact, M.interior_nonempty⟩
  refine ⟨M', ?_⟩
  ext u
  simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, bodySphericalSupport_apply,
    smul_eq_mul]
  exact Paper17.supportFunction_minkowski K.isCompact K.nonempty L.isCompact L.nonempty a b ha hb u.val

end P17Contract
