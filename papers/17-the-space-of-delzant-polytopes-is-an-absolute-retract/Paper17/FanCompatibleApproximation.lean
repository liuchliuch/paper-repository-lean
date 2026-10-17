import Paper17.DelzantDensity
import Paper17.CloseRefinement

/-! The full fan-compatible approximation assertion of Lemma 4.2. -/
noncomputable section
namespace Paper17

/-- Approximate a positive convex body by a genuine Delzant polytope whose
normal fan refines all members of a prescribed finite family. -/
theorem lemma_4_2 {n m : ℕ} (K : PosBody n) (Ps : Fin m → DelzantPolytope n)
    {η : ℝ} (hη : 0 < η) :
    ∃ Q : DelzantPolytope n, Metric.hausdorffDist Q.carrier K.carrier < η ∧
      ∀ i, DelzantPolytope.le (Ps i) Q := by
  obtain ⟨P, hP⟩ := exists_delzant_near K (by linarith : (0 : ℝ) < η / 2)
  obtain ⟨Q, hQ, _, hfan⟩ := DelzantPolytope.lemma_2_3 P Ps
    (by linarith : (0 : ℝ) < η / 2)
  refine ⟨Q, ?_, hfan⟩
  have hfin : EMetric.hausdorffEdist P.carrier K.carrier ≠ ⊤ :=
    Metric.hausdorffEdist_ne_top_of_nonempty_of_bounded P.val.nonempty K.nonempty
      P.val.isCompact.isBounded K.isCompact.isBounded
  calc Metric.hausdorffDist Q.carrier K.carrier
      ≤ Metric.hausdorffDist Q.carrier P.carrier + Metric.hausdorffDist P.carrier K.carrier :=
        Metric.hausdorffDist_triangle' hfin
    _ < η / 2 + η / 2 := add_lt_add hQ hP
    _ = η := by ring

end Paper17
