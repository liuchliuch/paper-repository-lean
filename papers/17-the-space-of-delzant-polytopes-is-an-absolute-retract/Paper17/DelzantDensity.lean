import Paper17.RationalNormalCones
import Paper17.ChainGeometry

/-! Actual density via rational vertices, projective resolution and small
Minkowski perturbation along the resolved fan. -/
noncomputable section
open scoped Pointwise
namespace Paper17

/-- The constructed resolution refines the actual finite normal fan. -/
theorem exists_delzant_refining_normalFan {n : ℕ} (P : Polytope n)
    (hP : HasRationalNormalPresentation P) :
    ∃ S : DelzantPolytope n, (NormalFan S.val).refines (NormalFan P) := by
  classical
  obtain ⟨S, hS⟩ := exists_delzant_refinement_of_rational_normal P hP
  refine ⟨S, ?_⟩
  intro C hC
  obtain ⟨y, hy, hCy⟩ := hS C hC
  obtain ⟨v, hv, hyv⟩ := exists_vertex_normalCone_superset P hy
  exact ⟨normalConeAt P v, Finset.mem_image.mpr ⟨v, hv, rfl⟩, hCy.trans hyv⟩

/-- A positive perturbation of a full-dimensional polytope by a Delzant
refinement is Delzant. The first summand need not already be smooth. -/
theorem add_smul_isDelzant_of_refines {n : ℕ} (R : Polytope n) (hR : R.IsFullDim)
    (S : DelzantPolytope n) (hS : (NormalFan S.val).refines (NormalFan R))
    {t : ℝ} (ht : 0 < t) : IsDelzant (R.add (S.val.smul t)) := by
  have hadd := normalFan_add R (S.val.smul t)
  rw [normalFan_smul_eq S.val ht] at hadd
  have hmeet := Fan.meet_equiv_of_refines hS
  have heq : Fan.Equivalent (NormalFan (R.add (S.val.smul t))) (NormalFan S.val) :=
    ⟨Fan.refines_trans hadd.1 hmeet.1, Fan.refines_trans hmeet.2 hadd.2⟩
  refine ⟨?_, normalFan_isSmooth_of_equivalent heq S.property.2⟩
  change (interior (R.add (S.val.smul t)).carrier).Nonempty
  rw [carrier_add_eq, carrier_smul_eq]
  exact (PosBody.add (R.toPosBody hR)
    (PosBody.smul t ht.ne' (S.val.toPosBody S.property.1))).interior_nonempty

/-- Genuine pointwise density of Delzant carriers, with no prescribed fans. -/
theorem exists_delzant_near {n : ℕ} (K : PosBody n) {η : ℝ} (hη : 0 < η) :
    ∃ Q : DelzantPolytope n, Metric.hausdorffDist Q.carrier K.carrier < η := by
  obtain ⟨R, hRdim, hRrat, hRclose⟩ := exists_ratPolytope_near K
    (by linarith : (0 : ℝ) < η / 2)
  let P : Polytope n := ⟨R.verts, R.nonempty_verts'⟩
  have hP : P.IsFullDim := hRdim
  have hrat : HasRationalNormalPresentation P :=
    hasRationalNormalPresentation_of_rational_vertices P hP hRrat
  obtain ⟨S, hS⟩ := exists_delzant_refining_normalFan P hrat
  obtain ⟨t, ht, hclose⟩ := DelzantPolytope.lemma_2_3_perturbation P S.val
    (by linarith : (0 : ℝ) < η / 2)
  let Q : DelzantPolytope n := ⟨P.add (S.val.smul t), add_smul_isDelzant_of_refines P hP S hS ht⟩
  refine ⟨Q, ?_⟩
  have hfin : EMetric.hausdorffEdist P.carrier K.carrier ≠ ⊤ :=
    Metric.hausdorffEdist_ne_top_of_nonempty_of_bounded P.nonempty K.nonempty
      P.isCompact.isBounded K.isCompact.isBounded
  calc Metric.hausdorffDist Q.carrier K.carrier
      ≤ Metric.hausdorffDist Q.carrier P.carrier + Metric.hausdorffDist P.carrier K.carrier :=
        Metric.hausdorffDist_triangle' hfin
    _ < η / 2 + η / 2 := add_lt_add hclose hRclose
    _ = η := by ring

end Paper17
