import Verification.Bridge
import Paper17.IntegralHalfspacePresentation

/-! The original general rational-normal-fan contract, using the actual smooth
projective resolution construction and canonical carrier normal cones. -/
noncomputable section
open scoped BigOperators
namespace P17Contract

theorem rational_normal_refinement {n : ℕ} (K : PosBody n) (hK : HasRationalNormalFan K) :
    ∃ Q : DelzantSpace n, bodyRefines Q.1 K := by
  classical
  obtain ⟨verts, hcar, hcones⟩ := hK
  have hne : verts.Nonempty := by
    have hh : (convexHull ℝ (verts : Set (V n))).Nonempty := by rw [hcar]; exact K.nonempty
    exact convexHull_nonempty_iff.mp hh
  let P : Paper17.Polytope n := ⟨verts, hne⟩
  have hPcar : P.carrier = K.carrier := hcar
  have hP : Paper17.HasRationalNormalPresentation P := by
    intro v hv
    obtain ⟨m, rays, hcone⟩ := hcones v hv
    refine ⟨m, rays, ?_⟩
    have hprod : (Paper17.normalConeAt P v : Set (V n)) = normalCone K.carrier v := by
      rw [production_normalCone, hPcar]
    exact hprod.trans hcone
  obtain ⟨Q, hQ⟩ := Paper17.exists_delzant_refinement_of_rational_normal P hP
  refine ⟨ofProduction Q, ?_⟩
  intro v hv
  obtain ⟨q, hq, hsub⟩ := Paper17.exists_vertex_normalCone_superset Q.val hv
  obtain ⟨w, hw, hqw⟩ := hQ (Paper17.normalConeAt Q.val q) (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
  refine ⟨w, hPcar ▸ hw, ?_⟩
  have hprod : (Paper17.normalConeAt P w : Set (V n)) = normalCone K.carrier w := by
    rw [production_normalCone, hPcar]
  rw [hprod] at hqw
  exact hsub.trans hqw

end P17Contract
