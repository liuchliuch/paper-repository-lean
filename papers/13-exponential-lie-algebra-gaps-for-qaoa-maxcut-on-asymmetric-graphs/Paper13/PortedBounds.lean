import Paper13.PortedAmplification
import Paper13.PositiveDimension
noncomputable section
namespace Paper13

/-- Proposition 5's two original finite-k bounds, on the actual graph algebra and largest constituent. -/
theorem proposition5_original_bounds {h k : ℕ} (hk : 1 ≤ k) (K : PortedGadget h) (B : SimpleGraph (Fin k)) :
    let r := Module.finrank ℂ (LinearMap.range (Matrix.toLin' K.projector))
    let d := 2^(h+1)
    Module.finrank ℝ (graphStd (portedAssemblyOrdinal K B)) ≤ (r^2+(d-r)^2)^k/2-1 ∧
      largestIrrep (portedAssemblyOrdinal K B) ≤ (max r (d-r))^k/2 := by
  have hbound := ported_amplification_bounds hk K B
  refine ⟨hbound.1,?_⟩
  apply csSup_le'
  rintro d ⟨W,hplus,hW,hd⟩
  rw [← hd]
  exact hbound.2 W hW
end Paper13
