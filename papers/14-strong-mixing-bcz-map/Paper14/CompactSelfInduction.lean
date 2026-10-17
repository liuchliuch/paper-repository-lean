import Paper14.CompactDynamics
import Paper14.GraphMeasures

open MeasureTheory Set Function Filter Topology
open scoped ENNReal
namespace Paper14
noncomputable section

lemma compactClamp_coe (z : CompactBCZ) : compactClamp z.val = z :=
  Subtype.ext (compactClamp_val_of_mem z.property)

lemma mr_eq_normalizedRestriction {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    mr r = normalizedRestriction m (Yr r) := by
  rw [normalizedRestriction,m_Yr hr hr1,mr,ENNReal.rpow_two,← ENNReal.ofReal_pow hr.le]

def compactPhi (r : ℝ) (z : CompactBCZ) : CompactBCZ := compactClamp (phiR r z.val)
def compactPhiInv (r : ℝ) (z : CompactBCZ) : CompactBCZ := compactClamp (phiRInv r z.val)

lemma measurable_compactPhi (r : ℝ) : Measurable (compactPhi r) :=
  continuous_compactClamp.measurable.comp ((measurable_phiR r).comp measurable_subtype_coe)
lemma measurable_compactPhiInv (r : ℝ) : Measurable (compactPhiInv r) :=
  continuous_compactClamp.measurable.comp ((measurable_phiRInv r).comp measurable_subtype_coe)

lemma compactPhi_coe {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {z : CompactBCZ}
    (hz : (z : ℝ × ℝ) ∈ Omega) : (compactPhi r z : ℝ × ℝ) = phiR r z.val :=
  compactClamp_val_of_mem (Omega_subset_compactBCZ (phiR_mem_Yr hr hr1 hz).1)

lemma compactPhiInv_coe {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {z : CompactBCZ}
    (hz : z ∈ compactYr r) : (compactPhiInv r z : ℝ × ℝ) = phiRInv r z.val :=
  compactClamp_val_of_mem (Omega_subset_compactBCZ (phiRInv_mem_Omega hr hr1 hz))

lemma measurePreserving_compactCoe_section {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    MeasurePreserving (Subtype.val : CompactBCZ → ℝ × ℝ)
      (normalizedRestriction compactBCZMeasure (compactYr r)) (mr r) := by
  rw [mr_eq_normalizedRestriction hr hr1]
  unfold normalizedRestriction
  rw [compactYr_mass]
  exact (measurePreserving_compactCoe.restrict_preimage (measurableSet_Yr r)).smul_measure _

lemma measurePreserving_compactClamp_section {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    MeasurePreserving compactClamp (mr r) (normalizedRestriction compactBCZMeasure (compactYr r)) := by
  refine ⟨continuous_compactClamp.measurable,?_⟩
  rw [← (measurePreserving_compactCoe_section hr hr1).map_eq,
    Measure.map_map continuous_compactClamp.measurable measurable_subtype_coe]
  have heq : compactClamp ∘ (Subtype.val : CompactBCZ → ℝ × ℝ) = id := by
    funext z
    exact compactClamp_coe z
  rw [heq,Measure.map_id]

/-- The actual self-induction pushforward transfers to the compact carrier. -/
theorem measurePreserving_compactPhi {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    MeasurePreserving (compactPhi r) compactBCZMeasure
      (normalizedRestriction compactBCZMeasure (compactYr r)) := by
  have hp := (measurePreserving_compactClamp_section hr hr1).comp (measurePreserving_phiR r hr hr1)
  refine ⟨measurable_compactPhi r,?_⟩
  rw [compactBCZMeasure,Measure.map_map (measurable_compactPhi r) continuous_compactClamp.measurable]
  have heq : (compactPhi r ∘ compactClamp) =ᵐ[m] (compactClamp ∘ phiR r) := by
    filter_upwards [ae_mem_Omega] with x hx
    change compactClamp (phiR r (compactClamp x : ℝ × ℝ)) = compactClamp (phiR r x)
    rw [compactClamp_val_of_mem (Omega_subset_compactBCZ hx)]
  rw [Measure.map_congr heq]
  exact hp.map_eq

lemma compactPhi_inverse_ae {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    (∀ᵐ z ∂compactBCZMeasure, compactPhiInv r (compactPhi r z) = z) ∧
    (∀ᵐ z ∂normalizedRestriction compactBCZMeasure (compactYr r), compactPhi r (compactPhiInv r z) = z) := by
  constructor
  · filter_upwards [ae_compact_mem_Omega] with z hz
    have hy : compactPhi r z ∈ compactYr r := by
      change (compactPhi r z : ℝ × ℝ) ∈ Yr r
      rw [compactPhi_coe hr hr1 hz]
      exact phiR_mem_Yr hr hr1 hz
    apply Subtype.ext
    rw [compactPhiInv_coe hr hr1 hy,compactPhi_coe hr hr1 hz]
    exact phiRInv_phiR hr hr1 hz
  · filter_upwards [normalizedRestriction_ae_mem (μ := compactBCZMeasure) (measurableSet_compactYr r)] with z hz
    have hx : (compactPhiInv r z : ℝ × ℝ) ∈ Omega := by
      rw [compactPhiInv_coe hr hr1 hz]
      exact phiRInv_mem_Omega hr hr1 hz
    apply Subtype.ext
    rw [compactPhi_coe hr hr1 hx,compactPhiInv_coe hr hr1 hz]
    exact phiR_phiRInv hr hr1 hz

lemma compactPhi_induced_conjugacy {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∀ᵐ z ∂compactBCZMeasure, inducedMap compactB (compactYr r) (compactPhi r z) = compactPhi r (compactB z) := by
  filter_upwards [ae_compact_mem_Omega] with z hz
  have hx : (compactPhi r z : ℝ × ℝ) ∈ Omega := by
    rw [compactPhi_coe hr hr1 hz]
    exact (phiR_mem_Yr hr hr1 hz).1
  have hb : (compactB z : ℝ × ℝ) ∈ Omega := by rw [compactB_coe hz]; exact B_mem_Omega hz
  apply Subtype.ext
  rw [compact_induced_coe hx,compactPhi_coe hr hr1 hz,compactPhi_coe hr hr1 hb,compactB_coe hz]
  exact (phiR_first_return_point hr hr1 hz).1

lemma compactPhi_tendsto_pointwise {z : CompactBCZ} (hz : (z : ℝ × ℝ) ∈ Omega) :
    Tendsto (fun r : ℝ => compactPhi r z) (𝓝[<] (1 : ℝ)) (𝓝 z) := by
  have hh := continuous_compactClamp.continuousAt.tendsto.comp (phiR_tendsto_pointwise hz)
  simpa only [compactClamp_coe z] using hh

lemma compactPhi_tendstoInMeasure (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝[<] (1 : ℝ))) :
    TendstoInMeasure compactBCZMeasure (fun n => compactPhi (r n)) atTop id := by
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    exact (measurable_compactPhi (r n)).aestronglyMeasurable
  · filter_upwards [ae_compact_mem_Omega] with z hz
    exact (compactPhi_tendsto_pointwise hz).comp hr

end
end Paper14
