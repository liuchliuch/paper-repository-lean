import Paper14.AeFactors
import Paper14.ReturnGeometry
import Paper14.MeasureBCZ

open MeasureTheory Set Function Filter Topology
namespace Paper14
noncomputable section

def compactBCZSet : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
abbrev CompactBCZ := ↥compactBCZSet

instance : CompactSpace CompactBCZ := isCompact_iff_compactSpace.mp (isCompact_Icc.prod isCompact_Icc)
instance : Nonempty CompactBCZ := ⟨⟨(1,1),⟨⟨by norm_num,le_rfl⟩,⟨by norm_num,le_rfl⟩⟩⟩⟩

def compactClamp (x : ℝ × ℝ) : CompactBCZ :=
  ⟨(max 0 (min 1 x.1),max 0 (min 1 x.2)),
    ⟨⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩,
     ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩⟩⟩

lemma continuous_compactClamp : Continuous compactClamp := by
  exact (show Continuous (fun x : ℝ × ℝ => (max 0 (min 1 x.1),max 0 (min 1 x.2))) from by fun_prop).subtype_mk _

lemma compactClamp_val_of_mem {x : ℝ × ℝ} (hx : x ∈ compactBCZSet) :
    (compactClamp x : ℝ × ℝ) = x := by
  apply Prod.ext <;> simp only [compactClamp,Subtype.coe_mk]
  · rw [min_eq_right hx.1.2,max_eq_right hx.1.1]
  · rw [min_eq_right hx.2.2,max_eq_right hx.2.1]

lemma Omega_subset_compactBCZ : Omega ⊆ compactBCZSet := fun x hx =>
  ⟨⟨hx.1.le,hx.2.1⟩,⟨hx.2.2.1.le,hx.2.2.2.1⟩⟩

def compactBCZMeasure : Measure CompactBCZ := Measure.map compactClamp m

theorem measurePreserving_compactClamp : MeasurePreserving compactClamp m compactBCZMeasure :=
  ⟨continuous_compactClamp.measurable,rfl⟩

instance : IsProbabilityMeasure compactBCZMeasure := by
  constructor
  rw [compactBCZMeasure,Measure.map_apply continuous_compactClamp.measurable MeasurableSet.univ]
  simp

theorem measurePreserving_compactCoe : MeasurePreserving (Subtype.val : CompactBCZ → ℝ × ℝ) compactBCZMeasure m := by
  refine ⟨measurable_subtype_coe,?_⟩
  rw [compactBCZMeasure,Measure.map_map measurable_subtype_coe continuous_compactClamp.measurable]
  have heq : (Subtype.val ∘ compactClamp : (ℝ × ℝ) → ℝ × ℝ) =ᵐ[m] id := by
    filter_upwards [ae_mem_Omega] with x hx
    exact compactClamp_val_of_mem (Omega_subset_compactBCZ hx)
  rw [Measure.map_congr heq,Measure.map_id]

lemma ae_compact_mem_Omega : ∀ᵐ z : CompactBCZ ∂compactBCZMeasure, (z : ℝ × ℝ) ∈ Omega :=
  measurePreserving_compactCoe.quasiMeasurePreserving.ae ae_mem_Omega

def compactB (z : CompactBCZ) : CompactBCZ := compactClamp (B z.val)
def compactBinv (z : CompactBCZ) : CompactBCZ := compactClamp (Binv z.val)

lemma measurable_compactB : Measurable compactB :=
  continuous_compactClamp.measurable.comp (measurable_B.comp measurable_subtype_coe)
lemma measurable_compactBinv : Measurable compactBinv :=
  continuous_compactClamp.measurable.comp (measurable_Binv.comp measurable_subtype_coe)

lemma compactB_coe {z : CompactBCZ} (hz : (z : ℝ × ℝ) ∈ Omega) :
    (compactB z : ℝ × ℝ) = B z.val := compactClamp_val_of_mem (Omega_subset_compactBCZ (B_mem_Omega hz))
lemma compactBinv_coe {z : CompactBCZ} (hz : (z : ℝ × ℝ) ∈ Omega) :
    (compactBinv z : ℝ × ℝ) = Binv z.val := compactClamp_val_of_mem (Omega_subset_compactBCZ (Binv_mem_Omega hz))

lemma compactB_ae_factor : ∀ᵐ x ∂m, compactClamp (B x) = compactB (compactClamp x) := by
  filter_upwards [ae_mem_Omega] with x hx
  unfold compactB
  rw [compactClamp_val_of_mem (Omega_subset_compactBCZ hx)]

theorem measurePreserving_compactB : MeasurePreserving compactB compactBCZMeasure compactBCZMeasure :=
  measurePreserving_of_ae_factor measurePreserving_B measurePreserving_compactClamp measurable_compactB compactB_ae_factor

theorem weakMixing_compactB (hweak : WeakMixing B m) : WeakMixing compactB compactBCZMeasure := by
  refine ⟨measurePreserving_compactB,?_⟩
  have hp := measurePreserving_compactClamp.prod measurePreserving_compactClamp
  apply ergodic_of_ae_factor hweak.2 hp (measurable_compactB.comp measurable_fst |>.prodMk (measurable_compactB.comp measurable_snd))
  have h1 := (measurePreserving_fst (μ := m) (ν := m)).quasiMeasurePreserving.ae compactB_ae_factor
  have h2 := (measurePreserving_snd (μ := m) (ν := m)).quasiMeasurePreserving.ae compactB_ae_factor
  filter_upwards [h1,h2] with z hz1 hz2
  exact Prod.ext hz1 hz2

lemma compact_inverse_ae : (∀ᵐ z ∂compactBCZMeasure, compactBinv (compactB z) = z) ∧
    (∀ᵐ z ∂compactBCZMeasure, compactB (compactBinv z) = z) := by
  constructor
  · filter_upwards [ae_compact_mem_Omega] with z hz
    apply Subtype.ext
    have hb : (compactB z : ℝ × ℝ) ∈ Omega := by rw [compactB_coe hz]; exact B_mem_Omega hz
    rw [compactBinv_coe hb,compactB_coe hz]
    exact Binv_B z.val.1 z.val.2 hz
  · filter_upwards [ae_compact_mem_Omega] with z hz
    apply Subtype.ext
    have hb : (compactBinv z : ℝ × ℝ) ∈ Omega := by rw [compactBinv_coe hz]; exact Binv_mem_Omega hz
    rw [compactB_coe hb,compactBinv_coe hz]
    exact B_Binv z.val.1 z.val.2 hz

end
end Paper14
