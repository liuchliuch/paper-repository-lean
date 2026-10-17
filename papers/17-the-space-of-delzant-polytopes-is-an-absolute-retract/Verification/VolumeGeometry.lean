import Verification.EuclideanConvergence
import Mathlib.Topology.Sequences

/-! The literal symmetric-difference-volume metric and the source metric
homeomorphism, including AE/AR and controlled extension in this metric. -/
noncomputable section
open scoped Topology
open Filter
namespace P17Contract

@[simp] theorem volSymmDiff_eq_symmDiffVol {n : ℕ} (K L : Set (V n)) :
    volSymmDiff K L = Paper17.symmDiffVol K L := by
  simp only [volSymmDiff, vol, Paper17.symmDiffVol, Set.symmDiff_def]

structure VolumeBody (n : ℕ) where
  body : EuclideanBody n

instance (n : ℕ) : MetricSpace (VolumeBody n) where
  dist K L := volSymmDiff K.body.body.carrier L.body.body.carrier
  dist_self K := by rw [volSymmDiff_eq_symmDiffVol, Paper17.symmDiffVol_self]
  dist_comm K L := by
    simp only [volSymmDiff_eq_symmDiffVol]
    exact Paper17.symmDiffVol_comm _ _
  dist_triangle K L M := by
    simp only [volSymmDiff_eq_symmDiffVol]
    exact Paper17.symmDiffVol_triangle _ _ _ K.body.body.isCompact.measure_lt_top.ne
      L.body.body.isCompact.measure_lt_top.ne M.body.body.isCompact.measure_lt_top.ne
  eq_of_dist_eq_zero {K L} h := by
    have hV : Tendsto (fun _ : ℕ => volSymmDiff K.body.body.carrier L.body.body.carrier) atTop (𝓝 0) := by
      simpa only [h] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    have hE := (prop_2_5_euclidean K.body (fun _ : ℕ => L.body)).mpr hV
    have hz : euclideanHausdorffDist K.body.body.carrier L.body.body.carrier = 0 :=
      tendsto_nhds_unique tendsto_const_nhds hE
    have hb : K.body = L.body := dist_eq_zero.mp (by rw [EuclideanBody.dist_eq]; exact hz)
    cases K
    cases L
    cases hb
    rfl

@[simp] theorem VolumeBody.dist_eq {n : ℕ} (K L : VolumeBody n) :
    dist K L = volSymmDiff K.body.body.carrier L.body.body.carrier := rfl

/-- Proposition 2.5 as an actual identity homeomorphism between the two
explicit metric spaces, rather than only a convergence criterion. -/
def volumeBodyHomeomorph (n : ℕ) : EuclideanBody n ≃ₜ VolumeBody n where
  toFun K := ⟨K⟩
  invFun := VolumeBody.body
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply SeqContinuous.continuous
    intro Ks K hK
    rw [tendsto_iff_dist_tendsto_zero]
    have hE := tendsto_iff_dist_tendsto_zero.mp hK
    have hE' : Tendsto (fun j => euclideanHausdorffDist K.body.carrier (Ks j).body.carrier)
        atTop (𝓝 0) := by
      simpa only [EuclideanBody.dist_eq, euclideanHausdorffDist, Metric.hausdorffDist_comm] using hE
    have hV := (prop_2_5_euclidean K Ks).mp hE'
    simpa only [VolumeBody.dist_eq, volSymmDiff_eq_symmDiffVol, Paper17.symmDiffVol_comm] using hV
  continuous_invFun := by
    apply SeqContinuous.continuous
    intro Ks K hK
    rw [tendsto_iff_dist_tendsto_zero]
    have hV := tendsto_iff_dist_tendsto_zero.mp hK
    have hV' : Tendsto (fun j => volSymmDiff K.body.body.carrier (Ks j).body.body.carrier)
        atTop (𝓝 0) := by
      simpa only [VolumeBody.dist_eq, volSymmDiff_eq_symmDiffVol, Paper17.symmDiffVol_comm] using hV
    have hE := (prop_2_5_euclidean K.body (fun j => (Ks j).body)).mpr hV'
    simpa only [EuclideanBody.dist_eq, euclideanHausdorffDist, Metric.hausdorffDist_comm] using hE

abbrev VolumeDelzantSpace (n : ℕ) := {K : VolumeBody n // IsDelzant K.body.body}

def volumeDelzantHomeomorph (n : ℕ) : EuclideanDelzantSpace n ≃ₜ VolumeDelzantSpace n where
  toFun P := ⟨⟨P.val⟩, P.property⟩
  invFun P := ⟨P.val.body, P.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := ((volumeBodyHomeomorph n).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((volumeBodyHomeomorph n).symm.continuous.comp continuous_subtype_val).subtype_mk _


end P17Contract
