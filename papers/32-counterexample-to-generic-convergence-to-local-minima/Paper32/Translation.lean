import Paper32.VariationalBridge
import Paper32.TiltMeasure

open Set Filter Topology
namespace Paper32

/-- The reverse and forward translations for the standard Clarke set in (2.1). -/
theorem clarke_sub_lin_iff {f : Point → ℝ} {z w v : Point} :
    w ∈ clarkeSubdiff (fun q => f q-lin v q) z ↔ w+v ∈ clarkeSubdiff f z := by
  constructor
  · intro hw
    have h := clarke_sub_lin_mem (v := -v) hw
    have hf : (fun q => (f q-lin v q)-lin (-v) q)=f := by
      funext q
      simp only [lin,Prod.fst_neg,Prod.snd_neg]
      ring
    simpa only [hf,sub_neg_eq_add] using h
  · intro hw
    simpa only [add_sub_cancel_right] using clarke_sub_lin_mem (v := v) hw

theorem clarkeSubdiff_sub_lin (f : Point → ℝ) (v z : Point) :
    clarkeSubdiff (fun q => f q-lin v q) z=(fun w => w-v) '' clarkeSubdiff f z := by
  ext w
  constructor
  · intro hw
    exact ⟨w+v,clarke_sub_lin_iff.mp hw,add_sub_cancel_right w v⟩
  · rintro ⟨u,hu,rfl⟩
    exact clarke_sub_lin_mem hu

theorem frechetSubdiff_sub_lin (f : Point → ℝ) (v z : Point) :
    frechetSubdiff (fun q => f q-lin v q) z=(fun w => w-v) '' frechetSubdiff f z := by
  ext w
  constructor
  · intro hw
    exact ⟨w+v,frechet_sub_lin.mp hw,add_sub_cancel_right w v⟩
  · rintro ⟨u,hu,rfl⟩
    apply frechet_sub_lin.mpr
    simpa using hu

theorem limitingSubdiff_sub_lin (f : Point → ℝ) (v z : Point) :
    limitingSubdiff (fun q => f q-lin v q) z=(fun w => w-v) '' limitingSubdiff f z := by
  ext w
  constructor
  · intro hw
    exact ⟨w+v,limiting_sub_lin.mp hw,add_sub_cancel_right w v⟩
  · rintro ⟨u,hu,rfl⟩
    apply limiting_sub_lin.mpr
    simpa using hu

theorem isOpen_tiltSquare : IsOpen tiltSquare := by
  exact isOpen_Ioo.prod isOpen_Ioo

end Paper32
