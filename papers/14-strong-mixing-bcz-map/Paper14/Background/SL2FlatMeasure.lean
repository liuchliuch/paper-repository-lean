import Paper14.Background.SL2Coordinates

open Matrix MeasureTheory Measure Filter Set Topology
open scoped Matrix ENNReal
namespace Paper14.Background
noncomputable section

lemma slChart_left00 {z : SL2Coordinates} (hz : z 0≠0) (g : SL2R) :
    (g*slChart z) 0 0=z 0*(g 0 0-g 0 1*z 2) := by
  simp only [slChart,dif_pos hz,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
  dsimp
  ring

lemma slChart_right00 {z : SL2Coordinates} (hz : z 0≠0) (g : SL2R) :
    (slChart z*g) 0 0=z 0*g 0 0+z 1*g 1 0 := by
  simp only [slChart,dif_pos hz,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
  rfl

lemma slChart_left {z : SL2Coordinates} (hz : z 0≠0) (g : SL2R)
    (hg : g 0 0-g 0 1*z 2≠0) : slChart (slLeftCoordinates g z)=g*slChart z := by
  rw [← slCoordinates_left hz g hg]
  apply slChart_coordinates
  rw [slChart_left00 hz]
  exact mul_ne_zero hz hg

lemma slChart_right {z : SL2Coordinates} (hz : z 0≠0) (g : SL2R)
    (hg : z 0*g 0 0+z 1*g 1 0≠0) : slChart (slRightCoordinates g z)=slChart z*g := by
  rw [← slCoordinates_right hz g hg]
  apply slChart_coordinates
  rwa [slChart_right00 hz]

def slLeftGood (g : SL2R) : Set SL2Coordinates :=
  {z | z 0≠0 ∧ g 0 0-g 0 1*z 2≠0}

def slRightGood (g : SL2R) : Set SL2Coordinates :=
  {z | z 0≠0 ∧ z 0*g 0 0+z 1*g 1 0≠0}

lemma measurableSet_slLeftGood (g : SL2R) : MeasurableSet (slLeftGood g) := by
  have hH : Measurable (fun z : SL2Coordinates => g 0 0-g 0 1*z 2) := by fun_prop
  exact ((measurableSet_eq_fun (measurable_pi_apply 0) measurable_const).compl).inter
    ((measurableSet_eq_fun hH measurable_const).compl)

lemma measurableSet_slRightGood (g : SL2R) : MeasurableSet (slRightGood g) := by
  have hH : Measurable (fun z : SL2Coordinates => z 0*g 0 0+z 1*g 1 0) := by fun_prop
  exact ((measurableSet_eq_fun (measurable_pi_apply 0) measurable_const).compl).inter
    ((measurableSet_eq_fun hH measurable_const).compl)

lemma measurable_slLeftCoordinates (g : SL2R) : Measurable (slLeftCoordinates g) := by
  apply measurable_pi_lambda
  intro i
  fin_cases i <;> simp [slLeftCoordinates] <;> fun_prop

lemma measurable_slRightCoordinates (g : SL2R) : Measurable (slRightCoordinates g) := by
  apply measurable_pi_lambda
  intro i
  fin_cases i <;> simp [slRightCoordinates] <;> fun_prop

lemma slLeftGood_map (g : SL2R) {z : SL2Coordinates} (hz : z∈slLeftGood g) :
    slLeftCoordinates g z∈slLeftGood g⁻¹ := by
  have hy0 : slLeftCoordinates g z 0≠0 := by
    simpa [slLeftCoordinates] using mul_ne_zero hz.1 hz.2
  refine ⟨hy0,?_⟩
  have heq : (g⁻¹*slChart (slLeftCoordinates g z)) 0 0=z 0 := by
    rw [slChart_left hz.1 g hz.2,inv_mul_cancel_left]
    simp [slChart,hz.1]
  rw [slChart_left00 hy0] at heq
  intro h
  rw [h,mul_zero] at heq
  exact hz.1 heq.symm

lemma slLeftCoordinates_inv (g : SL2R) {z : SL2Coordinates} (hz : z∈slLeftGood g) :
    slLeftCoordinates g⁻¹ (slLeftCoordinates g z)=z := by
  have hy := slLeftGood_map g hz
  rw [← slCoordinates_left hy.1 g⁻¹ hy.2,slChart_left hz.1 g hz.2,inv_mul_cancel_left]
  exact slCoordinates_chart hz.1

lemma slLeftCoordinates_injOn (g : SL2R) : InjOn (slLeftCoordinates g) (slLeftGood g) := by
  intro z hz w hw heq
  have h := congrArg (slLeftCoordinates g⁻¹) heq
  simpa [slLeftCoordinates_inv g hz,slLeftCoordinates_inv g hw] using h

lemma slLeftCoordinates_image (g : SL2R) :
    slLeftCoordinates g '' slLeftGood g=slLeftGood g⁻¹ := by
  ext y
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact slLeftGood_map g hz
  · intro hy
    refine ⟨slLeftCoordinates g⁻¹ y,?_,?_⟩
    · simpa using slLeftGood_map g⁻¹ hy
    · simpa using slLeftCoordinates_inv g⁻¹ hy

lemma ae_slCoordinate_ne (i : Fin 3) (r : ℝ) : ∀ᵐ z : SL2Coordinates ∂volume,z i≠r := by
  simpa only [volume_pi] using Measure.ae_eval_ne (fun _ : Fin 3 => (volume : Measure ℝ)) i r

lemma ae_slLeftGood (g : SL2R) : ∀ᵐ z : SL2Coordinates ∂volume,z∈slLeftGood g := by
  by_cases hb : g 0 1=0
  · have ha : g 0 0≠0 := by
      have hd : g 0 0*g 1 1-g 0 1*g 1 0=1 := by simpa only [Matrix.det_fin_two] using g.property
      intro h
      simp [h,hb] at hd
    filter_upwards [ae_slCoordinate_ne 0 0] with z hz
    exact ⟨hz,by simpa [hb] using ha⟩
  · filter_upwards [ae_slCoordinate_ne 0 0,ae_slCoordinate_ne 2 (g 0 0/g 0 1)] with z hz ht
    refine ⟨hz,?_⟩
    intro h
    apply ht
    apply (eq_div_iff hb).mpr
    nlinarith

/-- Left multiplication preserves ordinary three-dimensional Lebesgue measure
in the big-cell coordinates; all excluded coordinate hyperplanes are null. -/
theorem measurePreserving_slLeftCoordinates (g : SL2R) :
    MeasurePreserving (slLeftCoordinates g) volume volume := by
  have hJac := map_withDensity_abs_det_fderiv_eq_addHaar
    (volume : Measure SL2Coordinates) (measurableSet_slLeftGood g).nullMeasurableSet
    (fun z hz => (slLeft_hasFDerivAt g hz.1 hz.2).hasFDerivWithinAt)
    (slLeftCoordinates_injOn g)
  have hden : (fun z : SL2Coordinates => ENNReal.ofReal |(slLeftDerivative g z).toLinearMap.det|)
      =ᵐ[volume.restrict (slLeftGood g)] (fun _ => 1) := by
    filter_upwards [ae_restrict_mem (measurableSet_slLeftGood g)] with z hz
    rw [slLeftDerivative_det g hz.2]
    norm_num
  rw [withDensity_congr_ae hden] at hJac
  change Measure.map (slLeftCoordinates g)
    ((volume.restrict (slLeftGood g)).withDensity (1 : SL2Coordinates → ℝ≥0∞)) = _ at hJac
  rw [withDensity_one,slLeftCoordinates_image,
    Measure.restrict_eq_self_of_ae_mem (ae_slLeftGood g),
    Measure.restrict_eq_self_of_ae_mem (ae_slLeftGood g⁻¹)] at hJac
  exact ⟨measurable_slLeftCoordinates g,hJac⟩

lemma slRightGood_map (g : SL2R) {z : SL2Coordinates} (hz : z∈slRightGood g) :
    slRightCoordinates g z∈slRightGood g⁻¹ := by
  have hy0 : slRightCoordinates g z 0≠0 := by simpa [slRightCoordinates] using hz.2
  refine ⟨hy0,?_⟩
  have heq : (slChart (slRightCoordinates g z)*g⁻¹) 0 0=z 0 := by
    rw [slChart_right hz.1 g hz.2,mul_inv_cancel_right]
    simp [slChart,hz.1]
  rw [slChart_right00 hy0] at heq
  intro h
  rw [h] at heq
  exact hz.1 heq.symm

lemma slRightCoordinates_inv (g : SL2R) {z : SL2Coordinates} (hz : z∈slRightGood g) :
    slRightCoordinates g⁻¹ (slRightCoordinates g z)=z := by
  have hy := slRightGood_map g hz
  rw [← slCoordinates_right hy.1 g⁻¹ hy.2,slChart_right hz.1 g hz.2,mul_inv_cancel_right]
  exact slCoordinates_chart hz.1

lemma slRightCoordinates_injOn (g : SL2R) : InjOn (slRightCoordinates g) (slRightGood g) := by
  intro z hz w hw heq
  have h := congrArg (slRightCoordinates g⁻¹) heq
  simpa [slRightCoordinates_inv g hz,slRightCoordinates_inv g hw] using h

lemma slRightCoordinates_image (g : SL2R) :
    slRightCoordinates g '' slRightGood g=slRightGood g⁻¹ := by
  ext y
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact slRightGood_map g hz
  · intro hy
    refine ⟨slRightCoordinates g⁻¹ y,?_,?_⟩
    · simpa using slRightGood_map g⁻¹ hy
    · simpa using slRightCoordinates_inv g⁻¹ hy

lemma ae_slRightGood (g : SL2R) : ∀ᵐ z : SL2Coordinates ∂volume,z∈slRightGood g := by
  let L : SL2Coordinates →L[ℝ] ℝ := g 0 0 • slCoordProj 0+g 1 0 • slCoordProj 1
  have hproper : LinearMap.ker L.toLinearMap≠⊤ := by
    intro htop
    have hz : (![g 0 0,g 1 0,0] : SL2Coordinates)∈LinearMap.ker L.toLinearMap := by rw [htop]; trivial
    change g 0 0*g 0 0+g 1 0*g 1 0=0 at hz
    have ha : g 0 0=0 := by nlinarith [sq_nonneg (g 1 0)]
    have hc : g 1 0=0 := by nlinarith
    have hd : g 0 0*g 1 1-g 0 1*g 1 0=1 := by simpa only [Matrix.det_fin_two] using g.property
    simp [ha,hc] at hd
  have hnull : volume {z : SL2Coordinates | z 0*g 0 0+z 1*g 1 0=0}=0 := by
    convert addHaar_submodule (volume : Measure SL2Coordinates) (LinearMap.ker L.toLinearMap) hproper using 1
    congr 1
    ext z
    simp [L,slCoordProj,mul_comm]
  have hH : ∀ᵐ z : SL2Coordinates ∂volume,z 0*g 0 0+z 1*g 1 0≠0 := by
    rw [ae_iff]
    simpa only [not_not] using hnull
  filter_upwards [ae_slCoordinate_ne 0 0,hH] with z hz hH
  exact ⟨hz,hH⟩

/-- Right multiplication likewise preserves the flat coordinate measure. -/
theorem measurePreserving_slRightCoordinates (g : SL2R) :
    MeasurePreserving (slRightCoordinates g) volume volume := by
  have hJac := map_withDensity_abs_det_fderiv_eq_addHaar
    (volume : Measure SL2Coordinates) (measurableSet_slRightGood g).nullMeasurableSet
    (fun z hz => (slRight_hasFDerivAt g hz.1 hz.2).hasFDerivWithinAt)
    (slRightCoordinates_injOn g)
  have hden : (fun z : SL2Coordinates => ENNReal.ofReal |(slRightDerivative g z).toLinearMap.det|)
      =ᵐ[volume.restrict (slRightGood g)] (fun _ => 1) := by
    filter_upwards [] with z
    rw [slRightDerivative_det]
    norm_num
  rw [withDensity_congr_ae hden] at hJac
  change Measure.map (slRightCoordinates g)
    ((volume.restrict (slRightGood g)).withDensity (1 : SL2Coordinates → ℝ≥0∞)) = _ at hJac
  rw [withDensity_one,slRightCoordinates_image,
    Measure.restrict_eq_self_of_ae_mem (ae_slRightGood g),
    Measure.restrict_eq_self_of_ae_mem (ae_slRightGood g⁻¹)] at hJac
  exact ⟨measurable_slRightCoordinates g,hJac⟩

/-- The actual invariant measure on SL₂(ℝ), in flat section/flow coordinates. -/
def slFlatMeasure : Measure SL2R := Measure.map slChart volume

instance : SFinite slFlatMeasure := by unfold slFlatMeasure; infer_instance

instance slFlatMeasure_leftInvariant : slFlatMeasure.IsMulLeftInvariant where
  map_mul_left_eq_self g := by
    have hm : Measurable (fun h : SL2R => g*h) := (continuous_const.mul continuous_id).measurable
    change Measure.map (fun h => g*h) (Measure.map slChart volume)=Measure.map slChart volume
    rw [Measure.map_map hm measurable_slChart]
    calc
      Measure.map ((fun h => g*h) ∘ slChart) volume =
          Measure.map (slChart ∘ slLeftCoordinates g) volume := by
        apply Measure.map_congr
        filter_upwards [ae_slLeftGood g] with z hz
        exact (slChart_left hz.1 g hz.2).symm
      _ = Measure.map slChart (Measure.map (slLeftCoordinates g) volume) :=
        (Measure.map_map measurable_slChart (measurable_slLeftCoordinates g)).symm
      _ = Measure.map slChart volume := by rw [(measurePreserving_slLeftCoordinates g).map_eq]

instance slFlatMeasure_rightInvariant : slFlatMeasure.IsMulRightInvariant where
  map_mul_right_eq_self g := by
    have hm : Measurable (fun h : SL2R => h*g) := (continuous_id.mul continuous_const).measurable
    change Measure.map (fun h => h*g) (Measure.map slChart volume)=Measure.map slChart volume
    rw [Measure.map_map hm measurable_slChart]
    calc
      Measure.map ((fun h => h*g) ∘ slChart) volume =
          Measure.map (slChart ∘ slRightCoordinates g) volume := by
        apply Measure.map_congr
        filter_upwards [ae_slRightGood g] with z hz
        exact (slChart_right hz.1 g hz.2).symm
      _ = Measure.map slChart (Measure.map (slRightCoordinates g) volume) :=
        (Measure.map_map measurable_slChart (measurable_slRightCoordinates g)).symm
      _ = Measure.map slChart volume := by rw [(measurePreserving_slRightCoordinates g).map_eq]

end
end Paper14.Background
