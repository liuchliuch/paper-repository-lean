import Paper14.Background.PrimitiveApproximation
import Paper14.LatticeQuotient

open Matrix Set Function Filter Topology MeasureTheory
open scoped Matrix ENNReal
namespace Paper14
noncomputable section
open Background

lemma slUpper_integer_mem (j : ℤ) : slUpper (j : ℝ)∈slIntegerSubgroup := by
  apply (mem_slIntegerSubgroup _).mpr
  intro i k
  fin_cases i <;> fin_cases k
  · exact ⟨1,by norm_num [slUpper]⟩
  · exact ⟨j,rfl⟩
  · exact ⟨0,by norm_num [slUpper]⟩
  · exact ⟨1,by norm_num [slUpper]⟩

lemma slRightUpper_entries (g : SL2R) (t : ℝ) :
    (g*slUpper t) 0 0=g 0 0 ∧ (g*slUpper t) 0 1=g 0 0*t+g 0 1 ∧
      (g*slUpper t) 1 0=g 1 0 := by
  simp [Matrix.SpecialLinearGroup.coe_mul,slUpper,Matrix.mul_apply,Fin.sum_univ_two]

/-- A positive, irrational top-row slope places a genuine BCZ section in the past. -/
theorem sl_quotient_has_past_section_pos (g : SL2R) (ha : 0<g 0 0)
    (hξ : Irrational (g 0 1/g 0 0)) :
    ∃ x∈Omega,∃ T : ℝ,0≤T ∧
      (QuotientGroup.mk g : SL2R ⧸ slIntegerSubgroup)=QuotientGroup.mk (slChart ![x.1,x.2,T]) := by
  obtain ⟨γ,hγ0,hγ1,hγv⟩ := sl_exists_short_negative_column g ha hξ
  let g₁ := g*slIntegerEmbedding γ
  let j : ℤ := ⌊(1-g₁ 0 1)/g₁ 0 0⌋
  let g₂ := g₁*slUpper (j : ℝ)
  have hg₁ : 0<g₁ 0 0 := hγ0
  have hg₁1 : g₁ 0 0≤1 := hγ1
  have hentry : g₂ 0 0=g₁ 0 0 ∧ g₂ 0 1=g₁ 0 0*(j : ℝ)+g₁ 0 1 ∧ g₂ 1 0=g₁ 1 0 :=
    slRightUpper_entries g₁ (j : ℝ)
  have hlo : (j : ℝ)*g₁ 0 0≤1-g₁ 0 1 :=
    (le_div_iff₀ hg₁).mp (Int.floor_le _)
  have hhi : 1-g₁ 0 1<((j : ℝ)+1)*g₁ 0 0 :=
    (div_lt_iff₀ hg₁).mp (Int.lt_floor_add_one _)
  let x : ℝ × ℝ := (g₂ 0 0,g₂ 0 1)
  have hx : x∈Omega := by
    change 0<g₂ 0 0 ∧ g₂ 0 0≤1 ∧ 0<g₂ 0 1 ∧ g₂ 0 1≤1 ∧ 1<g₂ 0 0+g₂ 0 1
    rw [hentry.1,hentry.2.1]
    exact ⟨hg₁,hg₁1,by nlinarith,by nlinarith,by nlinarith⟩
  let T := -g₂ 1 0/g₂ 0 0
  have hT : 0≤T := by
    apply div_nonneg _ hx.1.le
    rw [hentry.2.2]
    exact neg_nonneg.mpr hγv.le
  refine ⟨x,hx,T,hT,?_⟩
  calc
    (QuotientGroup.mk g : SL2R ⧸ slIntegerSubgroup)=QuotientGroup.mk g₁ :=
      (QuotientGroup.mk_mul_of_mem g (show slIntegerEmbedding γ∈slIntegerSubgroup from ⟨γ,rfl⟩)).symm
    _ = QuotientGroup.mk g₂ := (QuotientGroup.mk_mul_of_mem g₁ (slUpper_integer_mem j)).symm
    _ = QuotientGroup.mk (slChart ![x.1,x.2,T]) := by
      have hch := slChart_coordinates (g := g₂) hx.1.ne'
      exact congrArg QuotientGroup.mk hch.symm

lemma slMinusOne_integer_mem : slDiagonal (-1) (by norm_num)∈slIntegerSubgroup := by
  apply (mem_slIntegerSubgroup _).mpr
  intro i k
  fin_cases i <;> fin_cases k
  · exact ⟨-1,by norm_num [slDiagonal]⟩
  · exact ⟨0,by norm_num [slDiagonal]⟩
  · exact ⟨0,by norm_num [slDiagonal]⟩
  · exact ⟨-1,by norm_num [slDiagonal]⟩

/-- Almost every real unimodular lattice has a genuine BCZ section in its past. -/
theorem sl_quotient_has_past_section (g : SL2R) (ha : g 0 0≠0)
    (hξ : Irrational (g 0 1/g 0 0)) :
    ∃ x∈Omega,∃ T : ℝ,0≤T ∧
      (QuotientGroup.mk g : SL2R ⧸ slIntegerSubgroup)=QuotientGroup.mk (slChart ![x.1,x.2,T]) := by
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · let g' := g*slDiagonal (-1) (by norm_num)
    have h00 : g' 0 0= -g 0 0 := by
      simp [g',Matrix.SpecialLinearGroup.coe_mul,slDiagonal,Matrix.mul_apply,Fin.sum_univ_two]
    have h01 : g' 0 1= -g 0 1 := by
      simp [g',Matrix.SpecialLinearGroup.coe_mul,slDiagonal,Matrix.mul_apply,Fin.sum_univ_two]
    obtain ⟨x,hx,T,hT,hq⟩ := sl_quotient_has_past_section_pos g' (by rw [h00]; linarith)
      (by simpa [h00,h01] using hξ)
    refine ⟨x,hx,T,hT,?_⟩
    exact (QuotientGroup.mk_mul_of_mem g slMinusOne_integer_mem).symm.trans hq
  · exact sl_quotient_has_past_section_pos g hpos hξ

/-- Every nonnegative flow time is in an actual ordinary BCZ roof interval. -/
theorem bcz_roof_interval {x : ℝ × ℝ} (hx : x∈Omega) {T : ℝ} (hT : 0≤T) :
    ∃ n : ℕ,H n x≤T ∧ T<H (n+1) x := by
  have hex : ∃ k : ℕ,T<H k x := by
    obtain ⟨k,hk⟩ := exists_nat_gt T
    exact ⟨k,hk.trans_le (H_ge_nat hx k)⟩
  let k := Nat.find hex
  have hk : T<H k x := Nat.find_spec hex
  have hk0 : k≠0 := by
    intro h
    simp [h,H] at hk
    linarith
  obtain ⟨n,hkn⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  refine ⟨n,?_,by simpa [hkn] using hk⟩
  exact le_of_not_gt (Nat.find_min hex (show n<k by rw [hkn]; omega))

/-- Moving forward to the last preceding BCZ return gives a representative
in the actual suspension roof interval. -/
theorem sl_quotient_roof_representative {x : ℝ × ℝ} (hx : x∈Omega)
    {T : ℝ} (hT : 0≤T) :
    ∃ y∈Omega,∃ s : ℝ,0≤s ∧ s<tau y ∧
      (QuotientGroup.mk (slChart ![x.1,x.2,T]) : SL2R ⧸ slIntegerSubgroup)=
        QuotientGroup.mk (slChart ![y.1,y.2,s]) := by
  obtain ⟨n,hn,hn1⟩ := bcz_roof_interval hx hT
  refine ⟨B^[n] x,B_iterate_mem hx n,T-H n x,sub_nonneg.mpr hn,?_,?_⟩
  · rw [H_succ] at hn1
    linarith
  · apply quotient_eq_of_slLattice_eq
    rw [slLattice_slChart (by simpa using hx.1.ne'),
      slLattice_slChart (by simpa using (B_iterate_mem hx n).1.ne')]
    change hMap T '' Lambda x=hMap (T-H n x) '' Lambda (B^[n] x)
    rw [← hMap_H_lattice hx n,hMap_image_add]
    congr 2
    ring

lemma ae_slCoordinates_irrational : ∀ᵐ z : SL2Coordinates ∂volume,
    z 0≠0 ∧ Irrational (z 1/z 0) := by
  have hq (q : ℚ) : ∀ᵐ z : SL2Coordinates ∂volume,
      z 0*(-(q : ℝ))+z 1≠0 := by
    let g : SL2R := ⟨!![-(q : ℝ),-1;1,0],by norm_num [Matrix.det_fin_two]⟩
    filter_upwards [ae_slRightGood g] with z hz
    simpa [g] using hz.2
  filter_upwards [ae_slCoordinate_ne 0 0,ae_all_iff.mpr hq] with z hz hqz
  refine ⟨hz,?_⟩
  rintro ⟨q,hqeq⟩
  apply hqz q
  have heq : z 1=(q : ℝ)*z 0 := (div_eq_iff hz).mp hqeq.symm
  nlinarith

lemma ae_slMatrix_irrational : ∀ᵐ g : SL2R ∂slFlatMeasure,
    g 0 0≠0 ∧ Irrational (g 0 1/g 0 0) := by
  have hmeas : MeasurableSet {g : SL2R | g 0 0≠0 ∧ Irrational (g 0 1/g 0 0)} := by
    have hrat : MeasurableSet {g : SL2R | Irrational (g 0 1/g 0 0)} := by
      have heq : {g : SL2R | Irrational (g 0 1/g 0 0)}=
          ⋂ q : ℚ,{g : SL2R | g 0 1/g 0 0≠(q : ℝ)} := by
        ext g
        simp [Irrational,eq_comm]
      rw [heq]
      exact MeasurableSet.iInter fun q =>
        (measurableSet_eq_fun ((measurable_slEntry 0 1).div (measurable_slEntry 0 0))
          measurable_const).compl
    exact ((measurableSet_eq_fun (measurable_slEntry 0 0) measurable_const).compl).inter hrat
  rw [slFlatMeasure,ae_map_iff measurable_slChart.aemeasurable hmeas]
  filter_upwards [ae_slCoordinates_irrational] with z hz
  simpa [slChart,hz.1] using hz

/-- Almost every real unimodular matrix has a representative in the actual BCZ roof domain. -/
theorem ae_sl_quotient_roof_representative : ∀ᵐ g : SL2R ∂slFlatMeasure,
    ∃ x∈Omega,∃ s : ℝ,0≤s ∧ s<tau x ∧
      (QuotientGroup.mk g : SL2R ⧸ slIntegerSubgroup)=QuotientGroup.mk (slChart ![x.1,x.2,s]) := by
  filter_upwards [ae_slMatrix_irrational] with g hg
  obtain ⟨x,hx,T,hT,hq⟩ := sl_quotient_has_past_section g hg.1 hg.2
  obtain ⟨y,hy,s,hs,hsroof,hqs⟩ := sl_quotient_roof_representative hx hT
  exact ⟨y,hy,s,hs,hsroof,hq.trans hqs⟩

/-- The exact quotient identity at every ordinary return, with arbitrary remaining flow time. -/
theorem sl_quotient_return_shift {x : ℝ × ℝ} (hx : x∈Omega) (n : ℕ) (T : ℝ) :
    (QuotientGroup.mk (slChart ![x.1,x.2,T]) : SL2R ⧸ slIntegerSubgroup)=
      QuotientGroup.mk (slChart ![(B^[n] x).1,(B^[n] x).2,T-H n x]) := by
  apply quotient_eq_of_slLattice_eq
  rw [slLattice_slChart (by simpa using hx.1.ne'),
    slLattice_slChart (by simpa using (B_iterate_mem hx n).1.ne')]
  change hMap T '' Lambda x=hMap (T-H n x) '' Lambda (B^[n] x)
  rw [← hMap_H_lattice hx n,hMap_image_add]
  congr 2
  ring

end
end Paper14
