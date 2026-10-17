import Paper15.FiniteDominance
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

noncomputable section
namespace Paper15
open MeasureTheory Finset BigOperators

attribute [local instance] TriangleModel.mX TriangleModel.mY TriangleModel.mZ
  TriangleModel.isProbX TriangleModel.isProbY TriangleModel.isProbZ

lemma integrable_real_bounded {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : Measurable f) {C : ℝ} (hb : ∀x, |f x|≤C) : Integrable f μ :=
  ⟨hf.aestronglyMeasurable,HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall hb)⟩

lemma mul_mem_unit {a b : ℝ} (ha : a ∈ Set.Icc (-1:ℝ) 1) (hb : b ∈ Set.Icc (-1:ℝ) 1) :
    a*b ∈ Set.Icc (-1:ℝ) 1 := by
  apply abs_le.mp
  rw [abs_mul]
  exact (mul_le_mul (abs_le.mpr ha) (abs_le.mpr hb) (abs_nonneg _) (by norm_num)).trans_eq (by ring)

lemma momentAt_mem {a b c : ℝ} (ha : a ∈ Set.Icc (-1:ℝ) 1)
    (hb : b ∈ Set.Icc (-1:ℝ) 1) (hc : c ∈ Set.Icc (-1:ℝ) 1) (u : Fin 3) :
    momentAt a b c u ∈ Set.Icc (-1:ℝ) 1 := by
  have hab := mul_mem_unit ha hb
  have hbc := mul_mem_unit hb hc
  have hca := mul_mem_unit hc ha
  fin_cases u
  · constructor <;> simp [momentAt] <;> linarith [ha.1,ha.2,hb.1,hb.2,hc.1,hc.2]
  · constructor <;> simp [momentAt] <;> linarith [hab.1,hab.2,hbc.1,hbc.2,hca.1,hca.2]
  · exact mul_mem_unit hab hc

def momentEuclidean (a b c : ℝ) : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (momentAt a b c)

lemma momentEuclidean_bound {a b c : ℝ} (ha : a ∈ Set.Icc (-1:ℝ) 1)
    (hb : b ∈ Set.Icc (-1:ℝ) 1) (hc : c ∈ Set.Icc (-1:ℝ) 1) :
    ‖momentEuclidean a b c‖ ≤ 3 := by
  have hsq (i : Fin 3) : |momentAt a b c i|^2 ≤ 1 := by
    have hi := momentAt_mem ha hb hc i
    have h := abs_le.mpr hi
    nlinarith [abs_nonneg (momentAt a b c i)]
  have hn := EuclideanSpace.norm_sq_eq (momentEuclidean a b c)
  simp only [momentEuclidean,PiLp.toLp_apply,Real.norm_eq_abs] at hn
  have hsum : (∑ i : Fin 3, |momentAt a b c i|^2) ≤ 3 := by
    calc
      _ ≤ ∑ i : Fin 3, (1:ℝ) := sum_le_sum (fun i _ => hsq i)
      _ = 3 := by simp
  have he : (∑ i : Fin 3, |momentAt a b c i|^2) = ‖momentEuclidean a b c‖^2 := hn.symm
  nlinarith [norm_nonneg (momentEuclidean a b c)]

namespace TriangleModel
variable (M : TriangleModel)
lemma condA_mem (y : M.Y) (z : M.Z) : M.condA y z ∈ Set.Icc (-1:ℝ) 1 := by
  have h:=M.pA_mem y z
  constructor <;> dsimp [condA] <;> linarith [h.1,h.2]
lemma condB_mem (z : M.Z) (x : M.X) : M.condB z x ∈ Set.Icc (-1:ℝ) 1 := by
  have h:=M.pB_mem z x
  constructor <;> dsimp [condB] <;> linarith [h.1,h.2]
lemma condC_mem (x : M.X) (y : M.Y) : M.condC x y ∈ Set.Icc (-1:ℝ) 1 := by
  have h:=M.pC_mem x y
  constructor <;> dsimp [condC] <;> linarith [h.1,h.2]
lemma condA_measurable : Measurable (Function.uncurry M.condA) :=
  (measurable_const.mul M.pA_measurable).sub measurable_const
lemma condB_measurable : Measurable (Function.uncurry M.condB) :=
  (measurable_const.mul M.pB_measurable).sub measurable_const
lemma condC_measurable : Measurable (Function.uncurry M.condC) :=
  (measurable_const.mul M.pC_measurable).sub measurable_const

def expect (f : M.X → M.Y → M.Z → ℝ) : ℝ := ∫x,∫y,∫z,f x y z ∂M.μZ ∂M.μY ∂M.μX

lemma eA_expect : M.eA = M.expect (fun _ y z => M.condA y z) := by
  simp [eA,expect]
lemma eB_expect : M.eB = M.expect (fun x _ z => M.condB z x) := by
  simp only [eB,expect,integral_const,measureReal_univ_eq_one,one_smul]
  exact integral_integral_swap (integrable_real_bounded M.condB_measurable
    (fun p => abs_le.mpr (M.condB_mem p.1 p.2)))
lemma eC_expect : M.eC = M.expect (fun x y _ => M.condC x y) := by
  simp [eC,expect]

def pointMoment (x : M.X) (y : M.Y) (z : M.Z) : EuclideanSpace ℝ (Fin 3) :=
  momentEuclidean (M.condA y z) (M.condB z x) (M.condC x y)

lemma pointMoment_measurable : Measurable (fun p : M.X × (M.Y × M.Z) => M.pointMoment p.1 p.2.1 p.2.2) := by
  change Measurable (fun p : M.X × (M.Y × M.Z) =>
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
      (momentAt (M.condA p.2.1 p.2.2) (M.condB p.2.2 p.1) (M.condC p.1 p.2.1)))
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.continuous.measurable.comp
  apply measurable_pi_lambda
  intro u
  have ha : Measurable (fun p : M.X × (M.Y × M.Z) => M.condA p.2.1 p.2.2) := M.condA_measurable.comp (measurable_snd.fst.prodMk measurable_snd.snd)
  have hb : Measurable (fun p : M.X × (M.Y × M.Z) => M.condB p.2.2 p.1) := M.condB_measurable.comp (measurable_snd.snd.prodMk measurable_fst)
  have hc : Measurable (fun p : M.X × (M.Y × M.Z) => M.condC p.1 p.2.1) := M.condC_measurable.comp (measurable_fst.prodMk measurable_snd.fst)
  dsimp [pointMoment,momentEuclidean,momentAt]
  split_ifs <;> fun_prop

lemma pointMoment_bound (x : M.X) (y : M.Y) (z : M.Z) : ‖M.pointMoment x y z‖ ≤ 3 :=
  momentEuclidean_bound (M.condA_mem _ _) (M.condB_mem _ _) (M.condC_mem _ _)

/-- The regularity needed to apply Fubini and linearity of expectation. -/
def Good (f : M.X → M.Y → M.Z → ℝ) : Prop :=
  Measurable (fun p : M.X × (M.Y × M.Z) => f p.1 p.2.1 p.2.2) ∧
    ∃ C : ℝ, ∀x y z, |f x y z| ≤ C

lemma goodA : M.Good (fun _ y z => M.condA y z) :=
  ⟨M.condA_measurable.comp measurable_snd,1,fun _ y z => abs_le.mpr (M.condA_mem y z)⟩
lemma goodB : M.Good (fun x _ z => M.condB z x) :=
  ⟨M.condB_measurable.comp (measurable_snd.snd.prodMk measurable_fst),
    1,fun x _ z => abs_le.mpr (M.condB_mem z x)⟩
lemma goodC : M.Good (fun x y _ => M.condC x y) :=
  ⟨M.condC_measurable.comp (measurable_fst.prodMk measurable_snd.fst),
    1,fun x y _ => abs_le.mpr (M.condC_mem x y)⟩
variable {M : TriangleModel}
lemma Good.const (c : ℝ) : M.Good (fun _ _ _ => c) := ⟨measurable_const,|c|,fun _ _ _ => le_rfl⟩
lemma Good.add {f g : M.X → M.Y → M.Z → ℝ} (hf : M.Good f) (hg : M.Good g) :
    M.Good (fun x y z => f x y z + g x y z) := by
  obtain ⟨C,hC⟩:=hf.2
  obtain ⟨D,hD⟩:=hg.2
  exact ⟨hf.1.add hg.1,C+D,fun x y z => (abs_add_le _ _).trans (add_le_add (hC x y z) (hD x y z))⟩
lemma Good.mul {f g : M.X → M.Y → M.Z → ℝ} (hf : M.Good f) (hg : M.Good g) :
    M.Good (fun x y z => f x y z * g x y z) := by
  obtain ⟨C,hC⟩:=hf.2
  obtain ⟨D,hD⟩:=hg.2
  refine ⟨hf.1.mul hg.1,(max C 0)*(max D 0),fun x y z => ?_⟩
  rw [abs_mul]
  exact mul_le_mul ((hC x y z).trans (le_max_left _ _))
    ((hD x y z).trans (le_max_left _ _)) (abs_nonneg _) (le_max_right _ _)

lemma Good.integrable {f : M.X → M.Y → M.Z → ℝ} (hf : M.Good f) :
    Integrable (fun p : M.X × (M.Y × M.Z) => f p.1 p.2.1 p.2.2) (M.μX.prod (M.μY.prod M.μZ)) := by
  obtain ⟨C,hC⟩:=hf.2
  exact integrable_real_bounded hf.1 (fun p => hC p.1 p.2.1 p.2.2)

variable (M : TriangleModel)
lemma expect_eq_integral {f : M.X → M.Y → M.Z → ℝ} (hf : M.Good f) :
    M.expect f = ∫p : M.X × (M.Y × M.Z), f p.1 p.2.1 p.2.2 ∂(M.μX.prod (M.μY.prod M.μZ)) := by
  rw [integral_prod _ hf.integrable]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [integral_prod]
  obtain ⟨C,hC⟩:=hf.2
  exact integrable_real_bounded (hf.1.comp (measurable_const.prodMk measurable_id))
    (fun p => hC x p.1 p.2)

lemma expect_add {f g : M.X → M.Y → M.Z → ℝ} (hf : M.Good f) (hg : M.Good g) :
    M.expect (fun x y z => f x y z + g x y z) = M.expect f + M.expect g := by
  rw [M.expect_eq_integral (hf.add hg),M.expect_eq_integral hf,M.expect_eq_integral hg,
    integral_add hf.integrable hg.integrable]
lemma expect_mul (c : ℝ) {f : M.X → M.Y → M.Z → ℝ} (hf : M.Good f) :
    M.expect (fun x y z => c*f x y z) = c*M.expect f := by
  rw [M.expect_eq_integral ((Good.const (M:=M) c).mul hf),M.expect_eq_integral hf,integral_const_mul]
lemma expect_const (c : ℝ) : M.expect (fun _ _ _ => c)=c := by simp [expect]

lemma aggregate_vec_expect (u : Fin 3) :
    M.aggregate.vec u = M.expect (fun x y z => momentAt (M.condA y z) (M.condB z x) (M.condC x y) u) := by
  fin_cases u
  · change (M.eA+M.eB+M.eC)/3 = M.expect (fun x y z => (M.condA y z+M.condB z x+M.condC x y)/3)
    have he : (fun x y z => (M.condA y z+M.condB z x+M.condC x y)/3) =
        (fun x y z => (1/3:ℝ)*(M.condA y z+M.condB z x+M.condC x y)) := by funext x y z; ring
    rw [he,M.expect_mul _ ((M.goodA.add M.goodB).add M.goodC),
      M.expect_add (M.goodA.add M.goodB) M.goodC,M.expect_add M.goodA M.goodB,
      ← M.eA_expect,← M.eB_expect,← M.eC_expect]
    ring
  · change (M.eAB+M.eBC+M.eCA)/3 = M.expect (fun x y z =>
      (M.condA y z*M.condB z x+M.condB z x*M.condC x y+M.condC x y*M.condA y z)/3)
    have he : (fun x y z => (M.condA y z*M.condB z x+M.condB z x*M.condC x y+M.condC x y*M.condA y z)/3) =
        (fun x y z => (1/3:ℝ)*(M.condA y z*M.condB z x+M.condB z x*M.condC x y+M.condC x y*M.condA y z)) := by funext x y z; ring
    rw [he,M.expect_mul _ (((M.goodA.mul M.goodB).add (M.goodB.mul M.goodC)).add (M.goodC.mul M.goodA)),
      M.expect_add ((M.goodA.mul M.goodB).add (M.goodB.mul M.goodC)) (M.goodC.mul M.goodA),
      M.expect_add (M.goodA.mul M.goodB) (M.goodB.mul M.goodC)]
    change (M.eAB+M.eBC+M.eCA)/3 = (1/3:ℝ)*(M.eAB+M.eBC+M.eCA)
    ring
  · rfl

end TriangleModel
end Paper15
