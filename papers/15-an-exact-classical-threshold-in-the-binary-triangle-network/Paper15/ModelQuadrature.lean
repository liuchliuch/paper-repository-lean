import Paper15.ModelIntegration

noncomputable section
namespace Paper15
open MeasureTheory Finset BigOperators
attribute [local instance] TriangleModel.mX TriangleModel.mY TriangleModel.mZ
  TriangleModel.isProbX TriangleModel.isProbY TriangleModel.isProbZ

lemma triple_integral_eval
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {μ : Measure α} {ν : Measure β} {ρ : Measure γ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    {d : Nat} (f : α → β → γ → EuclideanSpace ℝ (Fin d))
    (hf : Measurable (fun p : α × (β × γ) => f p.1 p.2.1 p.2.2))
    {C : ℝ} (hC : ∀ x y z, ‖f x y z‖ ≤ C) (u : Fin d) :
    (∫x,∫y,∫z,f x y z ∂ρ ∂ν ∂μ) u = ∫x,∫y,∫z,(f x y z) u ∂ρ ∂ν ∂μ := by
  have hm : Measurable (fun p : (α × β) × γ => f p.1.1 p.1.2 p.2) :=
    hf.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  have hi : Measurable (fun p : α × β => ∫z,f p.1 p.2 z ∂ρ) := integral_right_measurable hm
  have hx : Integrable (fun x => ∫y,∫z,f x y z ∂ρ ∂ν) μ :=
    integral_right_integrable hi (fun p => norm_integral_prob_le (hC p.1 p.2))
  rw [eval_integral_piLp (fun i => hx.eval_piLp i)]
  apply integral_congr_ae
  filter_upwards [] with x
  have hy : Integrable (fun y => ∫z,f x y z ∂ρ) ν :=
    integral_right_integrable (hf.comp (measurable_const.prodMk measurable_id))
      (fun p => hC x p.1 p.2)
  rw [eval_integral_piLp (fun i => hy.eval_piLp i)]
  apply integral_congr_ae
  filter_upwards [] with y
  have hz : Integrable (fun z => f x y z) ρ := integrable_bounded_measurable
    (hf.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))) (hC x y)
  exact eval_integral_piLp (fun i => hz.eval_piLp i) u

lemma Quad.avg_eval {α : Type*} (q : Quad α) (f : α → EuclideanSpace ℝ (Fin 3)) (u : Fin 3) :
    (q.avg f) u = ∑i,q.weight i*(f (q.point i)) u := by
  unfold Quad.avg
  let l : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) u
  change l (∑i,q.weight i • f (q.point i)) = _
  rw [map_sum]
  simp only [map_smul,PiLp.proj_apply,smul_eq_mul,l]

namespace TriangleModel
/-- Every measurable classical model is dominated by a finite ternary
 deterministic model, preserving the two constrained moments exactly. -/
theorem exists_ternary_dominating (M : TriangleModel) :
    ∃ (T : DetTriangle) (qx qy qz : Simplex2),
      (detMoments' T qx qy qz).M1 = M.aggregate.M1 ∧
      (detMoments' T qx qy qz).M3 = M.aggregate.M3 ∧
      M.aggregate.M2 ≤ (detMoments' T qx qy qz).M2 := by
  classical
  obtain ⟨qx,qy,qz,_,_,_,hq⟩ := triple_integral_quadrature (μ:=M.μX) (ν:=M.μY) (ρ:=M.μZ) M.pointMoment M.pointMoment_measurable ⟨3,M.pointMoment_bound⟩
  let F : FiniteResponse (Fin qx.n) (Fin qy.n) (Fin qz.n) := {
    A := fun j k => M.condA (qy.point j) (qz.point k)
    B := fun k i => M.condB (qz.point k) (qx.point i)
    C := fun i j => M.condC (qx.point i) (qy.point j)
    A_mem := fun _ _ => M.condA_mem _ _
    B_mem := fun _ _ => M.condB_mem _ _
    C_mem := fun _ _ => M.condC_mem _ _
  }
  let rx : Law (Fin qx.n) := ⟨qx.weight,qx.nonneg,qx.sum_eq⟩
  let ry : Law (Fin qy.n) := ⟨qy.weight,qy.nonneg,qy.sum_eq⟩
  let rz : Law (Fin qz.n) := ⟨qz.weight,qz.nonneg,qz.sum_eq⟩
  have hF (u : Fin 3) : F.moments rx ry rz u = M.aggregate.vec u := by
    calc
      _ = (qx.avg (fun x => qy.avg (fun y => qz.avg (fun z => M.pointMoment x y z)))) u := by
        simp only [Quad.avg_eval]
        rfl
      _ = (∫x,∫y,∫z,M.pointMoment x y z ∂M.μZ ∂M.μY ∂M.μX) u := congrArg (fun v => v u) hq
      _ = M.expect (fun x y z => momentAt (M.condA y z) (M.condB z x) (M.condC x y) u) :=
        triple_integral_eval M.pointMoment M.pointMoment_measurable M.pointMoment_bound u
      _ = _ := (M.aggregate_vec_expect u).symm
  let sa := FiniteResponse.seedLaw (Function.uncurry F.A) (fun p => F.A_mem p.1 p.2)
  let sb := FiniteResponse.seedLaw (Function.uncurry F.B) (fun p => F.B_mem p.1 p.2)
  let sc := FiniteResponse.seedLaw (Function.uncurry F.C) (fun p => F.C_mem p.1 p.2)
  obtain ⟨T,sx,sy,sz,h0,h2,h1⟩ := F.deterministicLift.exists_ternary_dominating F.deterministicLift_legal
    (rx.prod sb) (ry.prod sc) (rz.prod sa)
  have hl := F.deterministicLift_moments rx ry rz
  refine ⟨T,sx,sy,sz,?_,?_,?_⟩
  · exact h0.trans ((hl 0).trans (hF 0))
  · exact h2.trans ((hl 2).trans (hF 2))
  · exact ((hl 1).trans (hF 1)).symm.le.trans h1
end TriangleModel
end Paper15
