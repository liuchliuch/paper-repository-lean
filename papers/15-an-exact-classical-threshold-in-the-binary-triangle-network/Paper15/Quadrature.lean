import Paper15.IntegralConvex
import Mathlib.MeasureTheory.Integral.Prod

/-! # Exact finite quadrature for three independent sources

Sequential application of the full barycentre lemma preserves the entire
vector of chosen moments. Each source uses at most d+1 original values.
-/
noncomputable section
namespace Paper15
open Finset BigOperators MeasureTheory

structure Quad (α : Type*) where
  n : Nat
  point : Fin n → α
  weight : Fin n → ℝ
  nonneg : ∀ i, 0 ≤ weight i
  sum_eq : ∑ i, weight i = 1

def Quad.avg {α E : Type*} [AddCommMonoid E] [Module ℝ E] (q : Quad α) (f : α → E) : E :=
  ∑ i, q.weight i • f (q.point i)

lemma Quad.avg_comm {α β E : Type*} [AddCommMonoid E] [Module ℝ E]
    (q : Quad α) (r : Quad β) (f : α → β → E) :
    q.avg (fun x => r.avg (f x)) = r.avg (fun y => q.avg (fun x => f x y)) := by
  simp only [Quad.avg, smul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  exact smul_comm _ _ _

lemma Quad.integrable_avg {α β E : Type*} [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure β}
    (q : Quad α) (f : α → β → E) (hf : ∀ x, Integrable (f x) μ) :
    Integrable (fun y => q.avg (fun x => f x y)) μ :=
  integrable_finset_sum _ (fun i _ => (hf _).smul (q.weight i))

lemma Quad.integral_avg {α β E : Type*} [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {μ : Measure β}
    (q : Quad α) (f : α → β → E) (hf : ∀ x, Integrable (f x) μ) :
    (∫ y, q.avg (fun x => f x y) ∂μ) = q.avg (fun x => ∫ y, f x y ∂μ) := by
  change (∫ y, ∑ i, q.weight i • f (q.point i) y ∂μ) =
    ∑ i, q.weight i • ∫ y, f (q.point i) y ∂μ
  have hi (i : Fin q.n) (_ : i ∈ (Finset.univ : Finset (Fin q.n))) :
      Integrable (fun y => q.weight i • f (q.point i) y) μ := (hf _).smul _
  rw [integral_finset_sum Finset.univ hi]
  simp only [integral_smul]

lemma exists_quad {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {d : Nat} (f : α → EuclideanSpace ℝ (Fin d)) (hf : Integrable f μ) :
    ∃ q : Quad α, q.n ≤ d+1 ∧ q.avg f = ∫ x, f x ∂μ := by
  obtain ⟨n, hn, pts, w, _, h0, h1, heq⟩ :=
    lemma3_integrable_fullMeasure hf Set.univ (Filter.Eventually.of_forall (fun _ => Set.mem_univ _))
  exact ⟨⟨n,pts,w,h0,h1⟩,hn,heq⟩

lemma norm_integral_prob_le {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → E} {C : ℝ} (h : ∀ x, ‖f x‖ ≤ C) : ‖∫ x, f x ∂μ‖ ≤ C := by
  simpa using norm_integral_le_of_norm_le_const (μ := μ) (f := f) (Filter.Eventually.of_forall h)

lemma integrable_bounded_measurable {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {d : Nat}
    {f : α → EuclideanSpace ℝ (Fin d)} (hf : Measurable f)
    {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) : Integrable f μ :=
  ⟨hf.aestronglyMeasurable, HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall hC)⟩

lemma integral_right_measurable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {ν : Measure β} [SFinite ν] {d : Nat}
    {f : α × β → EuclideanSpace ℝ (Fin d)} (hf : Measurable f) :
    Measurable (fun x => ∫ y, f (x,y) ∂ν) :=
  hf.stronglyMeasurable.integral_prod_right'.measurable

lemma integral_right_integrable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {d : Nat} {f : α × β → EuclideanSpace ℝ (Fin d)} (hf : Measurable f)
    {C : ℝ} (hC : ∀ p, ‖f p‖ ≤ C) : Integrable (fun x => ∫ y, f (x,y) ∂ν) μ :=
  integrable_bounded_measurable (integral_right_measurable hf)
    (fun x => norm_integral_prob_le (fun y => hC (x,y)))

/-- Exact three-source quadrature, with no finiteness assumption on any of
the original measurable probability spaces. -/
theorem triple_integral_quadrature
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {μ : Measure α} {ν : Measure β} {ρ : Measure γ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    {d : Nat} (f : α → β → γ → EuclideanSpace ℝ (Fin d))
    (hf : Measurable (fun p : α × (β × γ) => f p.1 p.2.1 p.2.2))
    (hbounded : ∃ C : ℝ, ∀ x y z, ‖f x y z‖ ≤ C) :
    ∃ (qx : Quad α) (qy : Quad β) (qz : Quad γ),
      qx.n ≤ d+1 ∧ qy.n ≤ d+1 ∧ qz.n ≤ d+1 ∧
      qx.avg (fun x => qy.avg (fun y => qz.avg (fun z => f x y z))) =
        ∫ x, ∫ y, ∫ z, f x y z ∂ρ ∂ν ∂μ := by
  obtain ⟨C,hC⟩ := hbounded
  have hmeas : Measurable (fun p : (α × β) × γ => f p.1.1 p.1.2 p.2) :=
    hf.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  have hinner : Measurable (fun p : α × β => ∫ z, f p.1 p.2 z ∂ρ) :=
    integral_right_measurable hmeas
  have hgx : Integrable (fun x => ∫ y, ∫ z, f x y z ∂ρ ∂ν) μ :=
    integral_right_integrable hinner (fun p => norm_integral_prob_le (hC p.1 p.2))
  obtain ⟨qx,hxn,hx⟩ := exists_quad _ hgx
  have hiy (x : α) : Integrable (fun y => ∫ z, f x y z ∂ρ) ν :=
    integral_right_integrable (hf.comp (measurable_const.prodMk measurable_id))
      (fun p => hC x p.1 p.2)
  let gy := fun y => qx.avg (fun x => ∫ z, f x y z ∂ρ)
  have hgy : Integrable gy ν := qx.integrable_avg _ hiy
  obtain ⟨qy,hyn,hy⟩ := exists_quad gy hgy
  have hiz (x : α) (y : β) : Integrable (fun z => f x y z) ρ :=
    integrable_bounded_measurable
      (hf.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))) (hC x y)
  let gz := fun z => qx.avg (fun x => qy.avg (fun y => f x y z))
  have hgz : Integrable gz ρ := qx.integrable_avg _ (fun x => qy.integrable_avg _ (hiz x))
  obtain ⟨qz,hzn,hz⟩ := exists_quad gz hgz
  refine ⟨qx,qy,qz,hxn,hyn,hzn,?_⟩
  calc
    _ = qz.avg gz := by
      simp_rw [Quad.avg_comm qy qz]
      exact Quad.avg_comm qx qz _
    _ = ∫ z, gz z ∂ρ := hz
    _ = qx.avg (fun x => qy.avg (fun y => ∫ z, f x y z ∂ρ)) := by
      rw [show gz = fun z => qx.avg (fun x => qy.avg (fun y => f x y z)) from rfl]
      rw [Quad.integral_avg qx _ (fun x => qy.integrable_avg _ (hiz x))]
      congr 1
      funext x
      exact Quad.integral_avg qy _ (hiz x)
    _ = qy.avg gy := Quad.avg_comm qx qy _
    _ = ∫ y, gy y ∂ν := hy
    _ = qx.avg (fun x => ∫ y, ∫ z, f x y z ∂ρ ∂ν) := Quad.integral_avg qx _ hiy
    _ = _ := hx

end Paper15
