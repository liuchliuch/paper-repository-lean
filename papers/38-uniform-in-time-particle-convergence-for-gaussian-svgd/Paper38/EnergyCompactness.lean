import Paper38.EnergyDecay
import Paper38.HilbertCoordinates
import Paper38.GaussianEnergy
import Paper38.GradientGeometry
import Paper38.PotentialLowerBound

/-! Compact energy sublevels from strong convexity and the actual determinant barrier. -/

noncomputable section

namespace Paper38.EnergyCompactness

open Set Real MeasureTheory
open scoped InnerProductSpace NNReal Topology

section General
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A differentiable strongly convex energy has bounded sublevels on its domain,
even before a minimizer has been constructed. The anchor is arbitrary. -/
theorem strongConvex_sublevel_bounded {F : E → ℝ} {G : E → E} {Ω : Set E} {α : ℝ}
    (hα : 0 < α) (hstrong : EnergyDecay.StrongConvexGradientOn F G Ω α)
    {a : E} (ha : a ∈ Ω) (c : ℝ) : Bornology.IsBounded {x | x ∈ Ω ∧ F x ≤ c} := by
  let g := ‖G a‖
  let gap := c-F a
  let B := (4*α*|gap|+4*g^2)/α^2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  apply (Metric.isBounded_closedBall (x := a) (r := B+1)).subset
  intro x hx
  have h := hstrong a ha x hx.1
  have hcs := (abs_le.mp (abs_real_inner_le_norm (G a) (x-a))).1
  have hgap : α/2 * ‖x-a‖^2 - g*‖x-a‖ ≤ gap := by
    dsimp [g, gap]
    linarith [hx.2]
  have hmul := mul_le_mul_of_nonneg_left hgap hα.le
  have habs := mul_le_mul_of_nonneg_left (le_abs_self gap) hα.le
  have hsq : ‖x-a‖^2 ≤ B := by
    apply (le_div_iff₀ (sq_pos_of_pos hα)).mpr
    dsimp [B]
    nlinarith [sq_nonneg (α*‖x-a‖-2*g)]
  have hnorm : ‖x-a‖ ≤ B+1 := by nlinarith [sq_nonneg (‖x-a‖-1)]
  simpa only [Metric.mem_closedBall, dist_eq_norm] using hnorm

/-- A continuous barrier excludes domain-boundary limits of bounded sublevels;
Heine--Borel then gives actual compactness in the ambient finite-dimensional space. -/
theorem isCompact_sublevel_of_barrier [FiniteDimensional ℝ E]
    {F : E → ℝ} {G : E → E} {Ω : Set E} {α : ℝ}
    (hα : 0 < α) (hstrong : EnergyDecay.StrongConvexGradientOn F G Ω α)
    {a : E} (ha : a ∈ Ω) (hΩ : IsOpen Ω) (hF : ContinuousOn F Ω)
    (barrier : E → ℝ) (hbarrier : Continuous barrier) (c δ : ℝ)
    (hδ : 0 < δ)
    (hbound : ∀ x ∈ Ω, F x ≤ c → δ ≤ barrier x)
    (hboundary : ∀ x ∈ closure Ω, barrier x ≠ 0 → x ∈ Ω) :
    IsCompact {x | x ∈ Ω ∧ F x ≤ c} := by
  have hbounded := strongConvex_sublevel_bounded hα hstrong ha c
  apply Metric.isCompact_of_isClosed_isBounded _ hbounded
  apply isClosed_of_closure_subset
  intro x hx
  have hxcl : x ∈ closure Ω := closure_mono (fun _ hy => hy.1) hx
  have hxbarrier : δ ≤ barrier x :=
    ContinuousWithinAt.closure_le hx continuousWithinAt_const
      hbarrier.continuousAt.continuousWithinAt (fun y hy => hbound y hy.1 hy.2)
  have hxΩ : x ∈ Ω := hboundary x hxcl (ne_of_gt (hδ.trans_le hxbarrier))
  refine ⟨hxΩ, ?_⟩
  exact ContinuousWithinAt.closure_le hx
    ((hF x hxΩ).continuousAt (hΩ.mem_nhds hxΩ)).continuousWithinAt
    continuousWithinAt_const (fun y hy => hy.2)

end General

open Paper38.Model

local instance standardGaussian_probability (d : ℕ) : IsProbabilityMeasure (standardGaussian d) := by
  unfold standardGaussian
  exact Measure.isProbabilityMeasure_map
    (Paper38.GaussianCoupling.continuous_vec (d := d)).measurable.aemeasurable

/-- An actual quadratic upper envelope for the initialized Gaussian energy,
obtained by integrating the source potential growth bound. -/
theorem gaussian_energy_upper {d : ℕ} {V : Model.E d → ℝ} {α β : ℝ}
    (hV : AdmissiblePotential V α β) (q : Coordinates d) :
    Model.energy V q ≤ (|V 0|+‖fderiv ℝ V 0‖+2*β) *
      (1+‖q.1‖^2+frobSq q.2) - log q.2.det := by
  let C := |V 0|+‖fderiv ℝ V 0‖+2*β
  have hint := GaussianEnergy.affine_norm_sq_integrable q.1 q.2
  have havg : (∫ z, V (q.1+matVec q.2 z) ∂standardGaussian d) ≤
      ∫ z, C * (1+‖q.1+matVec q.2 z‖^2) ∂standardGaussian d := by
    apply integral_mono (GaussianEnergy.potential_integrable hV q.1 q.2)
      (((integrable_const 1).add hint).const_mul C)
    intro z
    exact (le_abs_self _).trans (PotentialBounds.potential_quadratic_growth hV _)
  have hformula : (∫ z, C * (1+‖q.1+matVec q.2 z‖^2) ∂standardGaussian d) =
      C * (1+‖q.1‖^2+frobSq q.2) := by
    rw [integral_const_mul, integral_add (integrable_const 1) hint,
      GaussianEnergy.affine_norm_sq_integral]
    simp [integral_const, add_assoc]
  rw [hformula] at havg
  unfold Model.energy
  dsimp [C] at havg
  linarith

/-- A genuine lower bound on V produces the strict determinant barrier on every
actual Gaussian energy sublevel; this is what prevents approach to the SPD boundary. -/
theorem gaussian_energy_determinant_barrier {d : ℕ} {V : Model.E d → ℝ} {α β vmin c : ℝ}
    (hV : AdmissiblePotential V α β) (hmin : ∀ x, vmin ≤ V x)
    {q : Coordinates d} (hq : q ∈ domain d) (hc : Model.energy V q ≤ c) :
    exp (vmin-c) ≤ q.2.det := by
  have hpotential : vmin ≤ ∫ z, V (q.1 + matVec q.2 z) ∂standardGaussian d := by
    have h := integral_mono (integrable_const vmin)
      (GaussianEnergy.potential_integrable hV q.1 q.2)
      (fun z => hmin (q.1 + matVec q.2 z))
    simpa using h
  have hlog : vmin-c ≤ log q.2.det := by
    unfold Model.energy at hc
    linarith
  have hpos : 0 < q.2.det := hq.det_pos
  calc
    exp (vmin-c) ≤ exp (log q.2.det) := exp_le_exp.mpr hlog
    _ = q.2.det := exp_log hpos

/-- Actual Gaussian energy sublevels are compact in the intrinsic symmetric
Hilbert space once its standard first-order strong convexity is established.
The determinant barrier is derived from the literal Gaussian integral above. -/
theorem gaussian_energy_sublevel_isCompact {d : ℕ} {V : Model.E d → ℝ} {α β vmin c : ℝ}
    (hV : AdmissiblePotential V α β) (hmin : ∀ x, vmin ≤ V x)
    (hcontinuous : ContinuousOn (HilbertCoordinates.energy V) (HilbertCoordinates.Domain d))
    (hstrong : EnergyDecay.StrongConvexGradientOn (HilbertCoordinates.energy V)
      (gradient (HilbertCoordinates.energy V)) (HilbertCoordinates.Domain d) α) :
    IsCompact {q : HilbertCoordinates.Tangent d |
      q ∈ HilbertCoordinates.Domain d ∧ HilbertCoordinates.energy V q ≤ c} := by
  apply isCompact_sublevel_of_barrier hV.alpha_pos hstrong
    (HilbertCoordinates.anchor_mem_Domain d) (HilbertCoordinates.Domain_isOpen d) hcontinuous
    (fun q => (HilbertCoordinates.toModel d q).2.det)
    ((HilbertCoordinates.toModel d).continuous.snd.matrix_det) c
    (exp (vmin-c)) (exp_pos _) _ _
  · intro q hq hc
    exact gaussian_energy_determinant_barrier hV hmin hq hc
  · intro q hq hdet
    exact HilbertCoordinates.Domain_closure_det_ne_zero hq hdet

/-- Derivatives and the actual quadratic Hessian lower bound suffice for compact
actual Gaussian energy sublevels; no minimizer or coercivity conclusion is assumed. -/
theorem gaussian_energy_sublevel_isCompact_of_C2 {d : ℕ} {V : Model.E d → ℝ} {α β vmin : ℝ}
    (hV : AdmissiblePotential V α β) (hmin : ∀ x, vmin ≤ V x)
    (hC2 : ContDiffOn ℝ 2 (HilbertCoordinates.energy V) (HilbertCoordinates.Domain d))
    (hH : ∀ q ∈ HilbertCoordinates.Domain d, ∀ v : HilbertCoordinates.Tangent d,
      α * ‖v‖^2 ≤ (fderiv ℝ (fderiv ℝ (HilbertCoordinates.energy V)) q v) v)
    (c : ℝ) : IsCompact {q : HilbertCoordinates.Tangent d |
      q ∈ HilbertCoordinates.Domain d ∧ HilbertCoordinates.energy V q ≤ c} := by
  exact gaussian_energy_sublevel_isCompact hV hmin hC2.continuousOn
    (GradientGeometry.strongConvexGradientOn_of_second_fderiv_lower
      (HilbertCoordinates.Domain_isOpen d) (HilbertCoordinates.Domain_convex d) hC2 hH)

/-- The global lower potential bound used above follows from the original
admissible-potential hypotheses, so only the actual C²/Hessian identities remain
as geometry inputs in this specialization. -/
theorem gaussian_energy_sublevel_compact_from_geometry {d : ℕ} {V : Model.E d → ℝ} {α β : ℝ}
    (hV : AdmissiblePotential V α β)
    (hC2 : ContDiffOn ℝ 2 (HilbertCoordinates.energy V) (HilbertCoordinates.Domain d))
    (hH : ∀ q ∈ HilbertCoordinates.Domain d, ∀ v : HilbertCoordinates.Tangent d,
      α * ‖v‖^2 ≤ (fderiv ℝ (fderiv ℝ (HilbertCoordinates.energy V)) q v) v)
    (c : ℝ) : IsCompact {q : HilbertCoordinates.Tangent d |
      q ∈ HilbertCoordinates.Domain d ∧ HilbertCoordinates.energy V q ≤ c} :=
  gaussian_energy_sublevel_isCompact_of_C2 hV
    (PotentialLowerBound.potential_global_lower hV) hC2 hH c

end Paper38.EnergyCompactness
