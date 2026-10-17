import Paper35.SourceModel
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

noncomputable section
open Set MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace Paper35.Source.CrossingJacobian

variable {d : ℕ}

/-- The actual common-height to bias-pair map in the visible crossing identity. -/
def phi (p : Probe d) (wi wj : Space d) (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.2 - inner ℝ wi (p.curve z.1), z.2 - inner ℝ wj (p.curve z.1))

def strip (p : Probe d) : Set (ℝ × ℝ) := Icc 0 p.length ×ˢ univ

def phiLip (wi wj : Space d) : ℝ≥0 :=
  max (1 + ‖innerSL ℝ wi‖₊) (1 + ‖innerSL ℝ wj‖₊)

/-- The common-height map is Lipschitz on the entire strip, with no bound on height. -/
theorem phi_lipschitzOn (p : Probe d) (wi wj : Space d) :
    LipschitzOnWith (phiLip wi wj) (phi p wi wj) (strip p) := by
  have hfst : LipschitzOnWith 1 (Prod.fst : ℝ × ℝ → ℝ) (strip p) :=
    LipschitzWith.prod_fst.lipschitzOnWith
  have hsnd : LipschitzOnWith 1 (Prod.snd : ℝ × ℝ → ℝ) (strip p) :=
    LipschitzWith.prod_snd.lipschitzOnWith
  have hc : LipschitzOnWith 1 (fun z : ℝ × ℝ => p.curve z.1) (strip p) := by
    simpa only [Function.comp_def, one_mul] using
      p.lipschitz.comp hfst (fun z hz => hz.1)
  have hi := (innerSL ℝ wi).lipschitz.comp_lipschitzOnWith hc
  have hj := (innerSL ℝ wj).lipschitz.comp_lipschitzOnWith hc
  simpa only [Function.comp_def, mul_one, phiLip, phi] using
    (hsnd.sub hi).prodMk (hsnd.sub hj)

/-- The actual derivative matrix, represented as a continuous linear map. -/
def phiDeriv (ai aj : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  ((ContinuousLinearMap.snd ℝ ℝ ℝ) - ai • (ContinuousLinearMap.fst ℝ ℝ ℝ)).prod
    ((ContinuousLinearMap.snd ℝ ℝ ℝ) - aj • (ContinuousLinearMap.fst ℝ ℝ ℝ))

@[simp] theorem phiDeriv_apply (ai aj : ℝ) (z : ℝ × ℝ) :
    phiDeriv ai aj z = (z.2 - ai * z.1, z.2 - aj * z.1) := by
  rfl

/-- A derivative of the original probe gives the actual two-dimensional derivative. -/
theorem hasFDerivAt_phi (p : Probe d) (wi wj u : Space d) (z : ℝ × ℝ)
    (hu : HasDerivAt p.curve u z.1) :
    HasFDerivAt (phi p wi wj)
      (phiDeriv (inner ℝ wi u) (inner ℝ wj u)) z := by
  have hi : HasDerivAt (fun s => inner ℝ wi (p.curve s)) (inner ℝ wi u) z.1 := by
    simpa only [inner_zero_left, add_zero] using (hasDerivAt_const z.1 wi).inner ℝ hu
  have hj : HasDerivAt (fun s => inner ℝ wj (p.curve s)) (inner ℝ wj u) z.1 := by
    simpa only [inner_zero_left, add_zero] using (hasDerivAt_const z.1 wj).inner ℝ hu
  convert (hasFDerivAt_snd.sub (hi.hasFDerivAt.comp z hasFDerivAt_fst)).prodMk
    (hasFDerivAt_snd.sub (hj.hasFDerivAt.comp z hasFDerivAt_fst)) using 1
  ext <;> simp [phiDeriv, ContinuousLinearMap.smulRight_apply, smul_eq_mul]

/-- The determinant is the difference of the two directional slopes. -/
theorem phiDeriv_det (ai aj : ℝ) : (phiDeriv ai aj).det = aj - ai := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ)]
  rw [Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Module.Basis.coe_finTwoProd_repr, phiDeriv_apply]
  ring

/-- Absolute Jacobian of the actual map, equal to the source crossing kernel factor. -/
theorem phiDeriv_abs_det (wi wj u : Space d) :
    |(phiDeriv (inner ℝ wi u) (inner ℝ wj u)).det| =
      |inner ℝ (wi - wj) u| := by
  rw [phiDeriv_det, inner_sub_left, abs_sub_comm]

/-- In two real dimensions a Lipschitz map sends every Lebesgue null set to a null set. -/
theorem lipschitz_image_null {f : (ℝ × ℝ) → ℝ × ℝ} {s : Set (ℝ × ℝ)} {C : ℝ≥0}
    (hf : LipschitzOnWith C f s) (hs : volume s = 0) : volume (f '' s) = 0 := by
  have hb := hf.hausdorffMeasure_image_le (d := (2 : ℝ)) (by norm_num)
  simp only [hausdorffMeasure_prod_real, hs, mul_zero] at hb
  exact le_zero_iff.mp hb

/-- Any null parameter set, crossed with arbitrary heights, has null bias-pair image. -/
theorem phi_image_null (p : Probe d) (wi wj : Space d) {N H : Set ℝ}
    (hNsub : N ⊆ Icc 0 p.length) (hN : volume N = 0) :
    volume (phi p wi wj '' (N ×ˢ H)) = 0 := by
  apply lipschitz_image_null ((phi_lipschitzOn p wi wj).mono ?_)
  · rw [Measure.volume_eq_prod, Measure.prod_prod, hN, zero_mul]
  · intro z hz
    exact ⟨hNsub hz.1, mem_univ _⟩

/-- The probe fails to have an ordinary derivative only on a null interior parameter set. -/
theorem nondifferentiable_interior_null (p : Probe d) :
    volume {s | s ∈ Ioo 0 p.length ∧ ¬ DifferentiableAt ℝ p.curve s} = 0 := by
  have hae : ∀ᵐ s, s ∈ Ioo 0 p.length → DifferentiableAt ℝ p.curve s := by
    filter_upwards [p.lipschitz.ae_differentiableWithinAt_of_mem_real] with s hs hs'
    exact (hs (Ioo_subset_Icc_self hs')).differentiableAt (Icc_mem_nhds hs'.1 hs'.2)
  simpa only [ae_iff, Classical.not_imp] using hae

/-- The ordinary nondifferentiability set on the closed probe interval is measurable. -/
theorem measurableSet_nondifferentiable (p : Probe d) :
    MeasurableSet {s | s ∈ Icc 0 p.length ∧ ¬ DifferentiableAt ℝ p.curve s} :=
  measurableSet_Icc.inter (measurableSet_of_differentiableAt ℝ p.curve).compl

/-- Adding the two endpoints to the exceptional set still gives zero parameter measure. -/
theorem nondifferentiable_null (p : Probe d) :
    volume {s | s ∈ Icc 0 p.length ∧ ¬ DifferentiableAt ℝ p.curve s} = 0 := by
  have hsub : {s | s ∈ Icc 0 p.length ∧ ¬ DifferentiableAt ℝ p.curve s} ⊆
      ({s | s ∈ Ioo 0 p.length ∧ ¬ DifferentiableAt ℝ p.curve s} ∪ {0}) ∪
        {p.length} := by
    intro s hs
    by_cases hz : s = 0
    · exact Or.inl (Or.inr hz)
    by_cases hL : s = p.length
    · exact Or.inr hL
    exact Or.inl (Or.inl ⟨⟨lt_of_le_of_ne hs.1.1 (Ne.symm hz),
      lt_of_le_of_ne hs.1.2 hL⟩, hs.2⟩)
  apply measure_mono_null hsub
  exact measure_union_null (measure_union_null (nondifferentiable_interior_null p)
    (by simp)) (by simp)

/-- Exceptional nondifferentiable parameters have null bias-pair image at all heights. -/
theorem phi_nondifferentiable_image_null (p : Probe d) (wi wj : Space d) (H : Set ℝ) :
    volume (phi p wi wj ''
      ({s | s ∈ Icc 0 p.length ∧ ¬ DifferentiableAt ℝ p.curve s} ×ˢ H)) = 0 := by
  exact phi_image_null p wi wj (fun s hs => hs.1) (nondifferentiable_null p)

/-- On the measurable regular part of the strip the derivative is the true Jacobian. -/
theorem hasFDerivAt_phi_of_differentiableAt (p : Probe d) (wi wj : Space d)
    {z : ℝ × ℝ} (hz : DifferentiableAt ℝ p.curve z.1) :
    HasFDerivAt (phi p wi wj)
      (phiDeriv (inner ℝ wi (deriv p.curve z.1))
        (inner ℝ wj (deriv p.curve z.1))) z :=
  hasFDerivAt_phi p wi wj (deriv p.curve z.1) z hz.hasDerivAt

/-- In particular the entire nondifferentiability strip has null image, retaining all heights. -/
theorem phi_nondifferentiable_interior_image_null (p : Probe d) (wi wj : Space d)
    (H : Set ℝ) :
    volume (phi p wi wj ''
      ({s | s ∈ Ioo 0 p.length ∧ ¬ DifferentiableAt ℝ p.curve s} ×ˢ H)) = 0 := by
  apply phi_image_null p wi wj (fun s hs => Ioo_subset_Icc_self hs.1)
  exact nondifferentiable_interior_null p

/-- The exceptional two-dimensional strip used by the area formula. -/
def badStrip (p : Probe d) : Set (ℝ × ℝ) :=
  {s | s ∈ Icc 0 p.length ∧ ¬ DifferentiableAt ℝ p.curve s} ×ˢ univ

theorem measurableSet_badStrip (p : Probe d) : MeasurableSet (badStrip p) :=
  (measurableSet_nondifferentiable p).prod MeasurableSet.univ

theorem badStrip_null (p : Probe d) : volume (badStrip p) = 0 := by
  rw [badStrip, Measure.volume_eq_prod, Measure.prod_prod, nondifferentiable_null p,
    zero_mul]

theorem phi_badStrip_image_null (p : Probe d) (wi wj : Space d) :
    volume (phi p wi wj '' (strip p ∩ badStrip p)) = 0 := by
  apply measure_mono_null (image_mono inter_subset_right)
  exact phi_nondifferentiable_image_null p wi wj univ

/-- The area-formula derivative hypothesis follows from the original Lipschitz probe. -/
theorem hasFDerivWithinAt_phi_off_badStrip (p : Probe d) (wi wj : Space d)
    {z : ℝ × ℝ} (hz : z ∈ strip p \ badStrip p) :
    HasFDerivWithinAt (phi p wi wj)
      (phiDeriv (inner ℝ wi (deriv p.curve z.1))
        (inner ℝ wj (deriv p.curve z.1))) (strip p \ badStrip p) z := by
  have hd : DifferentiableAt ℝ p.curve z.1 := by
    by_contra hn
    exact hz.2 ⟨⟨hz.1.1, hn⟩, mem_univ _⟩
  exact (hasFDerivAt_phi_of_differentiableAt p wi wj hd).hasFDerivWithinAt

/-- Consequently the determinant of the genuine Fréchet derivative has the source value. -/
theorem abs_det_fderiv_phi (p : Probe d) (wi wj : Space d)
    {z : ℝ × ℝ} (hz : DifferentiableAt ℝ p.curve z.1) :
    |(fderiv ℝ (phi p wi wj) z).det| =
      |inner ℝ (wi - wj) (deriv p.curve z.1)| := by
  rw [(hasFDerivAt_phi_of_differentiableAt p wi wj hz).fderiv]
  exact phiDeriv_abs_det wi wj (deriv p.curve z.1)

end Paper35.Source.CrossingJacobian
