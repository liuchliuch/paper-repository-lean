import Paper29.ExternalConvexSelection

noncomputable section
open MeasureTheory Filter
namespace Paper29.Attainment
open ExternalConvexSelection

theorem continuous_joint_labels {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (w : Fin n → ℝ) :
    Continuous (fun z : (Fin n → ℝ) × Space d => euclideanHuber A w z.1 z.2) := by
  unfold euclideanHuber affineHuber weightedHuber
  apply continuous_finset_sum
  intro i _
  have hx : Continuous (fun z : (Fin n → ℝ) × Space d => A.mulVec (WithLp.ofLp z.2)) := (A.mulVecLin.continuous_of_finiteDimensional.comp
    (PiLp.continuous_ofLp 2 (fun _ : Fin d => ℝ))).comp continuous_snd
  exact continuous_const.mul (continuous_huber.comp
    (((continuous_apply i).comp hx).sub ((continuous_apply i).comp continuous_fst)))

/-- AppendixA.3: actual Huber regularized minimizers, their uniqueness,
pointwise convergence to the already proved minimum-norm selection, and
Borel measurability in the observed labels. Every Huber hypothesis of the
separately disclosed general convex theorems is checked locally. -/
theorem minimumNormSelection_regularization {n d : ℕ}
    (parametric : ParametricQuadraticSelection) (tikhonov : TikhonovConvergence)
    (A : Matrix (Fin n) (Fin d) ℝ) (w : Fin n → ℝ) (hw : ∀ i,0 ≤ w i) :
    ∃ z : ℕ → (Fin n → ℝ) → Space d,
      (∀ k,Measurable (z k)) ∧
      (∀ k b,RegularizedMinimizer (euclideanHuber A w b) k (z k b) ∧
        ∀ x,RegularizedMinimizer (euclideanHuber A w b) k x → x=z k b) ∧
      (∀ b,Tendsto (fun k => z k b) atTop (nhds (minimumNormSelection A w b hw))) ∧
      Measurable (fun b => minimumNormSelection A w b hw) := by
  obtain ⟨z,hmeas,hmin⟩ := parametric n d (fun z => euclideanHuber A w z.1 z.2)
    (continuous_joint_labels A w) (fun b => convex_euclideanHuber A w b hw)
    (fun b x => weightedHuber_nonneg _ _ hw)
  have hconv (b : Fin n → ℝ) :
      Tendsto (fun k => z k b) atTop (nhds (minimumNormSelection A w b hw)) := by
    apply tikhonov d (euclideanHuber A w b) (continuous_euclideanHuber A w b)
      (convex_euclideanHuber A w b hw) (minimumNormSelection A w b hw)
      (minimumNormSelection_spec A w b hw).1
    · exact (minimumNormSelection_spec A w b hw).2
    · intro k
      exact (hmin k b).1
  exact ⟨z,hmeas,hmin,hconv,measurable_of_tendsto_metrizable hmeas (tendsto_pi_nhds.mpr hconv)⟩

end Paper29.Attainment
