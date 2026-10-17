import Paper34.Model
import Paper34.LAD
import Paper34.CellMass
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.Compact

/-!
# Native finite-dimensional norms and optimization foundations

The norm on the actual bounded-coordinate-degree polynomial submodule is
induced by its injective restriction to continuous functions on the source cube.
Consequently it is exactly the source supremum norm. The general minimization
lemma below is a topological consequence of a proved positive norm lower bound;
it does not replace the paper's own LAD inequality.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology

namespace Paper34

noncomputable section

instance cubeCompactSpace (n : ℕ) : CompactSpace (cube n) :=
  isCompact_iff_compactSpace.mp isCompact_Icc

instance cubeNonempty (n : ℕ) : Nonempty (cube n) :=
  (cube_nonempty n).to_subtype

/-- Actual polynomial evaluation as a continuous function on the source cube. -/
def polynomialCubeEval (n d : ℕ) : PolynomialSpace n d →ₗ[ℝ] C(cube n, ℝ) where
  toFun q := ⟨fun x => polyEval q x, (continuous_polyEval q).comp continuous_subtype_val⟩
  map_add' q r := by ext x; simp [polyEval]
  map_smul' c q := by ext x; simp [polyEval]

/-- Restriction to the cube is injective, by polynomial identity on an infinite
box in every coordinate. -/
theorem polynomialCubeEval_injective (n d : ℕ) : Function.Injective (polynomialCubeEval n d) := by
  intro q r h
  apply Subtype.ext
  apply MvPolynomial.funext_set (fun _ : Fin n => Icc (-1 : ℝ) 1)
    (fun _ => Set.Icc_infinite (by norm_num : (-1 : ℝ) < 1))
  intro x hx
  have hcube : x ∈ cube n :=
    ⟨fun k => (hx k (mem_univ k)).1, fun k => (hx k (mem_univ k)).2⟩
  exact congrArg (fun f : C(cube n, ℝ) => f ⟨x, hcube⟩) h

instance polynomialSpaceNormedAddCommGroup (n d : ℕ) : NormedAddCommGroup (PolynomialSpace n d) :=
  NormedAddCommGroup.induced _ _ (polynomialCubeEval n d) (polynomialCubeEval_injective n d)

instance polynomialSpaceNormedSpace (n d : ℕ) : NormedSpace ℝ (PolynomialSpace n d) :=
  NormedSpace.induced ℝ _ _ (polynomialCubeEval n d)

/-- The induced native norm is exactly the paper's actual supremum norm. -/
theorem norm_eq_supNorm {n d : ℕ} (q : PolynomialSpace n d) : ‖q‖ = supNorm q := by
  change ‖polynomialCubeEval n d q‖ = supNorm q
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (supNorm_nonneg q)).mpr
    intro x
    exact eval_le_supNorm q x.property
  · obtain ⟨x, hx, heq⟩ := supNorm_attained q
    rw [← heq]
    exact (polynomialCubeEval n d q).norm_coe_le_norm ⟨x, hx⟩

/-- The actual source polynomial space is finite-dimensional and proper. -/
theorem polynomialSpace_proper (n d : ℕ) : ProperSpace (PolynomialSpace n d) := inferInstance

/-- Evaluation at any fixed point is an actual linear functional. -/
def polyEvalLinear {n d : ℕ} (x : Point n) : PolynomialSpace n d →ₗ[ℝ] ℝ where
  toFun q := polyEval q x
  map_add' q r := by simp [polyEval]
  map_smul' c q := by simp [polyEval]

/-- Polynomial evaluation is continuous in the polynomial argument, also for
fixed points outside the cube. -/
theorem continuous_polyEval_in_polynomial {n d : ℕ} (x : Point n) :
    Continuous (fun q : PolynomialSpace n d => polyEval q x) :=
  (polyEvalLinear x).continuous_of_finiteDimensional

/-- The actual finite-sample weighted LAD objective is continuous. -/
theorem continuous_weightedLAD {κ ι : Type*} [Fintype κ] {n d : ℕ}
    (S : κ → Finset ι) (X : ι → Point n) (Y : ι → ℝ) :
    Continuous (weightedLAD (n := n) (d := d) S X Y) := by
  unfold weightedLAD weightedAverage
  apply continuous_const.mul
  apply continuous_finset_sum
  intro c _
  apply continuous_const.mul
  apply continuous_finset_sum
  intro i _
  exact ((continuous_polyEval_in_polynomial (X i)).sub continuous_const).abs

/-- The actual Chebyshev pushforward is supported on the cube. -/
theorem chebyshevLaw_ae_cube (n : ℕ) : ∀ᵐ x ∂chebyshevLaw n, x ∈ cube n := by
  have hcos : Continuous (fun theta : Point n => fun k => Real.cos (theta k)) :=
    continuous_pi (fun k => Real.continuous_cos.comp (continuous_apply k))
  have hcube : MeasurableSet (cube n) := measurableSet_Icc
  unfold chebyshevLaw
  apply (ae_map_iff (p := fun x : Point n => x ∈ cube n)
    hcos.measurable.aemeasurable hcube).mpr
  exact ae_of_all _ (fun theta => ⟨fun k => Real.neg_one_le_cos (theta k),
    fun k => Real.cos_le_one (theta k)⟩)

/-- Every actual source polynomial is integrable under the Chebyshev law. -/
theorem integrable_polyEval {n d : ℕ} (q : PolynomialSpace n d) :
    Integrable (polyEval q) (chebyshevLaw n) := by
  apply (integrable_const (supNorm q)).mono' (continuous_polyEval q).aestronglyMeasurable
  filter_upwards [chebyshevLaw_ae_cube n] with x hx
  exact eval_le_supNorm q hx

/-- The source `L¹` norm is bounded by the actual supremum norm. -/
theorem l1Norm_le_supNorm {n d : ℕ} (q : PolynomialSpace n d) : l1Norm q ≤ supNorm q := by
  unfold l1Norm
  calc
    (∫ x, |polyEval q x| ∂chebyshevLaw n) ≤
        ∫ _x, supNorm q ∂chebyshevLaw n := by
      apply integral_mono_ae (integrable_polyEval q).abs (integrable_const _)
      filter_upwards [chebyshevLaw_ae_cube n] with x hx
      exact eval_le_supNorm q hx
    _ = supNorm q := by simp

/-- Standard finite-dimensional coercive minimization, stated with its exact
positive norm lower bound. The bound is an input to this general topological
lemma and is proved for the paper's objective elsewhere. -/
theorem exists_min_of_lower_norm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : E → ℝ}
    (hf : Continuous f) {c B : ℝ} (hc : 0 < c)
    (hlower : ∀ x, c * ‖x‖ - B ≤ f x) : ∃ x, ∀ y, f x ≤ f y := by
  apply hf.exists_forall_le
  apply tendsto_atTop_mono hlower
  simpa only [sub_eq_add_neg] using
    tendsto_atTop_add_const_right (cocompact E) (-B)
      (Filter.Tendsto.const_mul_atTop hc tendsto_norm_cocompact_atTop)

/-- The translated version convenient for a recovery error `q - p`. -/
theorem exists_min_of_lower_norm_sub {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : E → ℝ}
    (hf : Continuous f) (x0 : E) {c B : ℝ} (hc : 0 < c)
    (hlower : ∀ x, c * ‖x - x0‖ - B ≤ f x) : ∃ x, ∀ y, f x ≤ f y := by
  apply exists_min_of_lower_norm hf hc (B := B + c * ‖x0‖)
  intro x
  have htri : ‖x‖ ≤ ‖x - x0‖ + ‖x0‖ := by
    simpa only [sub_add_cancel] using norm_add_le (x - x0) x0
  have htri' := mul_le_mul_of_nonneg_left htri hc.le
  nlinarith [hlower x]

end

end Paper34
