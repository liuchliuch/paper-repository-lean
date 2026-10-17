import Paper28.EuclideanCurrentTangentInput
import Paper28.WeakMeasureInputs

/-! Source (16) for actual spatial-oriented-tangent measures. Generic
Euclidean current weak convergence and strict mass convergence instantiate
the precisely disclosed general Reshetnyak polar theorem. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter MeasureTheory
open scoped Topology
universe v

def orientedTangentMeasure {d : ℕ}
    {I : CompactIntegralCurrentAlgebraInput.{0,v} (EuclideanAmbient d) inferInstance}
    (R : EuclideanCurrentTangentInput d I) {k : ℕ} (C : I.Current k) :
    FiniteMeasure (EuclideanAmbient d × EuclideanExterior d k) :=
  (R.massMeasure C).map (fun x => (x,R.polar C x))

theorem strict_tangent_measure_tendsto (hRes : StrictPolarMeasureContinuityInput.{0}) {d k : ℕ}
    (I : CompactIntegralCurrentAlgebraInput.{0,v} (EuclideanAmbient d) inferInstance)
    (R : EuclideanCurrentTangentInput d I)
    (C : I.Current k) (Ci : ℕ → I.Current k) (Si : ℕ → I.Current (k+1))
    (hHom : ∀ i, C-Ci i = I.boundary k (Si i))
    (hFill : Tendsto (fun i => I.mass (Si i)) atTop (𝓝 0))
    (hMass : Tendsto (fun i => I.mass (Ci i)) atTop (𝓝 (I.mass C)))
    (hBound : ∃ M : ℝ, ∀ i, I.mass (Ci i) ≤ M)
    (hSupport : ∃ K : Set (EuclideanAmbient d), IsCompact K ∧ I.support C ⊆ K ∧ ∀ i, I.support (Ci i) ⊆ K) :
    Tendsto (fun i => orientedTangentMeasure R (Ci i)) atTop (𝓝 (orientedTangentMeasure R C)) := by
  have hTotal : Tendsto (fun i => (R.massMeasure (Ci i)).mass) atTop (𝓝 (R.massMeasure C).mass) := by
    apply NNReal.tendsto_coe.mp
    simpa only [R.total_mass_eq] using hMass
  exact hRes d (PluckerIndex d k) (fun i => R.massMeasure (Ci i)) (R.massMeasure C)
    (fun i => R.polar (Ci i)) (R.polar C)
    (fun i => R.polar_measurable (Ci i)) (R.polar_measurable C)
    (fun i => R.polar_unit (Ci i)) (R.polar_unit C)
    (R.weak_vector_density C Ci Si hHom hFill hBound hSupport) hTotal

end Paper28
