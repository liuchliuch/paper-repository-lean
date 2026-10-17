import Paper28.NeighborhoodPushforwardInput

/-! Exact pushforward homology relations and vanishing pushed fillings,
then the native upper/lower mass convergence argument for actual currents. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open CategoryTheory Filter Set
open scoped Topology
universe u w v
variable {X : Type u} {Y : Type w} {metricX : MetricSpace X} {metricY : MetricSpace Y}
variable {I : CompactIntegralCurrentAlgebraInput.{u,v} X metricX}
  {J : CompactIntegralCurrentAlgebraInput.{w,v} Y metricY}
  {U : Set X} {f : X → Y}
  {hU : @IsOpen X metricX.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace U}
  {hf : LipschitzNearSet metricX metricY f U}
variable (P : NeighborhoodCurrentPushforwardInput metricX metricY I J U f hU hf)

def neighborhoodPushforwardChainMap : supportedCurrentChainComplex I U ⟶ compactCurrentChainComplex J :=
  ChainComplex.ofHom _ _ _ _ _ _ (fun k => AddCommGrpCat.ofHom (P.push k)) (by
    intro k
    ext C
    exact P.boundary_comm k C)

theorem pushforward_homology_relation (k : ℕ) (T Q : supportedCurrents I U k)
    (S : supportedCurrents I U (k+1)) (h : T.val-Q.val = I.boundary k S.val) :
    P.push k T-P.push k Q = J.boundary k (P.push (k+1) S) := by
  have hS : T-Q = supportedBoundary I U k S := Subtype.ext h
  rw [P.boundary_comm,← map_sub,hS]

theorem pushed_fillings_mass_tendsto_zero (k : ℕ) (Si : ℕ → supportedCurrents I U (k+1))
    (K : Set X) (L : NNReal)
    (hLip : letI := metricX; letI := metricY; LipschitzOnWith L f K)
    (hSupport : ∀ i, I.support (Si i).val ⊆ K)
    (hFill : Tendsto (fun i => I.mass (Si i).val) atTop (𝓝 0)) :
    Tendsto (fun i => J.mass (P.push (k+1) (Si i))) atTop (𝓝 0) := by
  letI := metricX
  letI := metricY
  apply squeeze_zero (fun i => J.mass_nonneg _) (fun i => P.mass_lipschitz_le (k+1) (Si i) L (hLip.mono (hSupport i)))
  simpa using tendsto_const_nhds.mul hFill

theorem pushed_mass_tendsto_of_sharp_upper (k : ℕ) (T : supportedCurrents I U k)
    (Qi : ℕ → supportedCurrents I U k) (Si : ℕ → supportedCurrents I U (k+1))
    (hHom : ∀ i, T.val-(Qi i).val = I.boundary k (Si i).val)
    (hFill : Tendsto (fun i => J.mass (P.push (k+1) (Si i))) atTop (𝓝 0))
    (hUpper : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, J.mass (P.push k (Qi i)) ≤ J.mass (P.push k T)+ε) :
    Tendsto (fun i => J.mass (P.push k (Qi i))) atTop (𝓝 (J.mass (P.push k T))) := by
  have hHom' : ∀ i, P.push k T-P.push k (Qi i) = J.boundary k (P.push (k+1) (Si i)) :=
    fun i => pushforward_homology_relation P k T (Qi i) (Si i) (hHom i)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hUpper (ε/2) (by positivity),
    J.mass_lower_semicontinuity k (P.push k T) (fun i => P.push k (Qi i))
      (fun i => P.push (k+1) (Si i)) hHom' hFill (ε/2) (by positivity)] with i hi hlo
  rw [Real.dist_eq]
  apply abs_lt.mpr
  constructor <;> linarith

end Paper28
