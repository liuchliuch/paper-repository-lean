import Paper28.PiecewiseCurrentMass

/-! The sharp mass theorem with only actual finite smooth face-stratum
geometry as hypotheses. All local Jacobian identities are derived from
the generic area-calculus laws; no Jacobian or mass estimate is a premise. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter MeasureTheory Set
open scoped Topology
universe w v

theorem sharp_mass_from_finite_round_strata {Y : Type w} (metricY : MetricSpace Y) {d k : ℕ}
    (I : CompactIntegralCurrentAlgebraInput.{0,v} (EuclideanAmbient d) inferInstance)
    (R : EuclideanCurrentTangentInput d I)
    (J : CompactIntegralCurrentAlgebraInput.{w,v} Y metricY)
    (U : Set (EuclideanAmbient d)) (f : EuclideanAmbient d → Y) (hU : IsOpen U)
    (hf : LipschitzNearSet inferInstance metricY f U)
    (P : NeighborhoodCurrentPushforwardInput inferInstance metricY I J U f hU hf)
    (A : EuclideanCurrentAreaInput metricY I R J U f hU hf P)
    (hPort : UpperPortmanteauInput.{0})
    (T : supportedCurrents I U k) (Qi : ℕ → supportedCurrents I U k) (Si : ℕ → supportedCurrents I U (k+1))
    (hHom : ∀ i, T.val-(Qi i).val = I.boundary k (Si i).val)
    (hFill : Tendsto (fun i => I.mass (Si i).val) atTop (𝓝 0))
    (N : Set (EuclideanAmbient d)) (L : NNReal)
    (hLip : letI := metricY; LipschitzOnWith L f N) (hSupport : ∀ i, I.support (Si i).val ⊆ N)
    {Idx : Type*} [Fintype Idx] (m : Idx → ℕ) (pieces : Idx → Set (EuclideanAmbient d))
    (g : ∀ j, EuclideanAmbient d → EuclideanSpace ℝ (Fin (m j)))
    (D : ∀ j, EuclideanAmbient d → Matrix (Fin (m j)) (Fin d) ℝ)
    (hK : ∀ j, IsCompact (pieces j)) (hD : ∀ j, ContinuousOn (D j) (pieces j))
    (Face : Idx → Type*) [∀ j, Fintype (Face j)]
    (strata : ∀ j, Face j → Set (EuclideanAmbient d))
    (hStrata : ∀ j, pieces j ⊆ ⋃ l, strata j l)
    (hUnit : ∀ j l x, x ∈ strata j l → ‖g j x‖ = 1)
    (hRound : ∀ j l, RoundLiftOn metricY f (g j) (strata j l))
    (hSmooth : ∀ j l x, x ∈ strata j l →
      HasFDerivAt (g j) (Matrix.toEuclideanLin (D j x)).toContinuousLinearMap x)
    (hT : I.support T.val ⊆ ⋃ j, pieces j) (hQi : ∀ i, I.support (Qi i).val ⊆ ⋃ j, pieces j)
    (hInjective : Set.InjOn f (I.support T.val))
    (hWeak : Tendsto (fun i => orientedTangentMeasure R (Qi i).val) atTop (𝓝 (orientedTangentMeasure R T.val))) :
    Tendsto (fun i => J.mass (P.push k (Qi i))) atTop (𝓝 (J.mass (P.push k T))) := by
  apply sharp_pushed_mass_tendsto metricY I R J U f hU hf P A hPort T Qi Si hHom hFill N L hLip hSupport
    m pieces D hK hD ?_ hT hQi hInjective hWeak
  intro C j
  exact metricJacobian_on_piece_of_finite_strata metricY I R J U f hU hf P A C
    (pieces j) (strata j) (g j) (D j) (hStrata j) (hUnit j) (hRound j) (hSmooth j)

end Paper28
