import Paper28.CompactNeighborhoodTail
import Paper28.StratifiedSharpMass

/-! Own analytic approximation assembled from the two Euclidean deformation
decompositions, strict tangent convergence, compact localization, finite
smooth round strata and the incident-envelope proof. In particular no
approximating cycles or sharp mass bound are supplied as inputs. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter MeasureTheory Set
open scoped Topology
universe w v

set_option maxHeartbeats 600000 in
theorem sharp_neighborhood_approximation {Y : Type w} (metricY : MetricSpace Y) {d k : ℕ}
    (I : CompactIntegralCurrentAlgebraInput.{0,v} (EuclideanAmbient d) inferInstance)
    (S : EuclideanSimplexIntegrationInput d I) (E : EuclideanDeformationInput d I S)
    (R : EuclideanCurrentTangentInput d I)
    (hRes : StrictPolarMeasureContinuityInput.{0}) (hPort : UpperPortmanteauInput.{0})
    (J : CompactIntegralCurrentAlgebraInput.{w,v} Y metricY)
    (U : Set (EuclideanAmbient d)) (f : EuclideanAmbient d → Y) (hU : IsOpen U)
    (hf : LipschitzNearSet inferInstance metricY f U)
    (P : NeighborhoodCurrentPushforwardInput inferInstance metricY I J U f hU hf)
    (A : EuclideanCurrentAreaInput metricY I R J U f hU hf P)
    (T : supportedCurrents I U (k+1)) (hCycle : I.boundary k T.val = 0)
    (hInjective : Set.InjOn f (I.support T.val))
    {Idx : Type*} [Fintype Idx] (m : Idx → ℕ) (cells : Idx → Set (EuclideanAmbient d))
    (hClosed : ∀ j, IsClosed (cells j)) (hCover : U ⊆ ⋃ j, cells j)
    (g : ∀ j, EuclideanAmbient d → EuclideanSpace ℝ (Fin (m j)))
    (D : ∀ j, EuclideanAmbient d → Matrix (Fin (m j)) (Fin d) ℝ)
    (hD : ∀ j, ContinuousOn (D j) (U ∩ cells j))
    (Face : Idx → Type*) [∀ j, Fintype (Face j)]
    (strata : ∀ j, Face j → Set (EuclideanAmbient d))
    (hStrata : ∀ j, U ∩ cells j ⊆ ⋃ l, strata j l)
    (hUnit : ∀ j l x, x ∈ strata j l → ‖g j x‖ = 1)
    (hRound : ∀ j l, RoundLiftOn metricY f (g j) (strata j l))
    (hSmooth : ∀ j l x, x ∈ strata j l →
      HasFDerivAt (g j) (Matrix.toEuclideanLin (D j x)).toContinuousLinearMap x) :
    ∃ Qi : ℕ → supportedCurrents I U (k+1), ∃ Si : ℕ → supportedCurrents I U (k+2),
      (∀ i, (Qi i).val ∈ euclideanPolyhedralCurrents S (k+1)) ∧
      (∀ i, I.boundary k (Qi i).val = 0) ∧
      (∀ i, J.boundary k (P.push (k+1) (Qi i)) = 0) ∧
      (∀ i, P.push (k+1) T-P.push (k+1) (Qi i) = J.boundary (k+1) (P.push (k+2) (Si i))) ∧
      Tendsto (fun i => J.mass (P.push (k+2) (Si i))) atTop (𝓝 0) ∧
      Tendsto (fun i => J.mass (P.push (k+1) (Qi i))) atTop (𝓝 (J.mass (P.push (k+1) T))) := by
  letI := metricY
  obtain ⟨Ti,Wi,ρ,hPoly,hCycles,hHom,hMass,hFill,hρ,hρT,hLoc,hWeak⟩ :=
    strict_euclidean_polyhedral_approximation hRes I S E R k T.val hCycle
  obtain ⟨N,hN,hTN,hNU,L,hLip,i₀,hi₀⟩ := compact_lipschitz_neighborhood_tail
    (I.support T.val) U (I.support_compact T.val) hU T.property
    (fun i => I.support (Ti i) ∪ I.support (Wi i)) ρ hρT hLoc f hf
  let Qi : ℕ → supportedCurrents I U (k+1) := fun i =>
    ⟨Ti (i+i₀),fun x hx => hNU (hi₀ i (Or.inl hx))⟩
  let Si : ℕ → supportedCurrents I U (k+2) := fun i =>
    ⟨Wi (i+i₀),fun x hx => hNU (hi₀ i (Or.inr hx))⟩
  have hHom' : ∀ i, T.val-(Qi i).val = I.boundary (k+1) (Si i).val := fun i => hHom (i+i₀)
  have hFill' : Tendsto (fun i => I.mass (Si i).val) atTop (𝓝 0) := hFill.comp (tendsto_add_atTop_nat i₀)
  have hSi : ∀ i, I.support (Si i).val ⊆ N := fun i _ hx => hi₀ i (Or.inr hx)
  let pieces : Idx → Set (EuclideanAmbient d) := fun j => N ∩ cells j
  have hPieceCover : N ⊆ ⋃ j, pieces j := by
    intro x hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp (hCover (hNU hx))
    exact mem_iUnion.mpr ⟨j,hx,hj⟩
  have hPieceU : ∀ j, pieces j ⊆ U ∩ cells j := fun _ _ hx => ⟨hNU hx.1,hx.2⟩
  have hSharp := sharp_mass_from_finite_round_strata metricY I R J U f hU hf P A hPort T Qi Si
    hHom' hFill' N L hLip hSi m pieces g D
    (fun j => hN.inter_right (hClosed j)) (fun j => (hD j).mono (hPieceU j))
    Face strata (fun j => (hPieceU j).trans (hStrata j)) hUnit hRound hSmooth
    (hTN.trans hPieceCover) (fun i _ hx => hPieceCover (hi₀ i (Or.inl hx))) hInjective
    (hWeak.comp (tendsto_add_atTop_nat i₀))
  refine ⟨Qi,Si,(fun i => hPoly (i+i₀)),(fun i => hCycles (i+i₀)),?_,
    (fun i => pushforward_homology_relation P (k+1) T (Qi i) (Si i) (hHom' i)),
    pushed_fillings_mass_tendsto_zero P (k+1) Si N L hLip hSi hFill',hSharp⟩
  intro i
  rw [P.boundary_comm]
  have hz : supportedBoundary I U k (Qi i) = 0 := Subtype.ext (hCycles (i+i₀))
  rw [hz,map_zero]

end Paper28
