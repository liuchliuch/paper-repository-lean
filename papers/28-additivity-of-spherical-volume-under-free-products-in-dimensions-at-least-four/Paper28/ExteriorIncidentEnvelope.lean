import Paper28.CompoundJacobian

/-! The source incident Jacobian on actual Euclidean exterior vectors.
Clipping outside the unit-vector compact domain makes it globally bounded
without changing any rectifiable tangent value. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
variable {J : Type*} [Fintype J]

def exteriorIncidentEnvelope {d k : ℕ} (m : J → ℕ)
    (pieces : J → Set (EuclideanSpace ℝ (Fin d)))
    (D : ∀ j, EuclideanSpace ℝ (Fin d) → Matrix (Fin (m j)) (Fin d) ℝ)
    (B : J → ℝ) (p : EuclideanSpace ℝ (Fin d) × EuclideanExterior d k) : ℝ :=
  incidentEnvelope (fun j => Prod.fst ⁻¹' pieces j)
    (fun j p => min (B j) (exteriorJacobian (k := k) (D j p.1) p.2)) p

theorem exteriorIncidentEnvelope_upperSemicontinuous {d k : ℕ} (m : J → ℕ)
    (pieces : J → Set (EuclideanSpace ℝ (Fin d)))
    (D : ∀ j, EuclideanSpace ℝ (Fin d) → Matrix (Fin (m j)) (Fin d) ℝ)
    (B : J → ℝ) (hClosed : ∀ j, IsClosed (pieces j))
    (hD : ∀ j, ContinuousOn (D j) (pieces j)) :
    UpperSemicontinuous (exteriorIncidentEnvelope (k := k) m pieces D B) := by
  apply incidentEnvelope_upperSemicontinuous
  · intro j
    exact (hClosed j).preimage continuous_fst
  · intro j
    have hDfst : ContinuousOn
        (fun p : EuclideanSpace ℝ (Fin d) × EuclideanExterior d k => D j p.1)
        (Prod.fst ⁻¹' pieces j) :=
      (hD j).comp continuous_fst.continuousOn (fun _ hp => hp)
    have hJ : ContinuousOn
        (fun p : EuclideanSpace ℝ (Fin d) × EuclideanExterior d k => exteriorJacobian (k := k) (D j p.1) p.2)
        (Prod.fst ⁻¹' pieces j) :=
      exteriorJacobian_continuousOn (k := k) _ _ _ hDfst continuous_snd.continuousOn
    exact ContinuousOn.inf continuousOn_const hJ

theorem exteriorIncidentEnvelope_bounded {d k : ℕ} (m : J → ℕ)
    (pieces : J → Set (EuclideanSpace ℝ (Fin d)))
    (D : ∀ j, EuclideanSpace ℝ (Fin d) → Matrix (Fin (m j)) (Fin d) ℝ)
    (B : J → ℝ) : ∃ M : ℝ, ∀ p, 0 ≤ exteriorIncidentEnvelope (k := k) m pieces D B p ∧
      exteriorIncidentEnvelope (k := k) m pieces D B p ≤ M := by
  let M := incidentEnvelope (fun _ : J => (univ : Set Unit)) (fun j _ => B j) ()
  refine ⟨M,?_⟩
  intro p
  refine ⟨incidentEnvelope_nonneg _ _ _,?_⟩
  apply incidentEnvelope_le
  · exact incidentEnvelope_nonneg _ _ _
  · intro j _
    exact (min_le_left _ _).trans (le_incidentEnvelope
      (fun _ : J => (univ : Set Unit)) (fun j (_ : Unit) => B j) () j (mem_univ _))

set_option maxHeartbeats 600000 in
theorem exists_exteriorJacobian_bound {d m k : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : IsCompact K)
    (D : EuclideanSpace ℝ (Fin d) → Matrix (Fin m) (Fin d) ℝ) (hD : ContinuousOn D K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ K, ∀ τ : EuclideanExterior d k, ‖τ‖ = 1 → exteriorJacobian (k := k) (D x) τ ≤ B := by
  let Q := K ×ˢ Metric.sphere (0 : EuclideanExterior d k) 1
  have hQ : IsCompact Q := hK.prod (isCompact_sphere _ _)
  have hJac : ContinuousOn
      (fun p : EuclideanSpace ℝ (Fin d) × EuclideanExterior d k => exteriorJacobian (k := k) (D p.1) p.2) Q :=
    exteriorJacobian_continuousOn (k := k) Q (fun p => D p.1) (fun p => p.2)
      (hD.comp continuous_fst.continuousOn (fun _ hp => hp.1)) continuous_snd.continuousOn
  obtain ⟨B,hB⟩ := (hQ.image_of_continuousOn hJac).bddAbove
  refine ⟨max 0 B,le_max_left _ _,?_⟩
  intro x hx τ hτ
  apply (hB _).trans (le_max_right _ _)
  exact ⟨(x,τ),⟨hx,by simpa only [Metric.mem_sphere,dist_zero_right] using hτ⟩,rfl⟩

/-- At a simple tangent vector every incident derivative has the same
Gram matrix. The bounded upper envelope is therefore exactly that actual
Jacobian, even on a singular face shared by several pieces. -/
theorem exteriorIncidentEnvelope_tangent_eq (hCB : CauchyBinetInput) {d k : ℕ}
    (m : J → ℕ) (pieces : J → Set (EuclideanSpace ℝ (Fin d)))
    (D : ∀ j, EuclideanSpace ℝ (Fin d) → Matrix (Fin (m j)) (Fin d) ℝ) (B : J → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (e : Fin k → EuclideanSpace ℝ (Fin d))
    (G : Matrix (Fin k) (Fin k) ℝ) (hSome : ∃ j, x ∈ pieces j)
    (hGram : ∀ j, x ∈ pieces j → Matrix.gram ℝ (fun i => Matrix.toEuclideanLin (D j x) (e i)) = G)
    (hBound : ∀ j, x ∈ pieces j → exteriorJacobian (k := k) (D j x) (pluckerCoordinates e) ≤ B j) :
    exteriorIncidentEnvelope (k := k) m pieces D B (x,pluckerCoordinates e) = Real.sqrt G.det := by
  apply incidentEnvelope_eq
  · exact Real.sqrt_nonneg _
  · exact hSome
  · intro j hj
    rw [min_eq_right (hBound j hj),exteriorJacobian_plucker hCB,hGram j hj]

end Paper28
