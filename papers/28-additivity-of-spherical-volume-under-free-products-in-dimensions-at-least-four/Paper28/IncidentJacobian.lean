import Paper28.FiniteIncidentEnvelope
import Paper28.FaceDerivativeIdentity
import Mathlib.Topology.Instances.Matrix

/-! The genuine Gram Jacobian envelope of the incident smooth pieces.
Its upper semicontinuity and exact tangent value are proved natively. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set Filter
open scoped Topology InnerProductSpace
variable {E F X J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [TopologicalSpace X] [Fintype J]

def frameImageJacobian {k : ℕ} (D : E →L[ℝ] F) (e : Fin k → E) : ℝ :=
  Real.sqrt (Matrix.gram ℝ (fun i => D (e i))).det

theorem frameImageJacobian_nonneg {k : ℕ} (D : E →L[ℝ] F) (e : Fin k → E) :
    0 ≤ frameImageJacobian D e := Real.sqrt_nonneg _

theorem frameImageJacobian_continuousOn {k : ℕ} (S : Set X)
    (D : X → E →L[ℝ] F) (e : X → Fin k → E)
    (hD : ContinuousOn D S) (he : ∀ i, ContinuousOn (fun x => e x i) S) :
    ContinuousOn (fun x => frameImageJacobian (D x) (e x)) S := by
  have hg : ContinuousOn (fun x => Matrix.gram ℝ (fun i => D x (e x i))) S := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    exact (hD.clm_apply (he i)).inner (hD.clm_apply (he j))
  have hdet : Continuous (fun M : Matrix (Fin k) (Fin k) ℝ => M.det) := continuous_id.matrix_det
  exact Real.continuous_sqrt.comp_continuousOn (hdet.comp_continuousOn hg)

def incidentJacobianEnvelope {k : ℕ} (pieces : J → Set E)
    (D : J → E → E →L[ℝ] F) (p : E×(Fin k → E)) : ℝ :=
  incidentEnvelope (fun j => Prod.fst ⁻¹' pieces j)
    (fun j p => frameImageJacobian (D j p.1) p.2) p

theorem incidentJacobianEnvelope_upperSemicontinuous {k : ℕ}
    (pieces : J → Set E) (D : J → E → E →L[ℝ] F)
    (hClosed : ∀ j, IsClosed (pieces j)) (hD : ∀ j, ContinuousOn (D j) (pieces j)) :
    UpperSemicontinuous (incidentJacobianEnvelope (k := k) pieces D) := by
  apply incidentEnvelope_upperSemicontinuous
  · intro j
    exact (hClosed j).preimage continuous_fst
  · intro j
    apply frameImageJacobian_continuousOn
    · exact (hD j).comp continuous_fst.continuousOn (fun _ h => h)
    · intro i
      exact ((continuous_apply i).comp continuous_snd).continuousOn

/-- Every incident extension has the same derivative on the limiting
tangent, because all extensions agree along the containing face. Thus the
finite upper envelope has exactly the required limiting Jacobian. -/
theorem incidentJacobianEnvelope_tangent_eq
    (pieces : J → Set E) (D : J → E → E →L[ℝ] F)
    (x : E) (S T : Submodule ℝ E) [FiniteDimensional ℝ T] (hTS : T ≤ S)
    (f : J → E → F) (h : E → F) (Dh : E →L[ℝ] F)
    (hSome : ∃ j, x ∈ pieces j)
    (hh : HasFDerivAt h Dh x)
    (hf : ∀ j, x ∈ pieces j → HasFDerivAt (f j) (D j x) x)
    (hFace : ∀ j, x ∈ pieces j →
      (fun v : S => f j (x+v.val)) =ᶠ[𝓝 0] (fun v : S => h (x+v.val))) :
    incidentJacobianEnvelope pieces D
      (x,fun i => (stdOrthonormalBasis ℝ T i).val) = frameJacobian (fun v : T => Dh v.val) := by
  apply incidentEnvelope_eq
  · exact Real.sqrt_nonneg _
  · exact hSome
  · intro j hj
    have hEq := derivatives_agree_on_subface S T hTS x (f j) h (D j x) Dh (hf j hj) hh (hFace j hj)
    unfold frameImageJacobian frameJacobian
    congr 2
    ext i l
    simp only [Matrix.gram_apply,hEq]

end Paper28
