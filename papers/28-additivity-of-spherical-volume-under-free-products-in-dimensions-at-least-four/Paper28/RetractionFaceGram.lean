import Paper28.ProjectiveRetraction
import Paper28.FaceDerivativeIdentity

/-! The source face Jacobian identity for an actual projective retraction
followed by incident smooth spherical lifts. The common-face transition
isometry preserves all tangent Gram entries. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter
open scoped Topology InnerProductSpace
variable {E F H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem retraction_face_gram_identity {k : ℕ}
    (P : E →L[ℝ] E) (ell : E →L[ℝ] ℝ) (x : E)
    (S : Submodule ℝ E) (g : E → F) (h : E → H)
    (Dg : E →L[ℝ] F) (Dh : E →L[ℝ] H) (A : H →ₗᵢ[ℝ] F)
    (hg : HasFDerivAt g Dg x) (hh : HasFDerivAt h Dh x)
    (hFace : (fun v : S => g (x+v.val)) =ᶠ[𝓝 0] (fun v : S => A (h (x+v.val))))
    (hEll : ell x = 1) (e : Fin k → E) (heS : ∀ i, e i ∈ S)
    (hPe : ∀ i, P (e i) = e i) (hElle : ∀ i, ell (e i) = 0) :
    Matrix.gram ℝ (fun i => Dg (projectiveRetractionDerivative P ell x (e i))) =
      Matrix.gram ℝ (fun i => Dh (e i)) := by
  let Ac : H →L[ℝ] F := A.toContinuousLinearMap
  have hAh : HasFDerivAt (fun y => A (h y)) (Ac.comp Dh) x := Ac.hasFDerivAt.comp x hh
  have hD := derivatives_agree_on_face S x g (fun y => A (h y)) Dg (Ac.comp Dh) hg hAh hFace
  have hValue : ∀ i, Dg (e i) = A (Dh (e i)) := fun i =>
    congrArg (fun L : S →L[ℝ] F => L ⟨e i,heS i⟩) hD
  ext i j
  simp only [Matrix.gram_apply,projectiveRetractionDerivative_face P ell x (e i) hEll (hPe i) (hElle i),
    projectiveRetractionDerivative_face P ell x (e j) hEll (hPe j) (hElle j),hValue]
  exact A.inner_map_map _ _

end Paper28
