import Paper28.NJacobian
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-! Agreement on a relative face forces equality of the actual derivatives
on its direction space. This is the tangent identity needed at singular
polyhedral faces; no sharp Jacobian assertion is an input. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter
open scoped Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem derivatives_agree_on_face (S : Submodule ℝ E) (x : E)
    (f g : E → F) (Df Dg : E →L[ℝ] F)
    (hf : HasFDerivAt f Df x) (hg : HasFDerivAt g Dg x)
    (hFace : (fun v : S => f (x+v.val)) =ᶠ[𝓝 0] (fun v : S => g (x+v.val))) :
    Df.comp S.subtypeL = Dg.comp S.subtypeL := by
  have hi : HasFDerivAt (fun v : S => x+v.val) S.subtypeL 0 := by
    have hc : HasFDerivAt (fun _ : S => x) (0 : S →L[ℝ] E) 0 := hasFDerivAt_const _ _
    have he : HasFDerivAt (fun v : S => v.val) S.subtypeL 0 := S.subtypeL.hasFDerivAt
    simpa only [zero_add] using hc.add he
  have hf' : HasFDerivAt f Df ((fun v : S => x+v.val) 0) := by simpa using hf
  have hg' : HasFDerivAt g Dg ((fun v : S => x+v.val) 0) := by simpa using hg
  have hfc := hf'.comp (f := fun v : S => x+v.val) (0 : S) hi
  have hgc := hg'.comp (f := fun v : S => x+v.val) (0 : S) hi
  exact (hfc.congr_of_eventuallyEq hFace.symm).unique hgc

theorem derivatives_agree_on_subface (S T : Submodule ℝ E) (hTS : T ≤ S) (x : E)
    (f g : E → F) (Df Dg : E →L[ℝ] F)
    (hf : HasFDerivAt f Df x) (hg : HasFDerivAt g Dg x)
    (hFace : (fun v : S => f (x+v.val)) =ᶠ[𝓝 0] (fun v : S => g (x+v.val))) :
    ∀ v : T, Df v.val = Dg v.val := by
  have h := derivatives_agree_on_face S x f g Df Dg hf hg hFace
  intro v
  exact congrArg (fun D : S →L[ℝ] F => D ⟨v.val,hTS v.property⟩) h

end Paper28
