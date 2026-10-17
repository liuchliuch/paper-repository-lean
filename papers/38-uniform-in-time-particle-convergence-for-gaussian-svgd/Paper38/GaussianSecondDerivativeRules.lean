import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Tactic.NormNum

noncomputable section
open Set Topology
namespace Paper38.GaussianEnergyGeometry
section Composition
variable {P Q : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]

lemma second_fderiv_comp_clm (g : Q → ℝ) (L : P →L[ℝ] Q) (x u w : P)
    (hg : ContDiffAt ℝ 2 g (L x)) :
    fderiv ℝ (fderiv ℝ (fun p => g (L p))) x u w =
      fderiv ℝ (fderiv ℝ g) (L x) (L u) (L w) := by
  have hD : DifferentiableAt ℝ (fderiv ℝ g) (L x) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt le_rfl
  have hd : HasFDerivAt (fun p : P => fderiv ℝ g (L p))
      ((fderiv ℝ (fderiv ℝ g) (L x)).comp L) x := hD.hasFDerivAt.comp x L.hasFDerivAt
  have hc : HasFDerivAt (fun _ : P => L) (0 : P →L[ℝ] P →L[ℝ] Q) x := hasFDerivAt_const L x
  have hnear : ∀ᶠ p in 𝓝 x, ContDiffAt ℝ 2 g (L p) :=
    L.continuous.continuousAt.eventually (hg.eventually (by norm_num))
  have heq : fderiv ℝ (fun p : P => g (L p)) =ᶠ[𝓝 x]
      (fun p => (fderiv ℝ g (L p)).comp L) := by
    filter_upwards [hnear] with p hp
    exact ((hp.differentiableAt (by norm_num)).hasFDerivAt.comp p L.hasFDerivAt).fderiv
  have hh := (hd.clm_comp hc).congr_of_eventuallyEq heq
  have ha := congrArg (fun B : P →L[ℝ] P →L[ℝ] ℝ => B u w) hh.fderiv
  simpa using ha

lemma second_fderiv_add (f g : P → ℝ) (x u w : P)
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    fderiv ℝ (fderiv ℝ (fun p => f p + g p)) x u w =
      fderiv ℝ (fderiv ℝ f) x u w + fderiv ℝ (fderiv ℝ g) x u w := by
  have hF : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt le_rfl
  have hG : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt le_rfl
  have heq : fderiv ℝ (fun p => f p + g p) =ᶠ[𝓝 x]
      (fun p => fderiv ℝ f p + fderiv ℝ g p) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with p hp hq
    exact fderiv_fun_add (hp.differentiableAt (by norm_num)) (hq.differentiableAt (by norm_num))
  have hh := (hF.hasFDerivAt.add hG.hasFDerivAt).congr_of_eventuallyEq heq
  have ha := congrArg (fun B : P →L[ℝ] P →L[ℝ] ℝ => B u w) hh.fderiv
  simpa using ha
end Composition

end Paper38.GaussianEnergyGeometry
