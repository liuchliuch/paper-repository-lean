import Paper14.AppendixStripArea
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Matrix.ToLin

open MeasureTheory Set
open scoped ENNReal Matrix
namespace Paper14
noncomputable section

def stripLinearMap (p q p' q' : ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  ((q • LinearMap.snd ℝ ℝ ℝ)-(p • LinearMap.fst ℝ ℝ ℝ)).prod
    ((q' • LinearMap.snd ℝ ℝ ℝ)-(p' • LinearMap.fst ℝ ℝ ℝ))

lemma stripLinearMap_apply (p q p' q' : ℝ) (x : ℝ × ℝ) :
    stripLinearMap p q p' q' x = (q*x.2-p*x.1,q'*x.2-p'*x.1) := rfl

lemma det_stripLinearMap (p q p' q' : ℝ) :
    LinearMap.det (stripLinearMap p q p' q') = p'*q-p*q' := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ)]
  have hm : LinearMap.toMatrix (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ) (stripLinearMap p q p' q') =
      !![-p,q;-p',q'] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply,Module.Basis.coe_finTwoProd_repr,stripLinearMap,
        Module.Basis.finTwoProd_zero,Module.Basis.finTwoProd_one]
  rw [hm,Matrix.det_fin_two]
  simp
  ring

/-- Exact area of the two full strips, before restricting to the Farey triangle. -/
theorem volume_two_strips (p q p' q' ε : ℝ) (hε : 0 ≤ ε) (hD : p'*q-p*q' ≠ 0) :
    volume {x : ℝ × ℝ | 1-ε < q*x.2-p*x.1 ∧ q*x.2-p*x.1 ≤ 1 ∧
      1-ε < q'*x.2-p'*x.1 ∧ q'*x.2-p'*x.1 ≤ 1} =
        ENNReal.ofReal (ε^2/|p'*q-p*q'|) := by
  letI : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
    change ((volume : Measure ℝ).prod volume).IsAddHaarMeasure
    infer_instance
  have heq : {x : ℝ × ℝ | 1-ε < q*x.2-p*x.1 ∧ q*x.2-p*x.1 ≤ 1 ∧
      1-ε < q'*x.2-p'*x.1 ∧ q'*x.2-p'*x.1 ≤ 1} =
        stripLinearMap p q p' q' ⁻¹' ((Ioc (1-ε) 1) ×ˢ (Ioc (1-ε) 1)) := by
    ext x
    simp [stripLinearMap_apply, and_assoc]
  rw [heq,Measure.addHaar_preimage_linearMap volume (by simpa [det_stripLinearMap] using hD),
    det_stripLinearMap]
  change ENNReal.ofReal |(p'*q-p*q')⁻¹| * ((volume.prod volume) ((Ioc (1-ε) 1) ×ˢ (Ioc (1-ε) 1))) = _
  rw [Measure.prod_prod,Real.volume_Ioc]
  have he : (1 : ℝ)-(1-ε) = ε := by ring
  rw [he,← ENNReal.ofReal_mul hε,← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  rw [abs_inv]
  ring

end
end Paper14
