import ELV.FourOracles
import ELV.ExecutedWitness

noncomputable section
namespace ELV.AdversaryFour
open ELV.Stabilize ELV.FourOracles
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma relative_inner (P Q : E ≃ₗᵢ[ℂ] E) (x y : E) :
    inner ℂ (P x) (Q y) = inner ℂ x ((Q.trans P.symm) y) := by
  rw [← P.inner_map_map x ((Q.trans P.symm) y)]
  simp [LinearIsometryEquiv.trans_apply]

/-- Four exact opposite-label filter constraints force the sharp norm sum.
No support restrictions on any of the query vectors are imposed. -/
theorem four_witness_bound (P Q : E ≃ₗᵢ[ℂ] E) (μ s : ℝ) (hs : 0 ≤ s)
    (hcircle : μ^2+s^2=1)
    (hT : ∀ z, (Q.trans P.symm) z + (Q.trans P.symm).symm z = (2*μ : ℂ) • z)
    (vL vH : Bool → E)
    (hv : ∀ ε η, (1 : ℂ) = inner ℂ (vL ε) (vH η) -
      inner ℂ (signed P ε (vL ε)) (signed Q η (vH η))) :
    4 ≤ s*(‖vL false‖^2+‖vL true‖^2+‖vH false‖^2+‖vH true‖^2) := by
  have h00 := hv false false
  have h01 := hv false true
  have h10 := hv true false
  have h11 := hv true true
  simp only [signed_false,signed_true_apply,inner_neg_left,inner_neg_right,neg_neg,
    relative_inner,sub_neg_eq_add] at h00 h01 h10 h11
  have he : inner ℂ (WithLp.toLp 2 (vL false,vL true))
      (filterBlock (Q.trans P.symm) μ (WithLp.toLp 2 (vH false,vH true))) = 2 := by
    rw [filterBlock_inner]
    change (alpha μ : ℂ)*(inner ℂ (vL false) (vH false)-inner ℂ (vL false) ((Q.trans P.symm) (vH false))) +
      (beta μ : ℂ)*(inner ℂ (vL false) (vH true)+inner ℂ (vL false) ((Q.trans P.symm) (vH true))) +
      (beta μ : ℂ)*(inner ℂ (vL true) (vH false)+inner ℂ (vL true) ((Q.trans P.symm) (vH false))) +
      (alpha μ : ℂ)*(inner ℂ (vL true) (vH true)-inner ℂ (vL true) ((Q.trans P.symm) (vH true))) = 2
    rw [← h00,← h01,← h10,← h11]
    simp [alpha,beta]
    ring
  have hb := filter_quadratic (Q.trans P.symm) μ s hs hcircle hT
    (WithLp.toLp 2 (vL false,vL true)) (WithLp.toLp 2 (vH false,vH true))
  rw [he,WithLp.prod_norm_sq_eq_of_L2,WithLp.prod_norm_sq_eq_of_L2] at hb
  norm_num at hb
  simpa only [add_assoc] using hb

end ELV.AdversaryFour
