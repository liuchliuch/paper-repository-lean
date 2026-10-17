import ELV.LowFamily
import ELV.OrthogonalObstruction

/-! Signed-Gram witnesses using just one query direction cannot have finite
uniform cost over the full promised oracle family. -/
noncomputable section
namespace ELV.Costs
open ELV.Model
variable {n : ℕ} [NeZero n] {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- A one-direction Gram constraint, with the inverse direction represented
by sigma=-1 and the forward direction by sigma=1. -/
def OneDirectionConstraint (gap : Gap) (σ : ℂ) (f : promisedFamily n gap.δ → K) : Prop :=
  ∀ O O', (if label gap.δ O = label gap.δ O' then (0 : ℂ) else 1) =
    (1 - inner ℂ O.val.phi O'.val.phi) * (σ * inner ℂ (f O) (f O'))

/-- Real Bessel obstruction on actual legal oracles, for either query direction. -/
theorem oneDirection_no_uniform_bound (gap : Gap) (σ : ℂ) (hσ : ‖σ‖ = 1)
    (f : promisedFamily n gap.δ → K) (h : OneDirectionConstraint gap σ f)
    (C : ℝ) (hbound : ∀ O, ‖f O‖ ^ 2 ≤ C) : False := by
  let L := lowInstance (n := n) gap
  obtain ⟨_,Op,_,hlabel,_⟩ := boundary_pair (n := n) gap
  have hσne : σ ≠ 0 := by intro hz; rw [hz,norm_zero] at hσ; norm_num at hσ
  have horth : ∀ i j, i ≠ j → inner ℂ (f (L i)) (f (L j)) = 0 := by
    intro i j hij
    have hh := h (L i) (L j)
    rw [lowInstance_label,lowInstance_label,if_pos rfl] at hh
    have hz : σ * inner ℂ (f (L i)) (f (L j)) = 0 :=
      (mul_eq_zero.mp hh.symm).resolve_left (lowInstance_filter_ne_zero gap i j hij)
    exact (mul_eq_zero.mp hz).resolve_left hσne
  have hcross : ∀ i, (1/2 : ℝ) ≤ ‖inner ℂ (f (L i)) (f Op)‖ := by
    intro i
    have hh := h (L i) Op
    rw [lowInstance_label,hlabel,if_neg (show (0 : Fin 2) ≠ 1 by decide)] at hh
    have hn := congrArg norm hh
    rw [norm_one,norm_mul,norm_mul,hσ,one_mul] at hn
    have hd : ‖1 - inner ℂ (L i).val.phi Op.val.phi‖ ≤ 2 := by
      have hc := norm_inner_le_norm (𝕜 := ℂ) (L i).val.phi Op.val.phi
      rw [(L i).val.phi_norm,Op.val.phi_norm,mul_one] at hc
      have ht := norm_sub_le (1 : ℂ) (inner ℂ (L i).val.phi Op.val.phi)
      rw [norm_one] at ht
      linarith
    have hm := mul_le_mul_of_nonneg_right hd (norm_nonneg (inner ℂ (f (L i)) (f Op)))
    nlinarith
  have hne : f (L 0) ≠ 0 := by
    intro hz
    have hh := hcross 0
    rw [hz,inner_zero_left,norm_zero] at hh
    norm_num at hh
  have hC : 0 < C := (sq_pos_of_pos (norm_pos_iff.mpr hne)).trans_le (hbound (L 0))
  exact Bessel.orthogonal_no_uniform_bound (fun i => f (L i)) (f Op)
    horth hcross C hC (fun i => hbound (L i)) (hbound Op)

end ELV.Costs
