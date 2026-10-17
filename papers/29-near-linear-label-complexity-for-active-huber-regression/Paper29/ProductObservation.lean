import Paper29.Transcript
import Paper29.FreshProduct
import Paper29.FreshHistory

noncomputable section
open scoped BigOperators Classical
namespace Paper29.Transcript

/-- An arbitrary finite hidden source, its conditionally independent response
bits, and an independent private seed. No information bound is a field. -/
def productObservationLaw {S I E : Type} [Fintype S] [Fintype I] [Fintype E] [DecidableEq I]
    (θ : S → ℝ) (hθ : ∀ s, 0 ≤ θ s) (hsθ : ∑ s,θ s=1)
    (q : E → ℝ) (hq : ∀ e, 0 ≤ q e) (hsq : ∑ e,q e=1)
    (p : S → I → Bool → ℝ) (hp : ∀ s i b, 0 ≤ p s i b) (hsp : ∀ s i,∑ b,p s i b=1) :
    Law (S × ((I → Bool) × E)) where
  weight ω := θ ω.1 * (∏ i,p ω.1 i (ω.2.1 i))*q ω.2.2
  nonneg ω := mul_nonneg (mul_nonneg (hθ ω.1) (Finset.prod_nonneg (fun i _ => hp _ _ _))) (hq _)
  total := by
    have hpi (s) : (∑ y : I → Bool,∏ i,p s i (y i)) = 1 := by
      rw [← Fintype.prod_sum]
      simp only [hsp,Finset.prod_const_one]
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type,← Finset.mul_sum,hsq,mul_one,hpi,hsθ]

namespace ProductObservation
variable {S I E : Type} [Fintype S] [Fintype I] [Fintype E] [DecidableEq I]
    (θ : S → ℝ) (hθ : ∀ s, 0 ≤ θ s) (hsθ : ∑ s,θ s=1)
    (q : E → ℝ) (hq : ∀ e, 0 ≤ q e) (hsq : ∑ e,q e=1)
    (p : S → I → Bool → ℝ) (hp : ∀ s i b, 0 ≤ p s i b) (hsp : ∀ s i,∑ b,p s i b=1)

local notation "P" => productObservationLaw θ hθ hsθ q hq hsq p hp hsp

lemma mass_source_responses (s : S) (y : I → Bool) :
    (P).mass (fun ω => (ω.1,ω.2.1)) (s,y) = θ s*(∏ i,p s i (y i)) := by
  unfold Law.mass
  simp only [Fintype.sum_prod_type,Prod.mk.injEq]
  simp [ite_and,productObservationLaw,← Finset.mul_sum,hsq]

lemma mass_source (s : S) : (P).mass Prod.fst s = θ s := by
  rw [← (P).sum_pair_mass_right Prod.fst (fun ω => ω.2.1)]
  simp_rw [mass_source_responses θ hθ hsθ q hq hsq p hp hsp]
  rw [← Finset.mul_sum,← Fintype.prod_sum]
  simp only [hsp,Finset.prod_const_one,mul_one]

lemma mass_seed (e : E) : (P).mass (fun ω => ω.2.2) e = q e := by
  unfold Law.mass
  simp only [Fintype.sum_prod_type]
  simp only [productObservationLaw]
  have hsp' (s : S) (i : I) : p s i true+p s i false=1 := by simpa only [Fintype.sum_bool] using hsp s i
  simp [← Finset.sum_mul,← Finset.mul_sum,← Fintype.prod_sum,hsp',hsθ]

lemma independent_seed : (P).Independent (fun ω => (ω.1,ω.2.1)) (fun ω => ω.2.2) := by
  intro sy e
  rcases sy with ⟨s,y⟩
  rw [mass_source_responses,mass_seed]
  unfold Law.mass
  simp only [Fintype.sum_prod_type,Prod.mk.injEq]
  simp [ite_and,productObservationLaw]

end ProductObservation
end Paper29.Transcript
