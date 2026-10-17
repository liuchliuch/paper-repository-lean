import Paper29.CompressedSuccess
import Paper29.EntropyBounds
import Paper29.FiniteWeightedAverage

noncomputable section
open scoped BigOperators Classical
namespace Paper29.HardDistribution
open Transcript

/-- Exact finite alphabet for short signs and the zero padded responses. -/
def shortAlphabet {n r : ℕ} (s : Signs r) (i : Fin n) : Option Bool :=
  if hi : i.val<r then some (s ⟨i.val,hi⟩) else none

def shortLabel : Option Bool → ℝ := Option.elim' 0 sign

theorem shortResponse_alphabet {n r : ℕ} (s : Signs r) :
    shortResponse (n:=n) s = fun i => shortLabel (shortAlphabet s i) := by
  funext i
  unfold shortResponse shortAlphabet
  split_ifs <;> rfl

def shortSeedLaw {E : Type} [Fintype E] {r : ℕ}
    (q : E → ℝ) (hq : ∀ e,0 ≤ q e) (hsq : ∑ e,q e=1) : Law (Signs r × E) where
  weight ω := signMass r ω.1*q ω.2
  nonneg ω := mul_nonneg (by unfold signMass; positivity) (hq ω.2)
  total := by simp only [Fintype.sum_prod_type,← Finset.mul_sum,hsq,mul_one,signMass_total]

theorem shortSeedLaw_source {E : Type} [Fintype E] {r : ℕ}
    (q : E → ℝ) (hq : ∀ e,0 ≤ q e) (hsq : ∑ e,q e=1) (s : Signs r) :
    (shortSeedLaw q hq hsq).mass Prod.fst s=signMass r s := by
  simp [Law.mass,shortSeedLaw,Fintype.sum_prod_type,← Finset.mul_sum,hsq]

theorem shortSeedLaw_independent {E : Type} [Fintype E] {r : ℕ}
    (q : E → ℝ) (hq : ∀ e,0 ≤ q e) (hsq : ∑ e,q e=1) :
    (shortSeedLaw (r:=r) q hq hsq).Independent Prod.fst Prod.snd := by
  intro s e
  rw [shortSeedLaw_source]
  simp [Law.mass,shortSeedLaw,Fintype.sum_prod_type,← Finset.sum_mul,signMass_total]

theorem shortSeedLaw_event_ge {E : Type} [Fintype E] {r : ℕ}
    (q : E → ℝ) (hq : ∀ e,0 ≤ q e) (hsq : ∑ e,q e=1)
    (F : Signs r × E → Prop) [DecidablePred F] (a : ℝ)
    (hF : ∀ s,a ≤ Sampling.eventMass q (Finset.univ.filter (fun e => F (s,e)))) :
    a ≤ Sampling.eventMass (shortSeedLaw q hq hsq).weight (Finset.univ.filter F) := by
  calc
    a = ∑ s : Signs r,signMass r s*a := by rw [← Finset.sum_mul,signMass_total,one_mul]
    _ ≤ ∑ s : Signs r,signMass r s*Sampling.eventMass q (Finset.univ.filter (fun e => F (s,e))) :=
      Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hF s) (by unfold signMass; positivity))
    _ = _ := by
      simp only [Sampling.eventMass,Finset.sum_filter,Fintype.sum_prod_type,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro e _
      change signMass r s*(if F (s,e) then q e else 0)=if F (s,e) then signMass r s*q e else 0
      split_ifs <;> ring

/-- A .99 exact-recovery event gives the strict .04r decoding threshold. -/
theorem expected_hamming_of_exact_success {Ω : Type} [Fintype Ω] {r : ℕ}
    (P : Law Ω) (source estimate : Ω → Signs r) (F : Ω → Prop) [DecidablePred F]
    (hr : 1 ≤ r) (hsuccess : (99/100:ℝ) ≤ Sampling.eventMass P.weight (Finset.univ.filter F))
    (hgood : ∀ ω,F ω → estimate ω=source ω) :
    (∑ ω,P.weight ω*RateDistortion.hamming (source ω) (estimate ω)) < (1/25:ℝ)*r := by
  have hfail : Sampling.eventMass P.weight (Finset.univ.filter (fun ω => ¬F ω)) ≤ (1/100:ℝ) := by
    have hh := finite_event_complement P F
    linarith
  have hpoint (ω : Ω) : RateDistortion.hamming (source ω) (estimate ω) ≤ if F ω then 0 else (r:ℝ) := by
    by_cases hf : F ω
    · simp [hf,hgood ω hf,RateDistortion.hamming]
    · simp only [if_neg hf]; exact hamming_le_rank _ _
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun ω _ => mul_le_mul_of_nonneg_left (hpoint ω) (P.nonneg ω))
  have he : (∑ ω,P.weight ω*(if F ω then 0 else (r:ℝ))) =
      Sampling.eventMass P.weight (Finset.univ.filter (fun ω => ¬F ω))*r := by
    simp only [Sampling.eventMass,Finset.sum_filter,mul_ite,mul_zero,ite_not,Finset.sum_mul,ite_mul,zero_mul]
  rw [he] at hs
  have hm := mul_le_mul_of_nonneg_right hfail (Nat.cast_nonneg r)
  have hr0 : (0:ℝ)<r := by exact_mod_cast hr
  linarith

end Paper29.HardDistribution
