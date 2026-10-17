import Paper29.ProductObservation
import Paper29.BernoulliInformation

noncomputable section
open scoped BigOperators Classical
namespace Paper29.Transcript.ProductObservation

variable {S I E : Type} [Fintype S] [Fintype I] [Fintype E] [DecidableEq I]
    (θ : S → ℝ) (hθ : ∀ s, 0 ≤ θ s) (hsθ : ∑ s,θ s=1)
    (q : E → ℝ) (hq : ∀ e, 0 ≤ q e) (hsq : ∑ e,q e=1)
    (p : S → I → Bool → ℝ) (hp : ∀ s i b, 0 ≤ p s i b) (hsp : ∀ s i,∑ b,p s i b=1)

local notation "P" => productObservationLaw θ hθ hsθ q hq hsq p hp hsp

/-- At an active history, the complete source/selected-bit conditional channel
is still the original Bernoulli channel. This is derived from fresh history
fibers and the actual product distribution, not assumed as a Markov premise. -/
theorem fresh_joint_mass_of_invariant {H : Type} [Fintype H]
    (history : E → (I → Bool) → H) (h : H) (j : I)
    (hinv : ∀ e y v, history e (Function.update y j v)=h ↔ history e y=h) (s : S) (b : Bool) :
    (P).mass (fun ω => ((ω.1,ω.2.1 j),history ω.2.2 ω.2.1)) ((s,b),h) =
      p s j b * (P).mass (fun ω => (ω.1,history ω.2.2 ω.2.1)) (s,h) := by
  have hbit (e : E) :
      (∑ y : I → Bool, (∏ i,p s i (y i))*(if history e y=h then 1 else 0)*
        (if y j=b then 1 else 0)) =
      p s j b*(∑ y : I → Bool, (∏ i,p s i (y i))*(if history e y=h then 1 else 0)) := by
    have hh := Sampling.product_fresh_coordinate (p s) j (hsp s j)
      (fun y => if history e y=h then 1 else 0) (by
        intro y v
        simp only [hinv e y v]) (fun v => if v=b then 1 else 0)
    simpa using hh
  unfold Law.mass
  simp only [Fintype.sum_prod_type,Prod.mk.injEq,ite_and]
  simp only [productObservationLaw]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  have hs (e : E) :
      (∑ y : I → Bool, if y j=b then if history e y=h then θ s*(∏ i,p s i (y i))*q e else 0 else 0) =
      p s j b*(∑ y : I → Bool, if history e y=h then θ s*(∏ i,p s i (y i))*q e else 0) := by
    have hh := congrArg (fun x : ℝ => θ s*q e*x) (hbit e)
    simp only [Finset.mul_sum] at hh
    rw [Finset.mul_sum]
    convert hh using 1 <;> apply Finset.sum_congr rfl <;> intro y _ <;>
      split_ifs <;> ring
  calc
    _ = ∑ y : I → Bool, ∑ e : E,
        if y j=b then if history e y=h then θ s*(∏ i,p s i (y i))*q e else 0 else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y j=b <;> simp [hy]
    _ = ∑ e : E, ∑ y : I → Bool,
        if y j=b then if history e y=h then θ s*(∏ i,p s i (y i))*q e else 0 else 0 := Finset.sum_comm
    _ = ∑ e : E, p s j b*(∑ y : I → Bool,
        if history e y=h then θ s*(∏ i,p s i (y i))*q e else 0) := by
      exact Finset.sum_congr rfl (fun e _ => hs e)
    _ = p s j b*(∑ e : E,∑ y : I → Bool,
        if history e y=h then θ s*(∏ i,p s i (y i))*q e else 0) := (Finset.mul_sum _ _ _).symm
    _ = _ := by rw [Finset.sum_comm]

theorem fresh_joint_mass (policy : Policy E I Bool) (t : ℕ) (h : History E I Bool t)
    (j : I) (hchoose : policy.choose t h=some j) (s : S) (b : Bool) :
    (P).mass (fun ω => ((ω.1,ω.2.1 j),policy.history ω.2.2 ω.2.1 t)) ((s,b),h) =
      p s j b * (P).mass (fun ω => (ω.1,policy.history ω.2.2 ω.2.1 t)) (s,h) :=
  fresh_joint_mass_of_invariant θ hθ hsθ q hq hsq p hp hsp
    (fun e y => policy.history e y t) h j
    (fun e y v => policy.history_fiber_update e y t h j v hchoose) s b

/-- The actual regular conditional law satisfies the selected-bit channel
factorization, including source posterior normalization. -/
theorem conditional_fresh_channel (policy : Policy E I Bool) (t : ℕ) (h : History E I Bool t)
    (j : I) (hchoose : policy.choose t h=some j)
    (hh : 0 < (P).mass (fun ω => policy.history ω.2.2 ω.2.1 t) h) (s : S) (b : Bool) :
    ((P).condition (fun ω => policy.history ω.2.2 ω.2.1 t) h hh).mass
        (fun ω => (ω.1,ω.2.1 j)) (s,b) =
      ((P).condition (fun ω => policy.history ω.2.2 ω.2.1 t) h hh).mass Prod.fst s * p s j b := by
  rw [Law.mass_condition,Law.mass_condition,
    fresh_joint_mass θ hθ hsθ q hq hsq p hp hsp policy t h j hchoose]
  ring

/-- Fully derived fresh-response information bound under the actual adaptive
posterior, uniformly over the prior and independent finite private seed. -/
theorem local_fresh_information_bound (policy : Policy E I Bool) (t : ℕ) (h : History E I Bool t)
    (j : I) (hchoose : policy.choose t h=some j)
    (hh : 0 < (P).mass (fun ω => policy.history ω.2.2 ω.2.1 t) h)
    (σ : S → Bool) (β : ℝ) (hβ : 0 ≤ β) (hβhi : β ≤ 1/4)
    (hform : ∀ s b, p s j b = HardDistribution.bitMass (1/2+β*HardDistribution.sign (σ s)) b) :
    (P).localInformation Prod.fst (fun ω => ω.2.1 j)
      (fun ω => policy.history ω.2.2 ω.2.1 t) h ≤ 16*β^2 := by
  rw [Law.localInformation_eq_condition_information _ _ _ _ _ hh]
  let Q := (P).condition (fun ω => policy.history ω.2.2 ω.2.1 t) h hh
  have hc : ∀ s b, Q.mass (fun ω => (ω.1,ω.2.1 j)) (s,b) =
      Q.mass Prod.fst s * HardDistribution.bitMass (1/2+β*HardDistribution.sign (σ s)) b := by
    intro s b
    rw [conditional_fresh_channel θ hθ hsθ q hq hsq p hp hsp policy t h j hchoose hh,hform]
  exact Law.biased_bit_information_le Q Prod.fst (fun ω => ω.2.1 j) σ β hβ hβhi hc

end Paper29.Transcript.ProductObservation
