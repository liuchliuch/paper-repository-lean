import Paper38.GradientWithin

/-! Energy dissipation with physical-time right-domain derivatives. -/
noncomputable section
namespace Paper38.WithinEnergyDecay
open Set Real
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem energy_exponential_decay {F : E → ℝ} {G : E → E}
    {P : E → E →L[ℝ] E} {q : ℝ → E} {Ω : Set E} {z : E}
    {α p t : ℝ} (hα : 0 < α) (hp : 0 ≤ p) (ht : 0 ≤ t)
    (hstrong : EnergyDecay.StrongConvexGradientOn F G Ω α) (hz : z ∈ Ω)
    (hF : ∀ x ∈ Ω, HasFDerivAt F (innerSL ℝ (G x)) x)
    (hq : ∀ s, 0 ≤ s → HasDerivWithinAt q (-(P (q s) (G (q s)))) (Ici 0) s)
    (hqΩ : ∀ s, 0 ≤ s → q s ∈ Ω)
    (hP : ∀ s, 0 ≤ s → ∀ v : E, p * ‖v‖^2 ≤ ⟪v, P (q s) v⟫_ℝ) :
    F (q t)-F z ≤ (F (q 0)-F z) * exp (-2*α*p*t) := by
  have hd : ∀ s, 0 ≤ s → HasDerivWithinAt (fun s => F (q s)-F z)
      (-⟪G (q s),P (q s) (G (q s))⟫_ℝ) (Ici 0) s := by
    intro s hs
    simpa using ((hF _ (hqΩ s hs)).comp_hasDerivWithinAt s (hq s hs)).sub_const (F z)
  have hbound : ∀ s ∈ Ico 0 t,
      -⟪G (q s),P (q s) (G (q s))⟫_ℝ ≤ (-2*α*p)*(F (q s)-F z) := by
    intro s hs
    have hpl := EnergyDecay.polyak_lojasiewicz hα hstrong hz (hqΩ s hs.1)
    have hell := hP s hs.1 (G (q s))
    have hmul := mul_le_mul_of_nonneg_left hpl hp
    nlinarith
  simpa only [sub_zero, mul_assoc] using Stability.scalar_exp_bound
    (fun s hs => (hd s hs.1).continuousWithinAt.mono (fun u hu => hu.1))
    (fun s hs => (hd s hs.1).mono (fun u hu => hs.1.trans hu)) hbound ht
end Paper38.WithinEnergyDecay
