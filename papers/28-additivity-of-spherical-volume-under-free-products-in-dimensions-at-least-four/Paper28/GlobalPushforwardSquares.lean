import Paper28.GlobalCurrentPushforwardInput

/-! Native consequences of canonical AK functoriality for a commuting
square and for a composition constant on the actual current support. -/
set_option autoImplicit false
noncomputable section
namespace Paper28

def hasGlobalLipschitz_comp {X Y Z : Type} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
    {f : X → Y} {g : Y → Z} (hf : ∃ L : NNReal, LipschitzWith L f) (hg : ∃ L : NNReal, LipschitzWith L g) :
    ∃ L : NNReal, LipschitzWith L (g ∘ f) := by
  obtain ⟨L,hL⟩ := hf
  obtain ⟨K,hK⟩ := hg
  exact ⟨K*L,hK.comp hL⟩

theorem globalCurrentPush_square (F : CanonicalGlobalCurrentCalculusInput)
    {X Y Z W : Type} [mX : MetricSpace X] [mY : MetricSpace Y] [mZ : MetricSpace Z] [mW : MetricSpace W]
    (I : CompactIntegralCurrentAlgebraInput.{0,0} X mX) (J : CompactIntegralCurrentAlgebraInput.{0,0} Y mY)
    (K : CompactIntegralCurrentAlgebraInput.{0,0} Z mZ) (L : CompactIntegralCurrentAlgebraInput.{0,0} W mW)
    (f : X → Y) (g : Y → Z) (f' : X → W) (g' : W → Z)
    (hf : ∃ L : NNReal, LipschitzWith L f) (hg : ∃ L : NNReal, LipschitzWith L g)
    (hf' : ∃ L : NNReal, LipschitzWith L f') (hg' : ∃ L : NNReal, LipschitzWith L g')
    (he : g ∘ f = g' ∘ f') (n : ℕ) (C : I.Current n) :
    (F.map J K g hg).push n ((F.map I J f hf).push n C) =
      (F.map L K g' hg').push n ((F.map I L f' hf').push n C) := by
  exact (F.composition I J K f g hf hg (hasGlobalLipschitz_comp hf hg) n C).trans
    ((congrArg (fun h => h C) (globalCurrentPushforward_congr F I K _ _
      (hasGlobalLipschitz_comp hf hg) (hasGlobalLipschitz_comp hf' hg') he n)).trans
      (F.composition I L K f' g' hf' hg' (hasGlobalLipschitz_comp hf' hg') n C).symm)

theorem globalCurrentPush_composition_constant_zero (F : CanonicalGlobalCurrentCalculusInput)
    {X Y Z : Type} [mX : MetricSpace X] [mY : MetricSpace Y] [mZ : MetricSpace Z]
    (I : CompactIntegralCurrentAlgebraInput.{0,0} X mX) (J : CompactIntegralCurrentAlgebraInput.{0,0} Y mY)
    (K : CompactIntegralCurrentAlgebraInput.{0,0} Z mZ) (Faithful : CurrentMassFaithfulnessInput K)
    (f : X → Y) (g : Y → Z)
    (hf : ∃ L : NNReal, LipschitzWith L f) (hg : ∃ L : NNReal, LipschitzWith L g)
    (k : ℕ) (C : I.Current (k+1)) (c : Z) (he : ∀ x ∈ I.support C, g (f x) = c) :
    (F.map J K g hg).push (k+1) ((F.map I J f hf).push (k+1) C) = 0 := by
  rw [F.composition I J K f g hf hg (hasGlobalLipschitz_comp hf hg)]
  exact globalCurrentPushforward_constant_zero _ Faithful k C c he

end Paper28
