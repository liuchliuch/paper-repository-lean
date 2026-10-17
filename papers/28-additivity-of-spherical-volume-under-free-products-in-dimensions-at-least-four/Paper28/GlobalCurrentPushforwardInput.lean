import Paper28.NeighborhoodPushforwardInput
import Paper28.CurrentLocalityInputs

/-! Generic canonical AK pushforwards for globally Lipschitz maps, with
their ordinary support, individual mass, boundary and composition laws.
No shadow, tree, finite summation, transfer or joint mass bound is a field.
-/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set

structure GlobalCurrentPushforwardInput
    {X Y : Type} (metricX : MetricSpace X) (metricY : MetricSpace Y)
    (I : CompactIntegralCurrentAlgebraInput.{0,0} X metricX)
    (J : CompactIntegralCurrentAlgebraInput.{0,0} Y metricY) (f : X → Y) where
  push : ∀ k, I.Current k →+ J.Current k
  boundary_comm : ∀ k (C : I.Current (k+1)), J.boundary k (push (k+1) C) = push k (I.boundary k C)
  support_subset : ∀ k (C : I.Current k), J.support (push k C) ⊆ f '' I.support C
  mass_lipschitz_le : ∀ k (C : I.Current k) (L : NNReal),
    (letI := metricX; letI := metricY; LipschitzOnWith L f (I.support C)) →
      J.mass (push k C) ≤ (L : ℝ)^k*I.mass C

structure CanonicalGlobalCurrentCalculusInput where
  map : ∀ {X Y : Type} [metricX : MetricSpace X] [metricY : MetricSpace Y]
    (I : CompactIntegralCurrentAlgebraInput.{0,0} X metricX)
    (J : CompactIntegralCurrentAlgebraInput.{0,0} Y metricY)
    (f : X → Y) (hf : ∃ L : NNReal, LipschitzWith L f), GlobalCurrentPushforwardInput metricX metricY I J f
  composition : ∀ {X Y Z : Type} [metricX : MetricSpace X] [metricY : MetricSpace Y] [metricZ : MetricSpace Z]
    (I : CompactIntegralCurrentAlgebraInput.{0,0} X metricX)
    (J : CompactIntegralCurrentAlgebraInput.{0,0} Y metricY)
    (K : CompactIntegralCurrentAlgebraInput.{0,0} Z metricZ)
    (f : X → Y) (g : Y → Z) (hf : ∃ L : NNReal, LipschitzWith L f)
    (hg : ∃ L : NNReal, LipschitzWith L g) (hgf : ∃ L : NNReal, LipschitzWith L (g ∘ f))
    (k : ℕ) (C : I.Current k),
      (map J K g hg).push k ((map I J f hf).push k C) = (map I K (g ∘ f) hgf).push k C
  identity : ∀ {X : Type} [metricX : MetricSpace X]
    (I : CompactIntegralCurrentAlgebraInput.{0,0} X metricX)
    (hf : ∃ L : NNReal, LipschitzWith L (id : X → X)) (k : ℕ) (C : I.Current k),
      (map I I id hf).push k C = C

theorem globalCurrentPushforward_congr (F : CanonicalGlobalCurrentCalculusInput)
    {X Y : Type} [metricX : MetricSpace X] [metricY : MetricSpace Y]
    (I : CompactIntegralCurrentAlgebraInput.{0,0} X metricX)
    (J : CompactIntegralCurrentAlgebraInput.{0,0} Y metricY)
    (f g : X → Y) (hf : ∃ L : NNReal, LipschitzWith L f) (hg : ∃ L : NNReal, LipschitzWith L g)
    (he : f = g) (k : ℕ) : (F.map I J f hf).push k = (F.map I J g hg).push k := by
  subst g
  rfl

theorem globalCurrentPushforward_constant_zero
    {X Y : Type} {metricX : MetricSpace X} {metricY : MetricSpace Y}
    {I : CompactIntegralCurrentAlgebraInput.{0,0} X metricX}
    {J : CompactIntegralCurrentAlgebraInput.{0,0} Y metricY} {f : X → Y}
    (P : GlobalCurrentPushforwardInput metricX metricY I J f) (Faithful : CurrentMassFaithfulnessInput J)
    (k : ℕ) (C : I.Current (k+1)) (c : Y) (hf : ∀ x ∈ I.support C, f x = c) : P.push (k+1) C = 0 := by
  apply Faithful.eq_zero_of_mass_zero
  have hLip : letI := metricX; letI := metricY; LipschitzOnWith 0 f (I.support C) := by
    letI := metricX
    letI := metricY
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [hf x hx,hf y hy,dist_self]
    simp
  have hM := P.mass_lipschitz_le (k+1) C 0 hLip
  simp only [NNReal.coe_zero,zero_pow (Nat.succ_ne_zero k),zero_mul] at hM
  exact le_antisymm hM (J.mass_nonneg _)

end Paper28
