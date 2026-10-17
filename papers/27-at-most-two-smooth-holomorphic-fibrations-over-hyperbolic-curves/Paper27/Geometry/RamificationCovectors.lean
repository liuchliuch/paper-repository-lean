import Paper27.Geometry.DifferentialRigidity
import Paper27.Geometry.Factorization
import Mathlib.Analysis.Analytic.Order

/-!
# Covectors and normalization maps on a ramification component

Failure of surjectivity of the actual joint differential forces the two
surjective covectors to have the same kernel. Its unique nonzero proportionality
factor is obtained by the proved linear algebra in `DifferentialRigidity`.
For actual maps of compact complex manifolds, finite pair fibres rule out a
nonconstant curve map on which both projections are constant. Finally, the
analytic derivative-order comparison uses Mathlib's actual analytic orders and
the multiplicative order theorem; no ramification divisor is supplied as a
label or assumed equal here.
-/

noncomputable section

open scoped Manifold Topology
open Filter

namespace Paper27.Geometry.RamificationCovectors

section Covectors

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A vector on which only the second covector is nonzero, together with an
`l₁`-unit vector, explicitly gives every prescribed pair of values. -/
theorem joint_surjective_of_kernel_vector (l₁ l₂ : V →ₗ[ℂ] ℂ)
    (h₁ : Function.Surjective l₁) (v : V) (hv₁ : l₁ v = 0) (hv₂ : l₂ v ≠ 0) :
    Function.Surjective (fun w : V => (l₁ w, l₂ w)) := by
  obtain ⟨e, he⟩ := h₁ 1
  intro ab
  refine ⟨ab.1 • e + ((ab.2 - ab.1 * l₂ e) / l₂ v) • v, ?_⟩
  apply Prod.ext
  · simp [map_add, map_smul, he, hv₁, smul_eq_mul]
  · simp only [map_add, map_smul, smul_eq_mul]
    rw [div_mul_cancel₀ _ hv₂]
    ring

/-- Non-surjectivity of the joint covector forces vanishing on the first
kernel. No finite dimensionality assumption is needed. -/
theorem kernel_vanishes_of_joint_not_surjective (l₁ l₂ : V →ₗ[ℂ] ℂ)
    (h₁ : Function.Surjective l₁)
    (hjoint : ¬ Function.Surjective (fun w : V => (l₁ w, l₂ w))) :
    ∀ v : V, l₁ v = 0 → l₂ v = 0 := by
  intro v hv₁
  by_contra hv₂
  exact hjoint (joint_surjective_of_kernel_vector l₁ l₂ h₁ v hv₁ hv₂)

/-- The graph slope of the pair is genuinely unique and nonzero when both
individual maps are onto and their joint map is not onto. -/
theorem existsUnique_nonzero_slope (l₁ l₂ : V →ₗ[ℂ] ℂ)
    (h₁ : Function.Surjective l₁) (h₂ : Function.Surjective l₂)
    (hjoint : ¬ Function.Surjective (fun w : V => (l₁ w, l₂ w))) :
    ∃! a : ℂ, a ≠ 0 ∧ ∀ v : V, l₂ v = a * l₁ v := by
  obtain ⟨a, ha0, ha⟩ := DifferentialRigidity.exists_nonzero_scalar l₁ l₂ h₁ h₂
    (kernel_vanishes_of_joint_not_surjective l₁ l₂ h₁ hjoint)
  refine ⟨a, ⟨ha0, ha⟩, ?_⟩
  intro b hb
  apply DifferentialRigidity.scalar_unique l₁ h₁
  intro v
  exact (hb.2 v).symm.trans (ha v)

/-- In particular the two actual kernels coincide. -/
theorem kernels_equal_of_joint_not_surjective (l₁ l₂ : V →ₗ[ℂ] ℂ)
    (h₁ : Function.Surjective l₁) (h₂ : Function.Surjective l₂)
    (hjoint : ¬ Function.Surjective (fun w : V => (l₁ w, l₂ w))) :
    LinearMap.ker l₁ = LinearMap.ker l₂ := by
  obtain ⟨a, ⟨ha0, ha⟩, hunique⟩ := existsUnique_nonzero_slope l₁ l₂ h₁ h₂ hjoint
  ext v
  simp only [LinearMap.mem_ker]
  rw [ha v, mul_eq_zero]
  simp [ha0]

end Covectors

section CurveMaps

variable {X : CompactComplexSurface}

/-- The range of a continuous map from a connected space is finite when both
its projections land in one finite pair fibre; hence it is a single point. -/
theorem continuous_map_constant_of_constant_projections
    {S : Type*} [TopologicalSpace S] [PreconnectedSpace S]
    (ν : S → X) (hν : Continuous ν) (s₀ : S)
    (f g : Fibration X) (hfinite : Fibration.FinitePair f g)
    (hf : ∀ s, f (ν s) = f (ν s₀))
    (hg : ∀ s, g (ν s) = g (ν s₀)) : ∀ s, ν s = ν s₀ := by
  have hrange : (Set.range ν).Finite := by
    apply (hfinite (f (ν s₀), g (ν s₀))).subset
    rintro x ⟨s, rfl⟩
    exact ⟨hf s, hg s⟩
  have hconnected : IsPreconnected (Set.range ν) := by
    simpa only [Set.image_univ] using isPreconnected_univ.image ν hν.continuousOn
  have hsub := finite_preconnected_subsingleton hrange hconnected
  intro s
  exact hsub ⟨s, rfl⟩ ⟨s₀, rfl⟩

/-- The specialization to the actual holomorphic normalization map of a curve
into the actual compact complex surface. -/
theorem curve_map_constant_of_constant_projections (D : Curve)
    (ν : HolomorphicMap D X) (f g : Fibration X) (hfinite : Fibration.FinitePair f g)
    (hf : ∃ b : f.base, ∀ p : D, f (ν p) = b)
    (hg : ∃ c : g.base, ∀ p : D, g (ν p) = c) :
    ∀ p : D, ν p = ν D.basepoint := by
  obtain ⟨b, hb⟩ := hf
  obtain ⟨c, hc⟩ := hg
  exact continuous_map_constant_of_constant_projections ν ν.holomorphic.continuous D.basepoint
    f g hfinite (fun p => (hb p).trans (hb D.basepoint).symm)
    (fun p => (hc p).trans (hc D.basepoint).symm)

/-- A nonconstant actual curve map cannot have both projections constant. -/
theorem one_projection_nonconstant (D : Curve) (ν : HolomorphicMap D X)
    (f g : Fibration X) (hfinite : Fibration.FinitePair f g)
    (hν : ∃ p q : D, ν p ≠ ν q) :
    (∃ p q : D, f (ν p) ≠ f (ν q)) ∨ (∃ p q : D, g (ν p) ≠ g (ν q)) := by
  by_cases hf : ∃ p q : D, f (ν p) ≠ f (ν q)
  · exact Or.inl hf
  right
  by_contra hg
  have hfconst : ∀ p : D, f (ν p) = f (ν D.basepoint) := by
    intro p
    by_contra hp
    exact hf ⟨p, D.basepoint, hp⟩
  have hgconst : ∀ p : D, g (ν p) = g (ν D.basepoint) := by
    intro p
    by_contra hp
    exact hg ⟨p, D.basepoint, hp⟩
  have hconstant := continuous_map_constant_of_constant_projections ν ν.holomorphic.continuous
    D.basepoint f g hfinite hfconst hgconst
  obtain ⟨p, q, hpq⟩ := hν
  exact hpq ((hconstant p).trans (hconstant q).symm)

end CurveMaps

section AnalyticOrders

/-- Multiplication by an analytic unit preserves the actual analytic order,
including the infinite-order case. -/
theorem analyticOrderAt_mul_unit {unit f : ℂ → ℂ} {z₀ : ℂ}
    (hunit : AnalyticAt ℂ unit z₀) (hf : AnalyticAt ℂ f z₀) (hne : unit z₀ ≠ 0) :
    analyticOrderAt (unit * f) z₀ = analyticOrderAt f z₀ := by
  rw [analyticOrderAt_mul hunit hf, hunit.analyticOrderAt_eq_zero.mpr hne, zero_add]

/-- The unit relation need only hold as an analytic germ, as is the case for
coordinate expressions of derivatives on the normalized ramification curve. -/
theorem analyticOrderAt_eq_of_unit_mul_germ {unit f g : ℂ → ℂ} {z₀ : ℂ}
    (hunit : AnalyticAt ℂ unit z₀) (hf : AnalyticAt ℂ f z₀) (hne : unit z₀ ≠ 0)
    (hg : g =ᶠ[𝓝 z₀] unit * f) : analyticOrderAt g z₀ = analyticOrderAt f z₀ := by
  exact (analyticOrderAt_congr hg).trans (analyticOrderAt_mul_unit hunit hf hne)

/-- The same equality in the exact natural-order convention used by
`MetricComparison.ramificationOrder`; no finiteness assumption is lost here. -/
theorem analyticOrderNatAt_eq_of_unit_mul_germ {unit f g : ℂ → ℂ} {z₀ : ℂ}
    (hunit : AnalyticAt ℂ unit z₀) (hf : AnalyticAt ℂ f z₀) (hne : unit z₀ ≠ 0)
    (hg : g =ᶠ[𝓝 z₀] unit * f) :
    analyticOrderNatAt g z₀ = analyticOrderNatAt f z₀ := by
  unfold analyticOrderNatAt
  rw [analyticOrderAt_eq_of_unit_mul_germ hunit hf hne hg]

/-- A relation `v' = unit * u'` implies equality of the actual vanishing orders
of the two derivatives. This is directly applicable after unfolding the actual
coordinate-derivative definition of curve-map ramification order. -/
theorem derivative_orders_eq_of_unit_relation {u v unit : ℂ → ℂ} {z₀ : ℂ}
    (hunit : AnalyticAt ℂ unit z₀) (hu : AnalyticAt ℂ (deriv u) z₀)
    (hne : unit z₀ ≠ 0) (hderiv : deriv v =ᶠ[𝓝 z₀] unit * deriv u) :
    analyticOrderNatAt (deriv v) z₀ = analyticOrderNatAt (deriv u) z₀ :=
  analyticOrderNatAt_eq_of_unit_mul_germ hunit hu hne hderiv

end AnalyticOrders

end Paper27.Geometry.RamificationCovectors
