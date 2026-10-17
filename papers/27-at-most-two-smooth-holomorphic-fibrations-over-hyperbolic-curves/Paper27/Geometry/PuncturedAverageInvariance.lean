import Paper27.Geometry.PuncturedSectionAverage

/-!
# Invariance of the actual punctured formula-(6) section

Actual differential pushforwards form a representation. Cyclic sums are
invariant, and preservation of the second retraction fixes its actual joint
inverse. Therefore the actual affine section in formula (6) is invariant.
-/
noncomputable section
open scoped Manifold Topology BigOperators
open Filter Finset
namespace Paper27.Geometry.PuncturedSplittingSections
open NeighbourhoodSplittings
variable {X : CompactComplexSurface} {D : EmbeddedCurve X} {U : D.Neighbourhood}
  {r s : D.Retraction U} {G : Type} [Group G]

/-- Zero extension is used only to compare algebraic action laws. -/
def zeroExtension (σ : Section D U) : NeighbourhoodSplittings.Section U :=
  fun p => evaluation p.val σ

theorem restrict_zeroExtension (σ : Section D U) : restrict (zeroExtension σ) = σ := by
  funext p
  exact evaluation_apply σ p.val.property p.property

namespace NeighbourhoodAction
variable (A : NeighbourhoodSplittings.NeighbourhoodAction G r)
  (hfix : ∀ g p, A.permutation g (curvePoint U p) = curvePoint U p)
include hfix

theorem restrict_pushforward (g : G) (σ : NeighbourhoodSplittings.Section U) :
    restrict (A.pushforward g σ) = pushforward A hfix g (restrict σ) := rfl

theorem pushforward_one (σ : Section D U) : pushforward A hfix 1 σ = σ := by
  have h := congrArg (fun t : NeighbourhoodSplittings.Section U => restrict t)
    (A.pushforward_one (zeroExtension σ))
  simpa only [restrict_pushforward A hfix, restrict_zeroExtension] using h

theorem pushforward_mul (g h : G) (σ : Section D U) :
    pushforward A hfix (g * h) σ = pushforward A hfix g (pushforward A hfix h σ) := by
  have he := congrArg (fun t : NeighbourhoodSplittings.Section U => restrict t)
    (A.pushforward_mul g h (zeroExtension σ))
  simpa only [restrict_pushforward A hfix, restrict_zeroExtension] using he

/-- The actual pushforwards on U minus D form a linear group representation. -/
def representation : G →* Section D U ≃ₗ[ℂ] Section D U where
  toFun g :=
    { toFun := pushforward A hfix g
      invFun := pushforward A hfix (g⁻¹)
      left_inv := fun σ => by rw [← pushforward_mul, inv_mul_cancel, pushforward_one]
      right_inv := fun σ => by rw [← pushforward_mul, mul_inv_cancel, pushforward_one]
      map_add' := (pushforwardLinear A hfix g).map_add
      map_smul' := (pushforwardLinear A hfix g).map_smul }
  map_one' := by apply LinearEquiv.ext; exact pushforward_one A hfix
  map_mul' g h := by apply LinearEquiv.ext; exact pushforward_mul A hfix g h

theorem powerAverage_fixed {n : ℕ} (g : G) (hn : g ^ n = 1) (σ : Section D U) :
    pushforward A hfix g (powerAverage A hfix n g σ) = powerAverage A hfix n g σ := by
  let f : ℕ → Section D U := fun j => pushforward A hfix (g ^ j) σ
  have hf : f n = f 0 := by simp only [f, hn, pow_zero]
  have hsum : ∑ j ∈ range n, f (j + 1) = ∑ j ∈ range n, f j := by
    have hh := (Finset.sum_range_succ' f n).symm.trans (Finset.sum_range_succ f n)
    rw [hf] at hh
    exact add_right_cancel hh
  change (pushforwardLinear A hfix g)
    ((n : ℂ)⁻¹ • ∑ j ∈ range n, pushforward A hfix (g ^ j) σ) = _
  rw [map_smul, map_sum]
  change (n : ℂ)⁻¹ • ∑ j ∈ range n, pushforward A hfix g (pushforward A hfix (g ^ j) σ) = _
  simp only [← pushforward_mul, ← pow_succ']
  exact congrArg (fun t : Section D U => (n : ℂ)⁻¹ • t) hsum

omit hfix in
/-- Preservation of any actual retraction gives its actual chain-rule identity. -/
theorem preserved_retraction_derivative (s : D.Retraction U) (g : G)
    (hpres : ∀ p : U.domain, s.toFun (A.map g p.val) = s.toFun p.val)
    (p : U.domain) :
    (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) s.toFun (A.map g p.val)).comp
      (A.derivative g p) = mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) s.toFun p.val := by
  have heq : s.toFun ∘ A.map g =ᶠ[𝓝 p.val] s.toFun :=
    Filter.eventually_of_mem (U.open_domain.mem_nhds p.property)
      (fun x hx => hpres ⟨x, hx⟩)
  change (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) s.toFun (A.map g p.val)).comp
    (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) (A.map g) p.val) = _
  rw [← mfderiv_comp p.val
    ((s.holomorphic _ (A.map_mem g p)).mdifferentiableAt
      (U.open_domain.mem_nhds (A.map_mem g p))) (A.differentiableAt g p)]
  exact heq.mfderiv_eq

omit A hfix in
/-- The joint inverse is characterized by its actual projection and kernel. -/
theorem jointInverse_unique (s : D.Retraction U) (ht : JointTransverse r s)
    (σ : Section D U) (hs : IsSplitting r σ)
    (hk : ∀ p : Point D U, ∀ w : ℂ,
      mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) s.toFun p.val.val (σ p w) = 0) :
    σ = jointInverse r s ht := by
  funext p
  apply ContinuousLinearMap.ext
  intro w
  apply (ht p).injective
  apply Prod.ext
  · exact (congrArg (fun L : ℂ →L[ℂ] ℂ => L w) (hs p)).trans
      (congrArg (fun L : ℂ →L[ℂ] ℂ => L w) (jointInverse_splitting r s ht p)).symm
  · exact (hk p w).trans (jointInverse_kernel r s ht p w).symm

/-- The actual second splitting is fixed because the action preserves both
actual retractions. -/
theorem jointInverse_fixed (s : D.Retraction U) (ht : JointTransverse r s) (g : G)
    (hpres : ∀ p : U.domain, s.toFun (A.map g p.val) = s.toFun p.val) :
    pushforward A hfix g (jointInverse r s ht) = jointInverse r s ht := by
  apply jointInverse_unique s ht _
    (pushforward_splitting A hfix g _ (jointInverse_splitting r s ht))
  intro p w
  let q := puncturePermutation A hfix (g⁻¹) p
  have heq := congrArg (fun L : (ℂ × ℂ) →L[ℂ] ℂ => L (jointInverse r s ht q w))
    (preserved_retraction_derivative A s g hpres q.val)
  have hforw : A.map g q.val.val = p.val.val := A.forward_inverse_image g p.val
  rw [hforw] at heq
  exact heq.trans (jointInverse_kernel r s ht q w)

theorem formulaSix_fixed {n : ℕ} (g : G) (hn : g ^ n = 1) (a : ℂ)
    (σ₂ σ₃ : Section D U) (h₂ : pushforward A hfix g σ₂ = σ₂) :
    pushforward A hfix g (formulaSix A hfix n g a σ₂ σ₃) =
      formulaSix A hfix n g a σ₂ σ₃ := by
  change (pushforwardLinear A hfix g) ((a - 1)⁻¹ •
    (a • powerAverage A hfix n g σ₃ - σ₂)) = _
  rw [map_smul, map_sub, map_smul]
  change (a - 1)⁻¹ • (a • pushforward A hfix g (powerAverage A hfix n g σ₃) -
    pushforward A hfix g σ₂) = _
  rw [powerAverage_fixed A hfix g hn, h₂]
  rfl

end NeighbourhoodAction
end Paper27.Geometry.PuncturedSplittingSections
