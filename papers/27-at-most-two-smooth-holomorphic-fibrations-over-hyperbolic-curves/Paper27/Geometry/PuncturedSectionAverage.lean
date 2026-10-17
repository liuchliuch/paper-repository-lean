import Paper27.Geometry.PuncturedSplittingSections

/-!
# Actual differential averages on the punctured neighbourhood

The action on sections is constructed by restricting the actual neighbourhood
permutations to U minus D and using their actual differentials. Projection is
equivariant at inverse-image points. In particular the actual finite average
and the actual formula (6) remain splittings.
-/
noncomputable section
open scoped Manifold Topology BigOperators
open Filter Finset

namespace Paper27.Geometry.PuncturedSplittingSections
open NeighbourhoodSplittings
variable {X : CompactComplexSurface} {D : EmbeddedCurve X} {U : D.Neighbourhood}
  {r : D.Retraction U} {G : Type} [Group G]

namespace NeighbourhoodAction
variable (A : NeighbourhoodSplittings.NeighbourhoodAction G r)
  (hfix : ∀ g : G, ∀ p : D.curve, A.permutation g (curvePoint U p) = curvePoint U p)
include hfix

 theorem support_iff (g : G) (p : U.domain) :
    (A.permutation g p).val ∈ D.support ↔ p.val ∈ D.support := by
  constructor
  · rintro ⟨q, hq⟩
    have heq : A.permutation g p = A.permutation g (curvePoint U q) := by
      rw [hfix]
      exact Subtype.ext hq.symm
    have hp := congrArg Subtype.val ((A.permutation g).injective heq)
    exact ⟨q, hp.symm⟩
  · rintro ⟨q, hq⟩
    have hp : p = curvePoint U q := Subtype.ext hq.symm
    rw [hp, hfix]
    exact ⟨q, rfl⟩

/-- The honest permutation action restricted to the actual punctured domain. -/
def puncturePermutation : G →* Equiv.Perm (Point D U) where
  toFun g := (A.permutation g).subtypeEquiv
    (fun p => (not_congr (support_iff A hfix g p)).symm)
  map_one' := by ext p; change (A.permutation 1 p.val).val = p.val.val; rw [map_one]; rfl
  map_mul' g h := by ext p; change (A.permutation (g * h) p.val).val = _; rw [map_mul]; rfl

 theorem puncturePermutation_val (g : G) (p : Point D U) :
    (puncturePermutation A hfix g p).val = A.permutation g p.val := rfl

/-- Pushforward is the actual derivative at the actual inverse-image point. -/
def pushforward (g : G) (σ : Section D U) : Section D U := fun p =>
  (A.derivative g (A.permutation (g⁻¹) p.val)).comp
    (σ (puncturePermutation A hfix (g⁻¹) p))

 theorem projection_pushforward (g : G) (σ : Section D U) (p : Point D U) :
    (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) r.toFun p.val.val).comp (pushforward A hfix g σ p) =
      (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) r.toFun
        (puncturePermutation A hfix (g⁻¹) p).val.val).comp
          (σ (puncturePermutation A hfix (g⁻¹) p)) := by
  apply ContinuousLinearMap.ext
  intro w
  have heq := congrArg (fun L : (ℂ × ℂ) →L[ℂ] ℂ =>
    L (σ (puncturePermutation A hfix (g⁻¹) p) w))
      (A.retraction_derivative g (A.permutation (g⁻¹) p.val))
  have hforw := A.forward_inverse_image g p.val
  rw [hforw] at heq
  exact heq

 theorem pushforward_splitting (g : G) (σ : Section D U) (hs : IsSplitting r σ) :
    IsSplitting r (pushforward A hfix g σ) := by
  intro p
  rw [projection_pushforward A hfix, hs]

 def pushforwardLinear (g : G) : Section D U →ₗ[ℂ] Section D U where
  toFun := pushforward A hfix g
  map_add' σ τ := by funext p; simp [pushforward]
  map_smul' a σ := by funext p; simp [pushforward]

/-- The finite cyclic differential average, with actual section summands. -/
def powerAverage (n : ℕ) (g : G) (σ : Section D U) : Section D U :=
  (n : ℂ)⁻¹ • ∑ j ∈ range n, pushforward A hfix (g ^ j) σ

 theorem powerAverage_splitting {n : ℕ} (hn : 0 < n) (g : G)
    (σ : Section D U) (hs : IsSplitting r σ) : IsSplitting r (powerAverage A hfix n g σ) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  intro p
  have hterm (j : ℕ) :
      (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) r.toFun p.val.val).comp
        (pushforward A hfix (g ^ j) σ p) = ContinuousLinearMap.id ℂ ℂ :=
    pushforward_splitting A hfix (g ^ j) σ hs p
  have htermValue (j : ℕ) (w : ℂ) :
      mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) r.toFun p.val.val
        (pushforward A hfix (g ^ j) σ p w) = w :=
    congrArg (fun L : ℂ →L[ℂ] ℂ => L w) (hterm j)
  apply ContinuousLinearMap.ext
  intro w
  change mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) r.toFun p.val.val
    (powerAverage A hfix n g σ p w) = w
  simp only [powerAverage, Pi.smul_apply, Finset.sum_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    map_smul, map_sum, htermValue, Finset.sum_const, Finset.card_range]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hnC, one_smul]

/-- The actual global section in equation (6), on U minus D. -/
def formulaSix (n : ℕ) (g : G) (a : ℂ) (σ₂ σ₃ : Section D U) : Section D U :=
  (a - 1)⁻¹ • (a • powerAverage A hfix n g σ₃ - σ₂)

 theorem formulaSix_splitting {n : ℕ} (hn : 0 < n) (g : G) (a : ℂ) (ha : a ≠ 1)
    (σ₂ σ₃ : Section D U) (h₂ : IsSplitting r σ₂) (h₃ : IsSplitting r σ₃) :
    IsSplitting r (formulaSix A hfix n g a σ₂ σ₃) := by
  intro p
  unfold formulaSix
  simp only [Pi.smul_apply, Pi.sub_apply, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.comp_sub, h₂ p, powerAverage_splitting A hfix hn g σ₃ h₃ p]
  have heq : a • (ContinuousLinearMap.id ℂ ℂ) - ContinuousLinearMap.id ℂ ℂ =
      (a - 1) • ContinuousLinearMap.id ℂ ℂ := by
    apply ContinuousLinearMap.ext
    intro w
    change a * w - w = (a - 1) * w
    ring
  rw [heq, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr ha), one_smul]

end NeighbourhoodAction
end Paper27.Geometry.PuncturedSplittingSections
