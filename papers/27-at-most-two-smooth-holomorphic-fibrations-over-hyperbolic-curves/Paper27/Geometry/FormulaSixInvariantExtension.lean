import Paper27.Geometry.ActualFormulaSixObstruction
import Paper27.Geometry.PuncturedAverageInvariance

/-!
# Invariance of the actual regular extension of formula (6)

The invariant punctured section and its actual tangent value along D give
invariance of the regular extension as an actual section on the whole
neighbourhood. No invariance of that extension is an external assumption.
-/
noncomputable section
open scoped Manifold Topology
open Filter
namespace Paper27.Geometry.PuncturedSplittingSections.NeighbourhoodAction
open NeighbourhoodSplittings
variable {X : CompactComplexSurface} {D : EmbeddedCurve X} {U : D.Neighbourhood}
  {r : D.Retraction U} {G : Type} [Group G]
  (A : NeighbourhoodSplittings.NeighbourhoodAction G r)
  (hfix : ∀ g p, A.permutation g (curvePoint U p) = curvePoint U p)

/-- An invariant punctured section whose extension equals the actual inclusion
differential along the fixed curve has an invariant actual extension. -/
theorem extension_fixed (g : G) (σ : PuncturedSplittingSections.Section D U)
    (S : NeighbourhoodSplittings.Section U)
    (hres : PuncturedSplittingSections.restrict S = σ)
    (hinv : pushforward A hfix g σ = σ)
    (hvalue : ∀ p : D.curve, S (curvePoint U p) =
      mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ) D.inclusion p) : A.pushforward g S = S := by
  funext q
  by_cases hd : q.val ∈ D.support
  · obtain ⟨p, hp⟩ := hd
    have hq : q = curvePoint U p := Subtype.ext hp.symm
    subst q
    change (A.derivative g (A.permutation (g⁻¹) (curvePoint U p))).comp
      (S (A.permutation (g⁻¹) (curvePoint U p))) = S (curvePoint U p)
    rw [hfix, hvalue]
    have heq : A.map g ∘ D.inclusion = D.inclusion := by
      funext t
      exact (A.map_eq g (curvePoint U t)).trans
        (congrArg Subtype.val (hfix g t))
    have heqgerm : A.map g ∘ D.inclusion =ᶠ[𝓝 p] D.inclusion :=
      Filter.EventuallyEq.of_eq heq
    have hd := heqgerm.mfderiv_eq (I := 𝓘(ℂ, ℂ)) (I' := 𝓘(ℂ, ℂ × ℂ))
    rw [mfderiv_comp p (A.differentiableAt g (curvePoint U p))
      (D.inclusion.holomorphic p)] at hd
    exact hd
  · have heq : PuncturedSplittingSections.restrict (A.pushforward g S) =
        PuncturedSplittingSections.restrict S := by
      rw [restrict_pushforward A hfix, hres, hinv]
    exact congrArg (fun τ : PuncturedSplittingSections.Section D U => τ ⟨q, hd⟩) heq
end Paper27.Geometry.PuncturedSplittingSections.NeighbourhoodAction

namespace Paper27.Geometry.RetractionCoordinateGerms.NormalAtlas
open PuncturedSplittingSections RetractionCoefficientHolomorphic MeromorphicSplittingAverage
variable {X : CompactComplexSurface} {D : EmbeddedCurve X} {U : D.Neighbourhood}
  {r₁ r₂ r₃ : D.Retraction U} {n : ℕ}
  (A : RetractionCoordinateGerms.NormalAtlas D U r₁ r₂ n)

/-- The actual section constructed by formula (6) extends to an invariant
actual holomorphic splitting tangent to D. The hypothesis `g^n=1` is a group
law, and is automatic for the actual roots-of-unity action. -/
theorem actual_formulaSix_invariant_extension {G : Type} [Group G]
    (J : TaylorGerms.TaylorCalculus) (P : ParametricTaylorCalculus J)
    (L : LaurentCalculus) (extension : LaurentSectionExtension L)
    (calculus : HolomorphicPuncturedCalculus)
    (B : RetractionCoordinateGerms.NormalAtlas D U r₁ r₃ n)
    (C : RetractionCoordinateGerms.NormalAtlas D U r₂ r₃ n) (hn : 2 ≤ n)
    (action : NeighbourhoodSplittings.NeighbourhoodAction G r₁)
    (hfix : ∀ g p, action.permutation g (NeighbourhoodSplittings.curvePoint U p) =
      NeighbourhoodSplittings.curvePoint U p)
    (scalar : G →* ℂˣ)
    (hgerm : ∀ g p, action.map g =ᶠ[𝓝 (D.inclusion p)]
      NormalAtlasAction.localRotation (A.chart p p).coordinates (scalar g : ℂ))
    (g : G) (hgn : g ^ n = 1) (hζ : IsPrimitiveRoot (scalar g : ℂ) n)
    (hpres : ∀ p : U.domain, r₂.toFun (action.map g p.val) = r₂.toFun p.val)
    (ht₂ : PuncturedSplittingSections.JointTransverse r₁ r₂)
    (ht₃ : PuncturedSplittingSections.JointTransverse r₁ r₃) :
    ∃ (a : ℂ) (s : NeighbourhoodSplittings.Section U), a ≠ 0 ∧ a ≠ 1 ∧
      NeighbourhoodSplittings.HolomorphicSection r₁ s ∧
      NeighbourhoodSplittings.IsSplitting r₁ s ∧
      PuncturedSplittingSections.restrict s =
        PuncturedSplittingSections.NeighbourhoodAction.formulaSix action hfix n g a
          (jointInverse r₁ r₂ ht₂) (jointInverse r₁ r₃ ht₃) ∧
      action.pushforward g s = s ∧
      ∀ p : D.curve, s (NeighbourhoodSplittings.curvePoint U p) =
        mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ) D.inclusion p := by
  obtain ⟨a, s, ha0, ha1, hhol, hs, hres, hincl⟩ := A.actual_formulaSix_extension J P L
    extension calculus B C hn action hfix scalar hgerm g hζ ht₂ ht₃
  have h₂ := PuncturedSplittingSections.NeighbourhoodAction.jointInverse_fixed action hfix
    r₂ ht₂ g hpres
  have havg := PuncturedSplittingSections.NeighbourhoodAction.formulaSix_fixed action hfix
    g hgn a (jointInverse r₁ r₂ ht₂) (jointInverse r₁ r₃ ht₃) h₂
  have hglobal := PuncturedSplittingSections.NeighbourhoodAction.extension_fixed action hfix g
    _ s hres havg hincl
  exact ⟨a, s, ha0, ha1, hhol, hs, hres, hglobal, hincl⟩
end Paper27.Geometry.RetractionCoordinateGerms.NormalAtlas
