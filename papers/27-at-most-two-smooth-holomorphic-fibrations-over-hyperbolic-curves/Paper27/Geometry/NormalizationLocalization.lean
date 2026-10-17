import Paper27.Geometry.RamificationSupport
import Paper27.Geometry.FiniteGermNeighbourhood
import Paper27.Geometry.FiniteAnalyticGerm

/-!
# Localizing all actual normalization branches at one surface point

The classical normalization input below is universal for finite holomorphic
maps between compact complex surfaces. It gives compact smooth normalization
curves, finite actual fibres, and coverage of the actual critical set. It does
not assert that their images are smooth, embedded, disjoint, or unramified
over either target factor.

The own localization argument uses compactness to ensure that every nearby
critical point belongs to one of the selected branches through the chosen
point. In particular, it excludes normalization points far from that fibre;
coverage at the centre alone would not suffice.

Classical source: Dinh--Sibony, *Dynamics in several complex variables*,
Appendix A.1, Theorem A.1.4 and Example A.1.5 (normalization is finite and a
normal analytic curve is smooth), https://arxiv.org/abs/0810.0811 . Applied to
the analytic Jacobian divisor of a finite map, compactness gives finitely many
compact normalization components. The Jacobian-divisor/normalization theorem
is an explicit parameter, not a production axiom.
-/
noncomputable section
open scoped Manifold
namespace Paper27.Geometry

/-- A finite family of actual compact curves mapping with finite fibres to
the actual surface. No embedding or immersion is included. -/
structure CompactCurveCover (X : CompactComplexSurface) where
  Index : Type
  [finite : Finite Index]
  curve : Index → Curve
  map : (i : Index) → HolomorphicMap (curve i) X
  finite_fibres : ∀ i p, (map i ⁻¹' {p}).Finite

attribute [instance] CompactCurveCover.finite

namespace CompactCurveCover

variable {X : CompactComplexSurface}

/-- A curve has infinitely many points because a nonempty open complex chart
does. This supplies nonconstancy from finite fibres without an extra label. -/
theorem curve_infinite (C : Curve) : Infinite C := by
  let e := chartAt ℂ C.basepoint
  have hinfinite : e.target.Infinite :=
    infinite_of_mem_nhds (e C.basepoint) (chart_target_mem_nhds ℂ C.basepoint)
  letI : Infinite e.target := hinfinite.to_subtype
  apply Infinite.of_injective (fun z : e.target => e.symm z.val)
  intro u v huv
  apply Subtype.ext
  exact e.symm.injOn u.property v.property huv

theorem map_nonconstant (N : CompactCurveCover X) (i : N.Index) :
    ∃ p q : N.curve i, N.map i p ≠ N.map i q := by
  letI := curve_infinite (N.curve i)
  by_contra h
  push_neg at h
  have heq : N.map i ⁻¹' {N.map i (N.curve i).basepoint} = Set.univ := by
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact h p (N.curve i).basepoint
  have hf := N.finite_fibres i (N.map i (N.curve i).basepoint)
  rw [heq] at hf
  exact Set.infinite_univ hf

def support (N : CompactCurveCover X) : Set X := ⋃ i, Set.range (N.map i)

/-- The indices are precisely all points of all normalization curves over
the fixed source point. This includes distinct branches on the same curve. -/
def Branch (N : CompactCurveCover X) (p : X) := Σ i, N.map i ⁻¹' {p}

instance (N : CompactCurveCover X) (p : X) : Finite (N.Branch p) := by
  letI : ∀ i : N.Index, Finite (N.map i ⁻¹' {p}) :=
    fun i => (N.finite_fibres i p).to_subtype
  exact inferInstanceAs (Finite (Σ i, N.map i ⁻¹' {p}))

theorem branch_nonempty_iff (N : CompactCurveCover X) (p : X) :
    Nonempty (N.Branch p) ↔ p ∈ N.support := by
  constructor
  · rintro ⟨⟨i, t, ht⟩⟩
    exact Set.mem_iUnion.mpr ⟨i, t, ht⟩
  · intro hp
    obtain ⟨i, t, ht⟩ := Set.mem_iUnion.mp hp
    exact ⟨⟨i, t, ht⟩⟩

/-- Simultaneous shrinking on the surface for arbitrary open neighbourhoods
of every actual normalization point over `p`. The conclusion uses precisely
those branches, rather than an unspecified new branch family. -/
theorem localize_branches (N : CompactCurveCover X) (p : X)
    (O : (b : N.Branch p) → Set (N.curve b.1))
    (hO : ∀ b, IsOpen (O b)) (hp : ∀ b, b.2.val ∈ O b) :
    ∃ V : Set X, IsOpen V ∧ p ∈ V ∧
      ∀ q ∈ V, q ∈ N.support →
        ∃ (b : N.Branch p) (t : N.curve b.1), t ∈ O b ∧ N.map b.1 t = q := by
  classical
  let W : (i : N.Index) → Set (N.curve i) :=
    fun i => ⋃ t : N.map i ⁻¹' {p}, O ⟨i, t⟩
  have hopen : ∀ i, IsOpen (W i) := fun i => isOpen_iUnion fun t => hO ⟨i, t⟩
  have hfibre : ∀ i, N.map i ⁻¹' {p} ⊆ W i := by
    intro i t ht
    exact Set.mem_iUnion.mpr ⟨⟨t, ht⟩, hp ⟨i, t, ht⟩⟩
  have hshrink : ∀ i, ∃ V : Set X, IsOpen V ∧ p ∈ V ∧ N.map i ⁻¹' V ⊆ W i :=
    fun i => FiniteGermNeighbourhood.exists_target_neighbourhood_of_fibre_subset
      (N.map i) (N.map i).holomorphic.continuous p (W i) (hopen i) (hfibre i)
  choose V hV hpV hpre using hshrink
  refine ⟨⋂ i, V i, isOpen_iInter_of_finite hV, Set.mem_iInter.mpr hpV, ?_⟩
  intro q hq hsupport
  obtain ⟨i, t, ht⟩ := Set.mem_iUnion.mp hsupport
  have htV : N.map i t ∈ V i := ht ▸ Set.mem_iInter.mp hq i
  obtain ⟨s, hs⟩ := Set.mem_iUnion.mp (hpre i htV)
  exact ⟨⟨i, s⟩, t, hs, ht⟩

end CompactCurveCover

/-- Raw normalization data for the actual critical set of a finite map. -/
structure CriticalCurveNormalization {X Y : CompactComplexSurface}
    (q : RamificationSupport.FiniteSurjectiveHolomorphicMap X Y)
    extends CompactCurveCover X where
  support_eq : toCompactCurveCover.support =
    {p | ¬ Function.Surjective (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) q.map p)}

/-- The general analytic Jacobian-divisor normalization theorem. It has no
product-factor, metric, ramification smoothness, or fibration conclusion. -/
def CriticalCurveNormalizationTheorem : Prop :=
  ∀ (X Y : CompactComplexSurface)
    (q : RamificationSupport.FiniteSurjectiveHolomorphicMap X Y),
      Nonempty (CriticalCurveNormalization q)

namespace CriticalCurveNormalization

variable {X Y : CompactComplexSurface}
  {q : RamificationSupport.FiniteSurjectiveHolomorphicMap X Y}

theorem image_critical (N : CriticalCurveNormalization q) (i : N.Index)
    (t : N.curve i) :
    ¬ Function.Surjective (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) q.map (N.map i t)) := by
  change N.map i t ∈ {p | ¬ Function.Surjective
    (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) q.map p)}
  rw [← N.support_eq]
  exact Set.mem_iUnion.mpr ⟨i, t, rfl⟩

theorem critical_has_branch (N : CriticalCurveNormalization q) (p : X)
    (hp : ¬ Function.Surjective
      (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) q.map p)) :
    Nonempty (N.toCompactCurveCover.Branch p) := by
  apply (N.toCompactCurveCover.branch_nonempty_iff p).mpr
  rw [N.support_eq]
  exact hp

/-- Actual branch neighbourhoods cover every nearby critical point. This is
the needed global-to-local normalization step in Proposition 2.4. -/
theorem local_critical_cover (N : CriticalCurveNormalization q) (p : X)
    (O : (b : N.toCompactCurveCover.Branch p) → Set (N.curve b.1))
    (hO : ∀ b, IsOpen (O b)) (hp : ∀ b, b.2.val ∈ O b) :
    ∃ V : Set X, IsOpen V ∧ p ∈ V ∧
      ∀ x ∈ V, (¬ Function.Surjective
        (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) q.map x)) →
        ∃ (b : N.toCompactCurveCover.Branch p) (t : N.curve b.1),
          t ∈ O b ∧ N.map b.1 t = x := by
  obtain ⟨V, hV, hpV, hcover⟩ := N.toCompactCurveCover.localize_branches p O hO hp
  refine ⟨V, hV, hpV, ?_⟩
  intro x hx hcrit
  apply hcover x hx
  rw [N.support_eq]
  exact hcrit

end CriticalCurveNormalization
end Paper27.Geometry
