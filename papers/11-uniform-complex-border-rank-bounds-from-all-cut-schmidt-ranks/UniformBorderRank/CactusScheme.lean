import UniformBorderRank.CactusAffine
import UniformBorderRank.ProjectiveSecant
import Mathlib.AlgebraicGeometry.Artinian
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Finite closed subschemes and their projective spans

The affine-chart ideals used in `CactusAffine` specify actual schemes and
closed immersions. Finite-dimensional quotient algebras give finite schemes
over `Spec ℂ`. Their ideal-defined spans satisfy the `F(length)` secant bound,
and the same holds after the projective Zariski closure of their union.

The union here ranges over finite subschemes of specified product affine
charts. Identifying it with the union over all finite subschemes of the
projective Segre still requires the common-chart and section-trivialization
theorem; this file does not assume or claim that identification.
-/

noncomputable section
namespace UniformBorderRank
open AlgebraicGeometry CategoryTheory
open scoped LinearAlgebra.Projectivization

variable {N : ℕ} {d : Fin N → ℕ}

/-- Scheme-theoretic containment in an affine chart gives an actual quotient
coordinate ring. Containment of the underlying support suffices, even for
nonreduced closed subschemes. -/
theorem closedSubscheme_in_affine_chart_quotient
    {Z Y : Scheme} {R : CommRingCat}
    (f : Z ⟶ Y) (g : Spec R ⟶ Y)
    [IsClosedImmersion f] [IsOpenImmersion g]
    (h : Set.range f ⊆ Set.range g) :
    ∃ (I : Ideal R) (e : Z ≅ Spec (CommRingCat.of (R ⧸ I))),
      IsOpenImmersion.lift g f h =
        e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
  let q := IsOpenImmersion.lift g f h
  haveI : IsClosedImmersion (q ≫ g) := by
    dsimp [q]
    rw [IsOpenImmersion.lift_fac]
    infer_instance
  letI : IsClosedImmersion q := IsClosedImmersion.of_comp q g
  exact IsClosedImmersion.Spec_iff.mp inferInstance

/-- For a finite complex scheme, the quotient obtained from an actual affine
chart has finite-dimensional complex coordinate algebra. The compatibility
equation is the ordinary equation for morphisms over `Spec ℂ`. -/
theorem finiteClosedSubscheme_in_affine_chart_quotient
    {Z Y : Scheme} {R : CommRingCat} [Algebra ℂ R]
    (f : Z ⟶ Y) (g : Spec R ⟶ Y)
    [IsClosedImmersion f] [IsOpenImmersion g]
    (h : Set.range f ⊆ Set.range g)
    (s : Z ⟶ Spec (CommRingCat.of ℂ)) [IsFinite s]
    (hbase : IsOpenImmersion.lift g f h ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ R)) = s) :
    ∃ (I : Ideal R) (e : Z ≅ Spec (CommRingCat.of (R ⧸ I))),
      IsOpenImmersion.lift g f h =
        e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ∧
      FiniteDimensional ℂ (R ⧸ I) := by
  obtain ⟨I, e, he⟩ := closedSubscheme_in_affine_chart_quotient f g h
  refine ⟨I, e, he, ?_⟩
  let t := Spec.map (CommRingCat.ofHom (algebraMap ℂ (R ⧸ I)))
  have hmaps : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ R)) = t := by
    rw [← Spec.map_comp]
    rfl
  have hcomp : e.hom ≫ t = s := by
    rw [← hmaps, ← Category.assoc, ← he]
    exact hbase
  have ht : t = e.inv ≫ s := by
    rw [← hcomp]
    simp
  haveI : IsFinite t := by rw [ht]; infer_instance
  exact RingHom.finite_algebraMap.mp
    ((IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap ℂ (R ⧸ I)))).mp
      (inferInstance : IsFinite t))

/-- The product affine chart as an actual affine scheme. -/
def segreProductChart (b : ∀ i, Fin (d i)) : Scheme :=
  Spec (CommRingCat.of (SegreChartRing d b))

/-- The closed subscheme cut out by the full ideal `I`, with nilpotents. -/
def segreFiniteChartSubscheme (b : ∀ i, Fin (d i))
    (I : Ideal (SegreChartRing d b)) : Scheme :=
  Spec (CommRingCat.of (SegreChartRing d b ⧸ I))

/-- The canonical closed immersion of the quotient scheme into the chart. -/
def segreFiniteChartSubschemeInclusion (b : ∀ i, Fin (d i))
    (I : Ideal (SegreChartRing d b)) :
    segreFiniteChartSubscheme b I ⟶ segreProductChart b :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))

instance segreFiniteChartSubschemeInclusion_isClosedImmersion
    (b : ∀ i, Fin (d i)) (I : Ideal (SegreChartRing d b)) :
    IsClosedImmersion (segreFiniteChartSubschemeInclusion b I) := by
  dsimp [segreFiniteChartSubschemeInclusion]
  exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

theorem segreFiniteChartSubscheme_isArtinian
    (b : ∀ i, Fin (d i)) (I : Ideal (SegreChartRing d b))
    [FiniteDimensional ℂ (SegreChartRing d b ⧸ I)] :
    IsArtinianScheme (segreFiniteChartSubscheme b I) := by
  letI : IsArtinianRing (SegreChartRing d b ⧸ I) :=
    isArtinian_of_tower ℂ (inferInstance : IsArtinian ℂ (SegreChartRing d b ⧸ I))
  exact Scheme.isArtinianScheme_Spec.mpr inferInstance

/-- Finiteness here is the scheme-theoretic finite-morphism property. -/
theorem segreFiniteChartSubscheme_finite_over_complex
    (b : ∀ i, Fin (d i)) (I : Ideal (SegreChartRing d b))
    [FiniteDimensional ℂ (SegreChartRing d b ⧸ I)] :
    IsFinite (Spec.map (CommRingCat.ofHom
      (algebraMap ℂ (SegreChartRing d b ⧸ I)))) := by
  apply (IsFinite.SpecMap_iff _).mpr
  exact RingHom.finite_algebraMap.mpr inferInstance

/-- Union of the projective scheme-theoretic spans of length-at-most-`m`
closed subschemes lying in product affine charts. This definition uses ideals
and their vanishing linear sections, never algebra-product representations. -/
def productChartCactusSpans (d : Fin N → ℕ) (m : ℕ) : Set (ProjectiveTensor d) :=
  {p | ∃ (b : ∀ i, Fin (d i)) (I : Ideal (SegreChartRing d b))
      (_ : FiniteDimensional ℂ (SegreChartRing d b ⧸ I))
      (_ : Nontrivial (SegreChartRing d b ⧸ I))
      (T : Coeffs d) (hT : T ≠ 0),
    Module.finrank ℂ (SegreChartRing d b ⧸ I) ≤ m ∧
    T ∈ segreSubschemeSpan b I ∧ Projectivization.mk ℂ T hT = p}

theorem productChartCactusSpans_subset_secant (hN : 0 < N) (m : ℕ) :
    productChartCactusSpans d m ⊆ projectiveSecant d (F m) := by
  rintro p ⟨b, I, hfinite, hnontrivial, T, hT, hlength, hspan, rfl⟩
  letI := hfinite
  letI := hnontrivial
  exact borderRankLe_mem_projectiveSecant hN hT
    (borderRankLe_segreSubschemeSpan_of_length_le hN b I hlength hspan)

/-- Taking the actual homogeneous-polynomial projective Zariski closure
preserves the `F(m)` secant containment. -/
theorem productChartCactus_closure_subset_secant (hN : 0 < N) (m : ℕ) :
    projectiveZariskiClosure (productChartCactusSpans d m) ⊆
      projectiveSecant d (F m) := by
  have h := projectiveZariskiClosure_mono (productChartCactusSpans_subset_secant (d := d) hN m)
  simpa only [projectiveSecant, projectiveZariskiClosure_idem] using h

end UniformBorderRank
