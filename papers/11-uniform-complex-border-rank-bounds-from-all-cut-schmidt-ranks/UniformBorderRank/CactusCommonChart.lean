import UniformBorderRank.CactusAffine
import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Common affine charts for finite projective supports

A finite family of nonzero complex vectors admits one linear form nonzero
on the entire family. Consequently every finite set of projective points is
contained in one affine chart. We construct the chart's actual equivalence
with the hyperplane on which that linear form is one, and with its kernel
after choosing a point of that hyperplane.

These are statements about projective points and their chart coordinates.
They do not identify `Projectivization` with a projective scheme or prove the
line-bundle restriction theorem for finite subschemes.
-/

noncomputable section
namespace UniformBorderRank
open Module
open scoped LinearAlgebra.Projectivization

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Finite hyperplane avoidance, with no independence assumption on the
vectors. -/
theorem exists_dual_nonzero_on_finset (S : Finset V)
    (hS : ∀ x ∈ S, x ≠ 0) :
    ∃ ell : V →ₗ[ℂ] ℂ, ∀ x ∈ S, ell x ≠ 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert x S hx ih =>
    obtain ⟨ell, hell⟩ := ih (fun y hy => hS y (Finset.mem_insert_of_mem hy))
    obtain ⟨eta, heta⟩ := Module.Projective.exists_dual_ne_zero ℂ
      (hS x (Finset.mem_insert_self x S))
    let bad : Finset ℂ := (insert x S).image (fun y => -(ell y) / eta y)
    obtain ⟨c, hc⟩ := bad.exists_notMem
    refine ⟨ell + c • eta, ?_⟩
    intro y hy hzero
    change ell y + c * eta y = 0 at hzero
    by_cases heta0 : eta y = 0
    · have hyx : y ≠ x := by
        intro he
        subst y
        exact heta heta0
      have hyS : y ∈ S := (Finset.mem_insert.mp hy).resolve_left hyx
      have hell0 : ell y = 0 := by simpa [heta0] using hzero
      exact hell y hyS hell0
    · have hceq : c = -(ell y) / eta y := by
        apply (eq_div_iff heta0).mpr
        linear_combination hzero
      apply hc
      exact Finset.mem_image.mpr ⟨y, hy, hceq.symm⟩

/-- The affine projective chart determined by a linear form. The condition is
independent of representative, as the equivalence below also proves. -/
def projectiveLinearChart (ell : V →ₗ[ℂ] ℂ) : Set (Projectivization ℂ V) :=
  {p | ell p.rep ≠ 0}

/-- Every finite projective support lies in a common affine chart. -/
theorem finite_projective_support_common_chart (S : Finset (Projectivization ℂ V)) :
    ∃ ell : V →ₗ[ℂ] ℂ, ∀ p ∈ S, p ∈ projectiveLinearChart ell := by
  classical
  let R : Finset V := S.image Projectivization.rep
  have hR : ∀ x ∈ R, x ≠ 0 := by
    rintro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    exact p.rep_nonzero
  obtain ⟨ell, hell⟩ := exists_dual_nonzero_on_finset R hR
  refine ⟨ell, fun p hp => ?_⟩
  exact hell p.rep (Finset.mem_image.mpr ⟨p, hp, rfl⟩)

/-- A finite support in a product of projective spaces admits one product
affine chart, choosing one common nonvanishing form in every factor. -/
theorem finite_projective_product_support_common_chart {N : ℕ} {d : Fin N → ℕ}
    (S : Finset (∀ i, Projectivization ℂ (Fin (d i) → ℂ))) :
    ∃ ell : ∀ i, (Fin (d i) → ℂ) →ₗ[ℂ] ℂ,
      ∀ p ∈ S, ∀ i, p i ∈ projectiveLinearChart (ell i) := by
  classical
  have hex (i : Fin N) := finite_projective_support_common_chart (S.image (fun p => p i))
  choose ell hell using hex
  refine ⟨ell, fun p hp i => ?_⟩
  exact hell i (p i) (Finset.mem_image.mpr ⟨p, hp, rfl⟩)

/-- The normalized affine hyperplane for a projective chart. -/
abbrev projectiveChartHyperplane (ell : V →ₗ[ℂ] ℂ) := {x : V // ell x = 1}

theorem projectiveChartHyperplane_nonzero (ell : V →ₗ[ℂ] ℂ)
    (x : projectiveChartHyperplane ell) : (x : V) ≠ 0 := by
  intro hx
  have h := x.property
  rw [hx, map_zero] at h
  exact zero_ne_one h

theorem projectiveLinearChart_mk_iff (ell : V →ₗ[ℂ] ℂ) (x : V) (hx : x ≠ 0) :
    Projectivization.mk ℂ x hx ∈ projectiveLinearChart ell ↔ ell x ≠ 0 := by
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep ℂ x hx
  change ell (Projectivization.mk ℂ x hx).rep ≠ 0 ↔ ell x ≠ 0
  rw [← hc]
  simp [Units.smul_def, map_smul]

/-- The natural chart map from the normalized affine hyperplane. -/
def projectiveChartHyperplaneMap (ell : V →ₗ[ℂ] ℂ)
    (x : projectiveChartHyperplane ell) : projectiveLinearChart ell :=
  ⟨Projectivization.mk ℂ (x : V) (projectiveChartHyperplane_nonzero ell x),
    (projectiveLinearChart_mk_iff ell x _).mpr (by rw [x.property]; exact one_ne_zero)⟩

theorem projectiveChartHyperplaneMap_bijective (ell : V →ₗ[ℂ] ℂ) :
    Function.Bijective (projectiveChartHyperplaneMap ell) := by
  constructor
  · intro x y hxy
    have hmk := congrArg Subtype.val hxy
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp hmk
    have hc1 : c = 1 := by
      have h := congrArg ell hc
      simpa only [map_smul, x.property, y.property, smul_eq_mul, mul_one] using h
    apply Subtype.ext
    simpa only [hc1, one_smul] using hc.symm
  · intro p
    let x : V := (ell p.val.rep)⁻¹ • p.val.rep
    have hx : ell x = 1 := by
      dsimp [x]
      rw [map_smul, smul_eq_mul, inv_mul_cancel₀ p.property]
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    dsimp only [projectiveChartHyperplaneMap]
    change Projectivization.mk ℂ x _ = p.val
    rw [← p.val.mk_rep]
    exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨(ell p.val.rep)⁻¹, rfl⟩

/-- An actual equivalence between the affine projective chart and the
normalized affine hyperplane. -/
def projectiveChartEquivHyperplane (ell : V →ₗ[ℂ] ℂ) :
    projectiveLinearChart ell ≃ projectiveChartHyperplane ell :=
  (Equiv.ofBijective (projectiveChartHyperplaneMap ell)
    (projectiveChartHyperplaneMap_bijective ell)).symm

/-- Translating a normalized hyperplane by one of its points identifies it
with the kernel vector space of its defining form. -/
def projectiveHyperplaneEquivKernel (ell : V →ₗ[ℂ] ℂ)
    (a : V) (ha : ell a = 1) : projectiveChartHyperplane ell ≃ LinearMap.ker ell where
  toFun x := ⟨x.val - a, by simp [LinearMap.mem_ker, map_sub, x.property, ha]⟩
  invFun x := ⟨x.val + a, by simp [map_add, (LinearMap.mem_ker.mp x.property), ha]⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv x := by apply Subtype.ext; simp

/-- The common projective chart has affine coordinates in `ker ell`. -/
def projectiveChartEquivKernel (ell : V →ₗ[ℂ] ℂ)
    (a : V) (ha : ell a = 1) : projectiveLinearChart ell ≃ LinearMap.ker ell :=
  (projectiveChartEquivHyperplane ell).trans (projectiveHyperplaneEquivKernel ell a ha)

/-- Finite-dimensional affine coordinates on the chart, obtained from a
basis of the kernel of its defining form. -/
def projectiveChartEquivCoordinates [FiniteDimensional ℂ V]
    (ell : V →ₗ[ℂ] ℂ) (a : V) (ha : ell a = 1) :
    projectiveLinearChart ell ≃ (Fin (Module.finrank ℂ (LinearMap.ker ell)) → ℂ) :=
  (projectiveChartEquivKernel ell a ha).trans (Module.finBasis ℂ (LinearMap.ker ell)).equivFun.toEquiv

end UniformBorderRank
