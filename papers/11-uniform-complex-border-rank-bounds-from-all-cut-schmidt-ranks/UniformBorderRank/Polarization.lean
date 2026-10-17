import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-! The quantitative polarization mechanism of equation (12), expressed as
interpolation on homogeneous polynomials. -/
noncomputable section
namespace UniformBorderRank
open Finset Module MvPolynomial

abbrev HomogeneousPoly (s k : ℕ) := MvPolynomial.homogeneousSubmodule (Fin s) ℂ k

def degreeIndexEquiv (s k : ℕ) : Sym (Fin s) k ≃ {e : Fin s →₀ ℕ // e.degree = k} :=
  (Sym.equivNatSum (Fin s) k).trans
    (Equiv.subtypeEquivRight (fun e => by rfl))

noncomputable instance degreeIndexFintype (s k : ℕ) :
    Fintype {e : Fin s →₀ ℕ // e.degree = k} :=
  Fintype.ofEquiv (Sym (Fin s) k) (degreeIndexEquiv s k)

def homogeneousMonomialBasis (s k : ℕ) :
    Basis {e : Fin s →₀ ℕ // e.degree = k} ℂ (HomogeneousPoly s k) :=
  (MvPolynomial.basisRestrictSupport ℂ {e : Fin s →₀ ℕ | e.degree = k}).map
    (LinearEquiv.ofEq _ _ (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported (Fin s) ℂ k).symm)

instance homogeneousPolyFinite (s k : ℕ) : FiniteDimensional ℂ (HomogeneousPoly s k) :=
  Module.Finite.of_basis (homogeneousMonomialBasis s k)

theorem finrank_homogeneousPoly (s k : ℕ) :
    Module.finrank ℂ (HomogeneousPoly s k) = (s + k - 1).choose k := by
  rw [Module.finrank_eq_card_basis (homogeneousMonomialBasis s k),
    ← Fintype.card_congr (degreeIndexEquiv s k), Sym.card_sym_eq_choose]
  simp

def homogeneousEval (s k : ℕ) (x : Fin s → ℂ) : HomogeneousPoly s k →ₗ[ℂ] ℂ :=
  (MvPolynomial.aeval x).toLinearMap.comp (HomogeneousPoly s k).subtype

lemma span_homogeneousEval (s k : ℕ) :
    Submodule.span ℂ (Set.range (homogeneousEval s k)) = ⊤ := by
  apply Submodule.span_eq_top_of_ne_zero
  intro p hp
  have hn : ∃ x : Fin s → ℂ, MvPolynomial.eval x p.val ≠ 0 := by
    by_contra! hh
    have hz := p.property.eq_zero_of_forall_eval_eq_zero hh
    exact hp (Subtype.ext hz)
  obtain ⟨x, hx⟩ := hn
  refine ⟨homogeneousEval s k x, ⟨x, rfl⟩, ?_⟩
  simpa [homogeneousEval] using hx

/-- Every functional on degree-`k` homogeneous polynomials is a combination
of exactly `choose(s+k-1,k)` point evaluations.  Zero coefficients allow
fewer evaluations. -/
theorem homogeneous_interpolation (s k : ℕ) (ell : HomogeneousPoly s k →ₗ[ℂ] ℂ) :
    ∃ (x : Fin ((s + k - 1).choose k) → (Fin s → ℂ))
      (c : Fin ((s + k - 1).choose k) → ℂ),
      ∀ p : HomogeneousPoly s k, ell p = ∑ j, c j * MvPolynomial.eval (x j) p.val := by
  classical
  let ι : Type := ↥((linearIndepOn_empty ℂ (id :
    (HomogeneousPoly s k →ₗ[ℂ] ℂ) → (HomogeneousPoly s k →ₗ[ℂ] ℂ))).extend
      (Set.empty_subset (Set.range (homogeneousEval s k))))
  let B : Basis ι ℂ (HomogeneousPoly s k →ₗ[ℂ] ℂ) :=
    Basis.ofSpan (span_homogeneousEval s k).ge
  haveI : Finite ι := Module.Finite.finite_basis B
  have hcard : Module.finrank ℂ (HomogeneousPoly s k →ₗ[ℂ] ℂ) = (s + k - 1).choose k := by
    rw [Module.finrank_linearMap, Module.finrank_self, mul_one, finrank_homogeneousPoly]
  haveI : Fintype ι := Fintype.ofFinite ι
  have he : Fintype.card ι = (s + k - 1).choose k := by
    rw [← Module.finrank_eq_card_basis B, hcard]
  let e := (Fintype.equivFinOfCardEq he).symm
  have hB : ∀ j, ∃ x : Fin s → ℂ, B (e j) = homogeneousEval s k x := by
    intro j
    obtain ⟨x, hx⟩ := Basis.ofSpan_subset (span_homogeneousEval s k).ge ⟨e j, rfl⟩
    exact ⟨x, hx.symm⟩
  choose x hx using hB
  refine ⟨x, fun j => B.repr ell (e j), ?_⟩
  intro p
  have hsum := congrArg (fun f : HomogeneousPoly s k →ₗ[ℂ] ℂ => f p) (B.sum_repr ell)
  rw [← e.sum_comp] at hsum
  simpa [hx, homogeneousEval] using hsum.symm

def coordinateLinearPoly {E : Type*} [AddCommGroup E] [Module ℂ E] {s : ℕ}
    (B : Basis (Fin s) ℂ E) (y : E) : MvPolynomial (Fin s) ℂ :=
  ∑ j, (B.repr y j) • MvPolynomial.X j

lemma coordinateLinearPoly_homogeneous {E : Type*} [AddCommGroup E] [Module ℂ E] {s : ℕ}
    (B : Basis (Fin s) ℂ E) (y : E) : (coordinateLinearPoly B y).IsHomogeneous 1 := by
  apply (MvPolynomial.homogeneousSubmodule (Fin s) ℂ 1).sum_mem
  intro j _
  exact (MvPolynomial.homogeneousSubmodule (Fin s) ℂ 1).smul_mem _
    (MvPolynomial.isHomogeneous_X ℂ j)

lemma aeval_coordinateLinearPoly {E A : Type*} [AddCommGroup E] [Module ℂ E]
    [CommRing A] [Algebra ℂ A] {s : ℕ} (B : Basis (Fin s) ℂ E)
    (f : E →ₗ[ℂ] A) (y : E) :
    MvPolynomial.aeval (fun j => f (B j)) (coordinateLinearPoly B y) = f y := by
  simp only [coordinateLinearPoly, map_sum, map_smul, MvPolynomial.aeval_X]
  have h := congrArg f (B.sum_repr y)
  simpa only [map_sum, map_smul] using h

def coordinateFunctional {E : Type*} [AddCommGroup E] [Module ℂ E] {s : ℕ}
    (B : Basis (Fin s) ℂ E) (x : Fin s → ℂ) : E →ₗ[ℂ] ℂ :=
  ∑ j, x j • B.coord j

lemma eval_coordinateLinearPoly {E : Type*} [AddCommGroup E] [Module ℂ E] {s : ℕ}
    (B : Basis (Fin s) ℂ E) (x : Fin s → ℂ) (y : E) :
    MvPolynomial.eval x (coordinateLinearPoly B y) = coordinateFunctional B x y := by
  simp [coordinateLinearPoly, coordinateFunctional, mul_comm]

/-- Quantitative polarization (12): one set of pure powers represents the
multiplication form on every set of `k` arguments. -/
theorem pure_power_decomposition {E A : Type*} [AddCommGroup E] [Module ℂ E]
    [CommRing A] [Algebra ℂ A] {s : ℕ} (B : Basis (Fin s) ℂ E)
    (f : E →ₗ[ℂ] A) (ell : A →ₗ[ℂ] ℂ) (k : ℕ) :
    ∃ (eta : Fin ((s + k - 1).choose k) → (E →ₗ[ℂ] ℂ))
      (c : Fin ((s + k - 1).choose k) → ℂ),
      ∀ (ι : Type) [Fintype ι], Fintype.card ι = k → ∀ y : ι → E,
        ell (∏ i, f (y i)) = ∑ j, c j * ∏ i, eta j (y i) := by
  let L : HomogeneousPoly s k →ₗ[ℂ] ℂ := ell.comp
    ((MvPolynomial.aeval (fun j => f (B j))).toLinearMap.comp (HomogeneousPoly s k).subtype)
  obtain ⟨x, c, hc⟩ := homogeneous_interpolation s k L
  refine ⟨fun j => coordinateFunctional B (x j), c, ?_⟩
  intro ι _ hcard y
  have hp : (∏ i, coordinateLinearPoly B (y i)).IsHomogeneous k := by
    have hh := MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset ι)
      (fun i => coordinateLinearPoly B (y i)) (fun _ => 1)
      (fun i _ => coordinateLinearPoly_homogeneous B (y i))
    simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, hcard] using hh
  have hi := hc ⟨∏ i, coordinateLinearPoly B (y i), hp⟩
  change ell ((MvPolynomial.aeval (fun j => f (B j))) (∏ i, coordinateLinearPoly B (y i))) =
    ∑ j, c j * MvPolynomial.eval (x j) (∏ i, coordinateLinearPoly B (y i)) at hi
  simpa only [map_prod, aeval_coordinateLinearPoly, eval_coordinateLinearPoly] using hi

end UniformBorderRank
