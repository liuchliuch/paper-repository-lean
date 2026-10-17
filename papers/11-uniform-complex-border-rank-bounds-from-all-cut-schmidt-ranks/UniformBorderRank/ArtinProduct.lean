import UniformBorderRank.AlgebraProduct
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! Proposition 3.2 via local factors of a finite-dimensional algebra. -/
noncomputable section
namespace UniformBorderRank
open Finset Module

lemma exists_complex_residue {A : Type*} [CommRing A] [Algebra ℂ A]
    [FiniteDimensional ℂ A] [IsLocalRing A] :
    ∃ res : A →ₐ[ℂ] ℂ, ∀ x, res x = 0 ↔ x ∈ IsLocalRing.maximalIdeal A := by
  let I := IsLocalRing.maximalIdeal A
  letI : I.IsMaximal := by dsimp [I]; infer_instance
  letI : Module.Finite ℂ (A ⧸ I) := Module.Finite.of_surjective
    (Ideal.Quotient.mkₐ ℂ I).toLinearMap (Ideal.Quotient.mkₐ_surjective ℂ I)
  let e : ℂ ≃ₐ[ℂ] (A ⧸ I) := AlgEquiv.ofBijective (Algebra.ofId ℂ (A ⧸ I))
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ) (K := A ⧸ I))
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ I), ?_⟩
  intro x
  change e.symm (Ideal.Quotient.mk I x) = 0 ↔ x ∈ I
  rw [← map_zero e.symm, e.symm.injective.eq_iff]
  exact Ideal.Quotient.eq_zero_iff_mem

/-- The full local-algebra case of Proposition 3.2, with no prescribed
nilpotence exponent, basis, or residue map among its assumptions. -/
theorem borderRankLe_artin_local_product {N : ℕ} {d : Fin N → ℕ} (hN : 0 < N)
    {A : Type*} [CommRing A] [Algebra ℂ A] [FiniteDimensional ℂ A] [IsLocalRing A]
    (v : ∀ i, Fin (d i) → A) (ell : A →ₗ[ℂ] ℂ) :
    borderRankLe (fun u => ell (∏ i, v i (u i))) (F (Module.finrank ℂ A)) := by
  classical
  obtain ⟨res, hres⟩ := exists_complex_residue (A := A)
  let I := IsLocalRing.maximalIdeal A
  let q := Module.finrank ℂ A
  have hsurj : Function.Surjective res := by
    intro c
    exact ⟨algebraMap ℂ A c, by simp⟩
  have hker : LinearMap.ker res.toLinearMap = I.restrictScalars ℂ := by
    ext x
    exact hres x
  have hdim : Module.finrank ℂ (I.restrictScalars ℂ) = q - 1 := by
    have h := res.toLinearMap.finrank_range_add_finrank_ker
    rw [hker, LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self] at h
    omega
  let B : Basis (Fin (q - 1)) ℂ (I.restrictScalars ℂ) :=
    (Module.finBasis ℂ (I.restrictScalars ℂ)).reindex (finCongr hdim)
  let a : ∀ i, Fin (d i) → ℂ := fun i x => res (v i x)
  let n : ∀ i, Fin (d i) → I.restrictScalars ℂ := fun i x =>
    ⟨v i x - algebraMap ℂ A (res (v i x)), (hres _).mp (by simp)⟩
  have hq : 1 ≤ q := Module.finrank_pos
  have hb := borderRankLe_local_product hN I q hq
    (maximalIdeal_pow_finrank_eq_bot (K := ℂ) (A := A)) B ell a n
  have he : (fun u : ∀ i, Fin (d i) => ell (∏ i, (algebraMap ℂ A (a i (u i)) + (n i (u i)).val))) =
      (fun u : ∀ i, Fin (d i) => ell (∏ i, v i (u i))) := by
    ext u
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    dsimp [a, n]
    abel
  rw [he] at hb
  exact hb

/-- **Proposition 3.2.** Arbitrarily long products in any finite-dimensional
commutative unital complex algebra have border rank at most `F(dim A)`. -/
theorem borderRankLe_algebra_product {N : ℕ} {d : Fin N → ℕ} (hN : 0 < N)
    {A : Type*} [CommRing A] [Algebra ℂ A] [FiniteDimensional ℂ A] [Nontrivial A]
    (v : ∀ i, Fin (d i) → A) (ell : A →ₗ[ℂ] ℂ) :
    borderRankLe (fun u => ell (∏ i, v i (u i))) (F (Module.finrank ℂ A)) := by
  classical
  letI : IsArtinianRing A := isArtinian_of_tower ℂ (inferInstance : IsArtinian ℂ A)
  letI : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
  letI : DiscreteTopology (PrimeSpectrum A) :=
    PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mpr
      ⟨inferInstance, Ring.KrullDimLE.mk₀ (fun I h => (IsArtinianRing.isPrime_iff_isMaximal I).mp h)⟩
  let D : MaximalSpectrum A → Type _ := fun I => Localization.AtPrime I.asIdeal
  haveI (I : MaximalSpectrum A) : FiniteDimensional ℂ (D I) :=
    Module.Finite.of_surjective (IsScalarTower.toAlgHom ℂ A (D I)).toLinearMap
      (IsArtinianRing.localization_surjective I.asIdeal.primeCompl (D I))
  let e : A ≃ₐ[ℂ] MaximalSpectrum.PiLocalization A :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom ℂ A (MaximalSpectrum.PiLocalization A))
      (MaximalSpectrum.toPiLocalizationEquiv A).bijective
  let ellD (I : MaximalSpectrum A) : D I →ₗ[ℂ] ℂ :=
    ell.comp (e.symm.toLinearMap.comp (LinearMap.single ℂ D I))
  let vD (I : MaximalSpectrum A) : ∀ i, Fin (d i) → D I :=
    fun i x => algebraMap A (D I) (v i x)
  let T (I : MaximalSpectrum A) : Coeffs d := fun u => ellD I (∏ i, vD I i (u i))
  have hT (I : MaximalSpectrum A) : borderRankLe (T I) (F (Module.finrank ℂ (D I))) :=
    borderRankLe_artin_local_product hN (vD I) (ellD I)
  have he : (fun u => ell (∏ i, v i (u i))) = ∑ I : MaximalSpectrum A, T I := by
    ext u
    have hval : e (∏ i, v i (u i)) = fun I => ∏ i, vD I i (u i) := by
      ext I
      change algebraMap A (D I) (∏ i, v i (u i)) = ∏ i, algebraMap A (D I) (v i (u i))
      exact map_prod _ _ _
    have hprod : (∏ i, v i (u i)) = e.symm (fun I => ∏ i, vD I i (u i)) := by
      apply e.injective
      rw [e.apply_symm_apply]
      exact hval
    rw [hprod, ← Finset.univ_sum_single (fun I => ∏ i, vD I i (u i)), map_sum, map_sum]
    simp only [Finset.sum_apply]
    rfl
  have hdims : (∑ I : MaximalSpectrum A, Module.finrank ℂ (D I)) = Module.finrank ℂ A := by
    have hp := Module.finrank_pi_fintype ℂ (M := D)
    exact hp.symm.trans e.toLinearEquiv.finrank_eq.symm
  have hF : (∑ I : MaximalSpectrum A, F (Module.finrank ℂ (D I))) ≤ F (Module.finrank ℂ A) := by
    rw [← hdims]
    apply sum_F_le_F_sum univ (fun I => Module.finrank ℂ (D I)) univ_nonempty
    intro I _
    exact Module.finrank_pos
  rw [he]
  exact borderRankLe_mono hN hF (borderRankLe_finset_sum univ T
    (fun I => F (Module.finrank ℂ (D I))) (fun I _ => hT I))

end UniformBorderRank
