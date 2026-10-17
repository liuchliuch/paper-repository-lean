import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! The dimension bound on nilpotence used in Proposition 3.2. -/
noncomputable section
namespace UniformBorderRank

lemma ideal_pow_stable_eq_bot {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (I : Ideal A) (hI : IsNilpotent I) (k : ℕ) (he : I ^ (k + 1) = I ^ k) : I ^ k = ⊥ := by
  obtain ⟨t, ht⟩ := hI
  have hstable : ∀ n : ℕ, I ^ (k + n) = I ^ k := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.add_succ, pow_succ, ih, ← pow_succ, he]
  have hs := hstable t
  rw [pow_add, ht, mul_zero] at hs
  exact hs.symm

/-- Any nilpotent ideal in a finite-dimensional algebra vanishes at the
ambient vector-space dimension. -/
theorem ideal_pow_finrank_eq_bot {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A] (I : Ideal A) (hI : IsNilpotent I) :
    I ^ Module.finrank K A = ⊥ := by
  classical
  have hle (k : ℕ) : I ^ (k + 1) ≤ I ^ k := by
    rw [pow_succ]
    exact Ideal.mul_le_right
  have hdrop (k : ℕ) (hk : I ^ k ≠ ⊥) :
      (I ^ (k + 1)).restrictScalars K < (I ^ k).restrictScalars K := by
    apply lt_of_le_of_ne ((Submodule.restrictScalars_le K).mpr (hle k))
    intro he
    apply hk
    apply ideal_pow_stable_eq_bot (K := K) I hI k
    exact Submodule.restrictScalars_injective K A A he
  have hdim : ∀ k : ℕ, k ≤ Module.finrank K A →
      Module.finrank K ((I ^ k).restrictScalars K) + k ≤ Module.finrank K A := by
    intro k
    induction k with
    | zero =>
      intro _
      simpa only [Nat.add_zero] using ((I ^ 0).restrictScalars K).finrank_le
    | succ k ih =>
      intro hk
      have hp := ih (by omega)
      by_cases hz : I ^ k = ⊥
      · have hz' : I ^ (k + 1) = ⊥ := le_bot_iff.mp (by simpa [hz] using hle k)
        rw [hz', Submodule.restrictScalars_bot, finrank_bot]
        omega
      · have hd : Module.finrank K ((I ^ (k + 1)).restrictScalars K) <
            Module.finrank K ((I ^ k).restrictScalars K) :=
          Submodule.finrank_lt_finrank_of_lt (hdrop k hz)
        omega
  have hb := hdim (Module.finrank K A) le_rfl
  have hz : Module.finrank K ((I ^ Module.finrank K A).restrictScalars K) = 0 := by omega
  have hs := Submodule.finrank_eq_zero.mp hz
  exact Submodule.restrictScalars_injective K A A (hs.trans (Submodule.restrictScalars_bot K A A).symm)

/-- In a finite-dimensional local algebra, the `d`-th power of its maximal
ideal vanishes, with `d` equal to the vector-space dimension. -/
theorem maximalIdeal_pow_finrank_eq_bot {K A : Type*} [Field K] [CommRing A]
    [Algebra K A] [FiniteDimensional K A] [IsLocalRing A] :
    (IsLocalRing.maximalIdeal A) ^ Module.finrank K A = ⊥ := by
  letI : IsArtinianRing A := isArtinian_of_tower K (inferInstance : IsArtinian K A)
  have hI := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hI
  exact ideal_pow_finrank_eq_bot (K := K) _ hI

lemma prod_mem_ideal_pow {A ι : Type*} [CommRing A] (I : Ideal A)
    (S : Finset ι) (f : ι → A) (hf : ∀ i ∈ S, f i ∈ I) :
    ∏ i ∈ S, f i ∈ I ^ S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, pow_succ']
    exact Ideal.mul_mem_mul (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma prod_eq_zero_of_ideal_pow_eq_bot {A ι : Type*} [CommRing A] (I : Ideal A)
    (q : ℕ) (hq : I ^ q = ⊥) (S : Finset ι) (f : ι → A)
    (hf : ∀ i ∈ S, f i ∈ I) (hcard : q ≤ S.card) : ∏ i ∈ S, f i = 0 := by
  have he : I ^ S.card ≤ I ^ q := Ideal.pow_le_pow_right hcard
  have hm := he (prod_mem_ideal_pow I S f hf)
  simpa only [hq, Submodule.mem_bot] using hm

/-- The subset expansion (11) with all terms of degree at least `q` removed
by nilpotence. -/
theorem algebra_product_truncated {A : Type*} [CommRing A] [Algebra ℂ A]
    {N : ℕ} (I : Ideal A) (q : ℕ) (hq : I ^ q = ⊥)
    (ell : A →ₗ[ℂ] ℂ) (a : Fin N → ℂ) (n : Fin N → A)
    (hn : ∀ i, n i ∈ I) :
    ell (∏ i, (algebraMap ℂ A (a i) + n i)) =
      ∑ S : Finset (Fin N), if S.card < q then
        ell (∏ i ∈ S, n i) * (∏ i ∈ Sᶜ, a i) else 0 := by
  classical
  have hex : (∏ i, (algebraMap ℂ A (a i) + n i)) =
      ∑ S : Finset (Fin N),
        (∏ i ∈ Sᶜ, a i) • (∏ i ∈ S, n i) := by
    simp_rw [add_comm (algebraMap ℂ A (a _))]
    rw [Finset.prod_add]
    have hpow : (Finset.univ : Finset (Fin N)).powerset = Finset.univ := by ext S; simp
    rw [hpow]
    apply Finset.sum_congr rfl
    intro S _
    rw [Algebra.smul_def, map_prod]
    simp only [← Finset.compl_eq_univ_sdiff]
    ring
  rw [hex, map_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [map_smul, smul_eq_mul, mul_comm]
  by_cases h : S.card < q
  · rw [if_pos h]
  · rw [if_neg h]
    rw [prod_eq_zero_of_ideal_pow_eq_bot I q hq S n (fun i _ => hn i) (by omega), map_zero, zero_mul]

end UniformBorderRank
