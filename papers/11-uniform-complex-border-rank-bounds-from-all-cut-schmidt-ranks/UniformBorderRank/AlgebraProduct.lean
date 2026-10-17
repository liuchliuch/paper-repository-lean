import UniformBorderRank.Polarization
import UniformBorderRank.LocalAlgebra
import UniformBorderRank.BorderRank
import UniformBorderRank.RankOps
import UniformBorderRank.Comb

/-! Assembly of polarization and coefficient degenerations for a nilpotent
ideal. This is the local-factor estimate in Proposition 3.2. -/
noncomputable section
namespace UniformBorderRank
open Finset Module

def algebraDegreeTensor {N : ℕ} {d : Fin N → ℕ} {E A : Type*}
    [AddCommGroup E] [Module ℂ E] [CommRing A] [Algebra ℂ A]
    (ell : A →ₗ[ℂ] ℂ) (f : E →ₗ[ℂ] A) (a : ∀ i, Fin (d i) → ℂ)
    (n : ∀ i, Fin (d i) → E) (k : ℕ) : Coeffs d := fun u =>
  ∑ S ∈ powersetCard k (univ : Finset (Fin N)),
    ell (∏ i ∈ S, f (n i (u i))) * ∏ i ∈ Sᶜ, a i (u i)

theorem borderRankLe_algebraDegreeTensor {N : ℕ} {d : Fin N → ℕ} (hN : 0 < N)
    {E A : Type*} [AddCommGroup E] [Module ℂ E] [CommRing A] [Algebra ℂ A]
    {s : ℕ} (B : Basis (Fin s) ℂ E) (ell : A →ₗ[ℂ] ℂ) (f : E →ₗ[ℂ] A)
    (a : ∀ i, Fin (d i) → ℂ) (n : ∀ i, Fin (d i) → E) (k : ℕ) :
    borderRankLe (algebraDegreeTensor ell f a n k) ((k + 1) * (s + k - 1).choose k) := by
  classical
  obtain ⟨eta, c, hc⟩ := pure_power_decomposition B f ell k
  have he : algebraDegreeTensor ell f a n k =
      ∑ j : Fin ((s + k - 1).choose k),
        c j • prodCurveCoeff d a (fun i x => eta j (n i x)) k := by
    ext u
    change (∑ S ∈ powersetCard k (univ : Finset (Fin N)),
      ell (∏ i ∈ S, f (n i (u i))) * ∏ i ∈ Sᶜ, a i (u i)) = _
    have hpower (S : Finset (Fin N)) (hS : S ∈ powersetCard k univ) :
        ell (∏ i ∈ S, f (n i (u i))) =
          ∑ j, c j * ∏ i ∈ S, eta j (n i (u i)) := by
      have hh := hc S (by simpa only [Fintype.card_coe] using (mem_powersetCard.mp hS).2)
        (fun i => n i (u i))
      have hleft : (∏ i : S, f (n i (u i))) = ∏ i ∈ S, f (n i (u i)) :=
        Finset.prod_coe_sort S (fun i : Fin N => f (n i (u i)))
      have hright (j : Fin ((s + k - 1).choose k)) :
          (∏ i : S, eta j (n i (u i))) = ∏ i ∈ S, eta j (n i (u i)) :=
        Finset.prod_coe_sort S (fun i : Fin N => eta j (n i (u i)))
      simpa only [hleft, hright] using hh
    calc
      _ = ∑ S ∈ powersetCard k (univ : Finset (Fin N)),
          ∑ j, c j * ((∏ i ∈ S, eta j (n i (u i))) * ∏ i ∈ Sᶜ, a i (u i)) := by
        apply sum_congr rfl
        intro S hS
        rw [hpower S hS, sum_mul]
        apply sum_congr rfl
        intro j _
        ring
      _ = _ := by
        rw [sum_comm]
        simp [prodCurveCoeff, Finset.sum_apply, mul_sum]
  rw [he]
  have hb := borderRankLe_finset_sum univ
    (fun j : Fin ((s + k - 1).choose k) =>
      c j • prodCurveCoeff d a (fun i x => eta j (n i x)) k)
    (fun _ => k + 1) (fun j _ => borderRankLe_smul hN (c j)
      (borderRankLe_prodCurveCoeff d hN a (fun i x => eta j (n i x)) k))
  simpa only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_comm] using hb

lemma sum_powersetCard_range {N : ℕ} {M : Type*} [AddCommMonoid M]
    (q : ℕ) (F : Finset (Fin N) → M) :
    (∑ k ∈ range q, ∑ S ∈ powersetCard k (univ : Finset (Fin N)), F S) =
      ∑ S : Finset (Fin N), if S.card < q then F S else 0 := by
  classical
  have he (k : ℕ) : powersetCard k (univ : Finset (Fin N)) =
      (univ : Finset (Finset (Fin N))).filter (fun S => S.card = k) := by
    ext S
    simp [mem_powersetCard]
  simp_rw [he, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro S _
  simp [eq_comm]

/-- Local estimate with explicit length data: a codimension-one nilpotent
ideal with `I^q=0` gives the paper's `F(q)` bound, uniformly in tensor order. -/
theorem borderRankLe_local_product {N : ℕ} {d : Fin N → ℕ} (hN : 0 < N)
    {A : Type*} [CommRing A] [Algebra ℂ A] (I : Ideal A)
    (q : ℕ) (hq : 1 ≤ q) (hzero : I ^ q = ⊥)
    (B : Basis (Fin (q - 1)) ℂ (I.restrictScalars ℂ))
    (ell : A →ₗ[ℂ] ℂ) (a : ∀ i, Fin (d i) → ℂ)
    (n : ∀ i, Fin (d i) → I.restrictScalars ℂ) :
    borderRankLe (fun u => ell (∏ i, (algebraMap ℂ A (a i (u i)) + (n i (u i)).val)))
      (F q) := by
  classical
  let T : Coeffs d := fun u => ell (∏ i, (algebraMap ℂ A (a i (u i)) + (n i (u i)).val))
  have he : T = ∑ k ∈ range q,
      algebraDegreeTensor ell (I.restrictScalars ℂ).subtype a n k := by
    ext u
    rw [Finset.sum_apply]
    unfold algebraDegreeTensor
    rw [sum_powersetCard_range]
    exact algebra_product_truncated I q hzero ell (fun i => a i (u i))
      (fun i => (n i (u i)).val) (fun i => (n i (u i)).property)
  have hb := borderRankLe_finset_sum (range q)
    (fun k => algebraDegreeTensor ell (I.restrictScalars ℂ).subtype a n k)
    (fun k => (k + 1) * (q - 1 + k - 1).choose k)
    (fun k _ => borderRankLe_algebraDegreeTensor hN B ell _ a n k)
  have hsum : (∑ k ∈ range q, (k + 1) * (q - 1 + k - 1).choose k) = F q := by
    have hm : ∀ k, q - 1 + k - 1 = q + k - 2 := by omega
    simp_rw [hm]
    change Fsum q = F q
    by_cases hq1 : q = 1
    · subst q; simp [Fsum]
    · exact Fsum_eq_F q (by omega)
  rw [hsum, ← he] at hb
  exact hb

end UniformBorderRank
