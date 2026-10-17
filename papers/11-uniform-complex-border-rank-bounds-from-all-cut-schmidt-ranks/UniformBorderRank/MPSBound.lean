import UniformBorderRank.ArtinProduct
import UniformBorderRank.Centralizer
import Mathlib.Data.Finset.NoncommProd

/-! Uniform border rank of a cross-commuting matrix product, allowing a
bounded number of internally noncommutative sites. -/
noncomputable section
namespace UniformBorderRank
open Finset Module

theorem borderRankLe_cross_commuting_product {N r : ℕ} {d : Fin N → ℕ}
    (hN : 0 < N) (hr : 1 ≤ r) (hd : ∀ i, d i ≤ r)
    (A : Fin N → Subalgebra ℂ (EndMat r))
    (hcross : ∀ i j, i ≠ j → CrossComm (A i : Set (EndMat r)) (A j : Set (EndMat r)))
    (v : ∀ i, Fin (d i) → EndMat r) (hv : ∀ i x, v i x ∈ A i)
    (ell : EndMat r →ₗ[ℂ] ℂ) :
    borderRankLe (fun u => ell (univ.noncommProd (fun i => v i (u i))
      (fun i _ j _ hij => hcross i j hij _ (hv i _) _ (hv j _))))
      (r ^ (r ^ 2 - 1) * F (r ^ 2)) := by
  classical
  let Q := noncommutativeSites A
  let G := Algebra.adjoin ℂ (goodGenerators A)
  letI : CommRing G := Algebra.adjoinCommRingOfComm ℂ (goodGenerators_commute A hcross)
  let emb : G →ₗ[ℂ] (Fin r → Fin r → ℂ) :=
    { toFun := fun x => x.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  haveI : FiniteDimensional ℂ G := FiniteDimensional.of_injective emb (fun x y h => Subtype.ext h)
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  haveI : Nontrivial G := by infer_instance
  have hq : Q.card ≤ r ^ 2 - 1 := (centralizer_algebras hr A hcross).1
  have hG : Module.finrank ℂ G ≤ r ^ 2 := goodAlgebra_finrank_le A
  have hmem (i : Fin N) (hi : i ∉ Q) (x : Fin (d i)) : v i x ∈ G := by
    apply Algebra.subset_adjoin
    refine ⟨i, ?_, hv i x⟩
    simpa only [Q, noncommutativeSites, mem_filter, mem_univ, true_and] using hi
  let B (gamma : ∀ i : Q, Fin (d i)) : EndMat r :=
    Q.noncommProd (fun i => if h : i ∈ Q then v i (gamma ⟨i, h⟩) else 1)
      (by
        intro i hi j hj hij
        dsimp only [Function.onFun]
        split_ifs <;> first
          | exact hcross i j hij _ (hv i _) _ (hv j _)
          | exact Commute.one_left _
          | exact Commute.one_right _)
  let g (gamma : ∀ i : Q, Fin (d i)) (i : Fin N) (x : Fin (d i)) : G :=
    if h : i ∈ Q then (if x = gamma ⟨i, h⟩ then 1 else 0)
      else ⟨v i x, hmem i h x⟩
  let ellG (gamma : ∀ i : Q, Fin (d i)) : G →ₗ[ℂ] ℂ :=
    ell.comp ((LinearMap.mulLeft ℂ (B gamma)).comp G.val.toLinearMap)
  let T (gamma : ∀ i : Q, Fin (d i)) : Coeffs d :=
    fun u => ellG gamma (∏ i, g gamma i (u i))
  have hT (gamma : ∀ i : Q, Fin (d i)) : borderRankLe (T gamma) (F (Module.finrank ℂ G)) :=
    borderRankLe_algebra_product hN (g gamma) (ellG gamma)
  have he : (fun u => ell (univ.noncommProd (fun i => v i (u i))
      (fun i _ j _ hij => hcross i j hij _ (hv i _) _ (hv j _)))) =
      ∑ gamma : (∀ i : Q, Fin (d i)), T gamma := by
    ext u
    let gamma₀ : ∀ i : Q, Fin (d i) := fun i => u i
    rw [Finset.sum_apply, Finset.sum_eq_single gamma₀]
    · have hg (i : Fin N) (hi : i ∈ Q) : g gamma₀ i (u i) = 1 := by simp [g, hi, gamma₀]
      have hgood (i : Fin N) (hi : i ∈ Qᶜ) : (g gamma₀ i (u i)).val = v i (u i) := by
        simp [g, mem_compl.mp hi]
      have hprodG : (∏ i, g gamma₀ i (u i)) = ∏ i ∈ Qᶜ, g gamma₀ i (u i) := by
        symm
        exact Finset.prod_subset (subset_univ Qᶜ) (fun i _ hi => hg i (by simpa using hi))
      have hval : ((∏ i, g gamma₀ i (u i)) : G).val =
          Qᶜ.noncommProd (fun i => v i (u i))
            (fun i _ j _ hij => hcross i j hij _ (hv i _) _ (hv j _)) := by
        rw [hprodG, ← Finset.noncommProd_eq_prod]
        have hm := Finset.map_noncommProd Qᶜ (fun i => g gamma₀ i (u i))
          (fun _ _ _ _ _ => Commute.all _ _) G.val.toMonoidHom
        calc
          _ = Qᶜ.noncommProd (fun i => (g gamma₀ i (u i)).val)
              (fun _ _ _ _ _ => (Commute.all _ _).map G.val.toMonoidHom) := hm
          _ = _ := by
            apply Finset.noncommProd_congr rfl
            intro i hi
            exact hgood i hi
      have hb : B gamma₀ = Q.noncommProd (fun i => v i (u i))
          (fun i _ j _ hij => hcross i j hij _ (hv i _) _ (hv j _)) := by
        apply Finset.noncommProd_congr rfl
        intro i hi
        simp [gamma₀, hi]
      have hs := Finset.noncommProd_union_of_disjoint (show Disjoint Q Qᶜ from disjoint_compl_right)
        (fun i => v i (u i))
        (fun i _ j _ hij => hcross i j hij _ (hv i _) _ (hv j _))
      simp only [union_compl] at hs
      change ell _ = ell (B gamma₀ * ((∏ i, g gamma₀ i (u i)) : G).val)
      rw [hb, hval, ← hs]
    · intro gamma _ hne
      have hn : ∃ i : Q, gamma i ≠ u i := by
        simpa [gamma₀, funext_iff] using hne
      obtain ⟨i, hi⟩ := hn
      have hzero : g gamma i (u i) = 0 := by
        simp [g, i.property, Ne.symm hi]
      have hp : (∏ j, g gamma j (u j)) = 0 := Finset.prod_eq_zero (mem_univ i.val) hzero
      simp only [T, hp, map_zero]
    · simp
  have hcount : Fintype.card (∀ i : Q, Fin (d i)) ≤ r ^ Q.card := by
    rw [Fintype.card_pi]
    calc
      _ ≤ ∏ _i : Q, r := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => by simpa using hd i)
      _ = _ := by simp
  have hbound : (∑ _gamma : (∀ i : Q, Fin (d i)), F (Module.finrank ℂ G)) ≤
      r ^ (r ^ 2 - 1) * F (r ^ 2) := by
    simp only [sum_const, card_univ, smul_eq_mul]
    exact Nat.mul_le_mul (hcount.trans (Nat.pow_le_pow_right (by omega) hq))
      (F_mono Module.finrank_pos hG)
  rw [he]
  exact borderRankLe_mono hN hbound (borderRankLe_finset_sum univ T
    (fun _ => F (Module.finrank ℂ G)) (fun gamma _ => hT gamma))

end UniformBorderRank
