import Paper06.MatchLaw
import Paper06.Posterior
import Mathlib.Data.Fintype.Perm
import Mathlib.Logic.Equiv.Prod
import Mathlib.LinearAlgebra.Pi

open Real Set BigOperators
open scoped Classical

namespace Paper06.Matching

variable {R : Type*} [Fintype R] [CommRing R] [Nontrivial R]

theorem card_ne_zero : (Fintype.card R : ℝ) ≠ 0 := by
  exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card R))

/-- The edge leaves the input at either endpoint uniform after the other
endpoint has been observed. -/
theorem edgeW_input_sum (z : R × R) (x : R) :
    (∑ a : R, edgeW z (x, a)) = (Fintype.card R : ℝ) ^ (-3 : ℤ) := by
  classical
  unfold edgeW
  rw [← Finset.mul_sum]
  have h : (∑ a : R, if z.2 + a = z.1 * x then (1 : ℝ) else 0) = 1 := by
    rw [Finset.sum_eq_single (z.1 * x - z.2)]
    · simp
    · intro a _ ha
      have hn : ¬ z.2 + a = z.1 * x := by
        intro he
        apply ha
        calc a = (z.2 + a) - z.2 := by ring
             _ = z.1 * x - z.2 := by rw [he]
      simp [hn]
    · simp
  rw [h, mul_one]

/-- Both one-site marginals are uniform on the input-output alphabet. -/
theorem edgeW_marginal (z : R × R) :
    (∑ z' : R × R, edgeW z z') = (Fintype.card R : ℝ) ^ (-2 : ℤ) := by
  change (∑ z' : R × R, edgeW z (z'.1, z'.2)) = _
  rw [Fintype.sum_prod_type' (fun x a => edgeW z (x, a))]
  simp_rw [edgeW_input_sum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc := card_ne_zero (R := R)
  simp only [zpow_neg, zpow_ofNat]
  field_simp

theorem edgeW_sum_one :
    (∑ zz : (R × R) × (R × R), edgeW zz.1 zz.2) = 1 := by
  rw [Fintype.sum_prod_type']
  simp_rw [edgeW_marginal]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul,
    Nat.cast_mul, zpow_neg, zpow_ofNat]
  have hc := card_ne_zero (R := R)
  field_simp

/-- The normalized finite-field CHSH edge distribution. -/
noncomputable def edgeLaw : FinProb ((R × R) × (R × R)) where
  w zz := edgeW zz.1 zz.2
  nonneg zz := edgeW_nonneg _ _
  sum_eq_one := edgeW_sum_one

/-- Labelled endpoints of `m` disjoint edges. -/
abbrev Sites (m : ℕ) := Fin m × Bool

noncomputable local instance sitesDecidableEq (m : ℕ) : DecidableEq (Sites m) :=
  Classical.decEq _

/-- Group the endpoints of each canonical edge. -/
def groupEndpoints (m : ℕ) (Z : Type*) : (Sites m → Z) ≃ (Fin m → Z × Z) where
  toFun z j := (z (j, false), z (j, true))
  invFun w i := if i.2 then (w i.1).2 else (w i.1).1
  left_inv z := by
    funext i
    rcases i with ⟨j, b⟩
    cases b <;> rfl
  right_inv w := by
    funext j
    rfl

/-- Product edge law for the canonical perfect matching. -/
noncomputable def canonicalW (m : ℕ) (z : Sites m → R × R) : ℝ :=
  ∏ j : Fin m, edgeW (z (j, false)) (z (j, true))

theorem canonicalW_nonneg (m : ℕ) (z : Sites m → R × R) :
    0 ≤ canonicalW m z :=
  Finset.prod_nonneg (fun _ _ => edgeW_nonneg _ _)

theorem canonicalW_sum_one (m : ℕ) :
    (∑ z : Sites m → R × R, canonicalW m z) = 1 := by
  have he : (∑ z : Sites m → R × R, canonicalW m z) =
      ∑ w : Fin m → (R × R) × (R × R), productW m (edgeLaw (R := R)) w := by
    exact Fintype.sum_equiv (groupEndpoints m (R × R)) _ _ (fun _ => rfl)
  rw [he, productW_sum_one]

/-- A uniformly relabelled product of independent edge laws.  Every
perfect matching occurs with the same number of endpoint labellings. -/
noncomputable def matchingW (m : ℕ) (z : Sites m → R × R) : ℝ :=
  (Fintype.card (Equiv.Perm (Sites m)) : ℝ)⁻¹ *
    ∑ σ : Equiv.Perm (Sites m), canonicalW m (z ∘ σ)

theorem matchingW_nonneg (m : ℕ) (z : Sites m → R × R) :
    0 ≤ matchingW m z := by
  unfold matchingW
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  exact Finset.sum_nonneg (fun _ _ => canonicalW_nonneg _ _)

theorem matchingW_sum_one (m : ℕ) :
    (∑ z : Sites m → R × R, matchingW m z) = 1 := by
  classical
  unfold matchingW
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hσ : ∀ σ : Equiv.Perm (Sites m),
      (∑ z : Sites m → R × R, canonicalW m (z ∘ σ)) = 1 := by
    intro σ
    let e : (Sites m → R × R) ≃ (Sites m → R × R) :=
      { toFun := fun z => z ∘ σ
        invFun := fun z => z ∘ σ.symm
        left_inv := by intro z; funext i; simp
        right_inv := by intro z; funext i; simp }
    exact (e.sum_comp (canonicalW m)).trans (canonicalW_sum_one m)
  simp_rw [hσ]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (by exact_mod_cast
    (ne_of_gt (Fintype.card_pos : 0 < Fintype.card (Equiv.Perm (Sites m)))))

/-- The random perfect-matching extension on `2m` sites. -/
noncomputable def matchingLaw (m : ℕ) : FinProb (Sites m → R × R) where
  w := matchingW m
  nonneg := matchingW_nonneg m
  sum_eq_one := matchingW_sum_one m

/-- Relabelling the observed coordinates preserves the matching law. -/
theorem matchingW_exchangeable (m : ℕ) (τ : Equiv.Perm (Sites m))
    (z : Sites m → R × R) : matchingW m (z ∘ τ) = matchingW m z := by
  classical
  unfold matchingW
  congr 1
  let e : Equiv.Perm (Sites m) ≃ Equiv.Perm (Sites m) :=
    { toFun := fun σ => σ.trans τ
      invFun := fun σ => σ.trans τ.symm
      left_inv := by
        intro σ
        apply Equiv.ext
        intro i
        exact τ.symm_apply_apply (σ i)
      right_inv := by
        intro σ
        apply Equiv.ext
        intro i
        exact τ.apply_symm_apply (σ i) }
  exact Fintype.sum_equiv e _ _ (fun σ => rfl)

theorem canonicalW_update (m : ℕ) (z : Sites m → R × R)
    (i : Sites m) (za : R × R) :
    canonicalW m (Function.update z i za) =
      edgeW (z (i.1, !i.2)) za *
        ∏ j ∈ Finset.univ.erase i.1, edgeW (z (j, false)) (z (j, true)) := by
  classical
  unfold canonicalW
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i.1)]
  have hrest : (∏ j ∈ Finset.univ.erase i.1,
      edgeW ((Function.update z i za) (j, false))
        ((Function.update z i za) (j, true))) =
      ∏ j ∈ Finset.univ.erase i.1, edgeW (z (j, false)) (z (j, true)) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i.1 := (Finset.mem_erase.mp hj).1
    have hf : (j, false) ≠ i := by intro he; exact hji (congrArg Prod.fst he)
    have ht : (j, true) ≠ i := by intro he; exact hji (congrArg Prod.fst he)
    simp [Function.update_of_ne hf, Function.update_of_ne ht]
  rw [hrest, mul_comm]
  congr 1
  rcases i with ⟨j, b⟩
  cases b
  · simp only [Bool.not_false, Function.update_self]
    have ht : (j, true) ≠ (j, false) := by simp
    rw [Function.update_of_ne ht, edgeW_symm]
  · simp only [Bool.not_true, Function.update_self]
    have hf : (j, false) ≠ (j, true) := by simp
    rw [Function.update_of_ne hf]

/-- The lifted fixed-input identity for one fixed perfect matching. -/
theorem canonicalW_fixedInput (m : ℕ) (z : Sites m → R × R)
    (i : Sites m) (x : R) :
    (∑ a : R, canonicalW m (Function.update z i (x, a))) =
      (∑ za : R × R, canonicalW m (Function.update z i za)) *
        (Fintype.card R : ℝ)⁻¹ := by
  simp_rw [canonicalW_update]
  rw [← Finset.sum_mul, edgeW_input_sum]
  rw [← Finset.sum_mul, edgeW_marginal]
  have hc := card_ne_zero (R := R)
  simp only [zpow_neg, zpow_ofNat]
  field_simp

/-- The lifted fixed-input identity survives averaging over matchings,
at every coordinate. -/
theorem matchingW_fixedInput (m : ℕ) (z : Sites m → R × R)
    (i : Sites m) (x : R) :
    (∑ a : R, matchingW m (Function.update z i (x, a))) =
      (∑ za : R × R, matchingW m (Function.update z i za)) *
        (Fintype.card R : ℝ)⁻¹ := by
  classical
  unfold matchingW
  simp_rw [Function.update_comp_equiv]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  conv_rhs => rw [Finset.sum_comm]
  simp_rw [canonicalW_fixedInput]
  rw [← Finset.sum_mul, mul_assoc]

/-- The vector-valued map specifying the input marginal. -/
noncomputable def inputMargLinear : ((R × R) → ℝ) →ₗ[ℝ] (R → ℝ) where
  toFun := inputMarg
  map_add' f g := by
    funext x
    exact Finset.sum_add_distrib
  map_smul' c f := by
    funext x
    exact (Finset.mul_sum _ _ _).symm

/-- Transport a finite law through a bijective relabelling of its sites. -/
noncomputable def reindexLaw {κ ι α : Type*} [Fintype κ] [Fintype ι] [Fintype α]
    [DecidableEq κ] [DecidableEq ι]
    (e : κ ≃ ι) (P : FinProb (κ → α)) : FinProb (ι → α) where
  w z := P.w (z ∘ e)
  nonneg z := P.nonneg _
  sum_eq_one := by
    let ee : (ι → α) ≃ (κ → α) :=
      { toFun := fun z => z ∘ e
        invFun := fun z => z ∘ e.symm
        left_inv := by intro z; funext i; simp
        right_inv := by intro z; funext i; simp }
    exact (ee.sum_comp P.w).trans P.sum_eq_one

/-- The matching extension with any chosen labels on its `2m` sites. -/
noncomputable def matchingLawAlong {κ : Type*} [Fintype κ] [DecidableEq κ]
    (m : ℕ) (e : Sites m ≃ κ) : FinProb (κ → R × R) :=
  reindexLaw e (matchingLaw m)

theorem matchingLawAlong_exchangeable {κ : Type*} [Fintype κ] [DecidableEq κ]
    (m : ℕ) (e : Sites m ≃ κ) (τ : Equiv.Perm κ) (z : κ → R × R) :
    (matchingLawAlong m e).w (z ∘ τ) = (matchingLawAlong m e).w z := by
  let σ : Equiv.Perm (Sites m) := (e.trans τ).trans e.symm
  have heq : (z ∘ τ) ∘ e = (z ∘ e) ∘ σ := by
    funext i
    simp [σ, Function.comp_def]
  change matchingW m ((z ∘ τ) ∘ e) = matchingW m (z ∘ e)
  rw [heq, matchingW_exchangeable]

theorem matchingLawAlong_fixedInput {κ : Type*} [Fintype κ] [DecidableEq κ]
    (m : ℕ) (e : Sites m ≃ κ) (z : κ → R × R) (i : κ) (x : R) :
    (∑ a : R, (matchingLawAlong m e).w (Function.update z i (x, a))) =
      (∑ za : R × R, (matchingLawAlong m e).w (Function.update z i za)) *
        (Fintype.card R : ℝ)⁻¹ := by
  change (∑ a : R, matchingW m ((Function.update z i (x, a)) ∘ e)) =
      (∑ za : R × R, matchingW m ((Function.update z i za) ∘ e)) * _
  simp_rw [Function.update_comp_equiv]
  exact matchingW_fixedInput m (z ∘ e) (e.symm i) x

/-- Canonical identification of `n` labels with paired endpoints when
`n` is even. -/
noncomputable def evenSitesEquiv (n : ℕ) (hn : Even n) : Sites (n / 2) ≃ Fin n := by
  apply Fintype.equivOfCardEq
  simp only [Sites, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  obtain ⟨m, hm⟩ := hn
  omega

/-- Equation (8), on the standard coordinate set `Fin n`, for every even
`n`.  This construction is independent of every later marginal size. -/
noncomputable def matchingLawFin (n : ℕ) (hn : Even n) :
    FinProb (Fin n → R × R) :=
  matchingLawAlong (n / 2) (evenSitesEquiv n hn)

theorem matchingLawFin_exchangeable (n : ℕ) (hn : Even n)
    (τ : Equiv.Perm (Fin n)) (z : Fin n → R × R) :
    (matchingLawFin n hn).w (z ∘ τ) = (matchingLawFin n hn).w z :=
  matchingLawAlong_exchangeable _ _ _ _

theorem matchingLawFin_fixedInput (n : ℕ) (hn : Even n)
    (z : Fin n → R × R) (i : Fin n) (x : R) :
    (∑ a : R, (matchingLawFin n hn).w (Function.update z i (x, a))) =
      (∑ za : R × R, (matchingLawFin n hn).w (Function.update z i za)) *
        (Fintype.card R : ℝ)⁻¹ :=
  matchingLawAlong_fixedInput _ _ _ _ _

/-- **Proposition 3.2.** The law in equation (8) is exchangeable and
satisfies the lifted fixed-input constraint at every one of its `n`
coordinates.  Its construction precedes every choice of marginal size. -/
theorem prop_3_2 (n : ℕ) (hn : Even n) :
    Posterior.Exchangeable (matchingLawFin (R := R) n hn) ∧
      ∀ i : Fin n, Posterior.LiftedCP (inputMargLinear (R := R))
        (uniformW R) (matchingLawFin n hn) i := by
  refine ⟨matchingLawFin_exchangeable n hn, ?_⟩
  intro i z
  funext x
  exact matchingLawFin_fixedInput n hn z i x

/-- Existence form of Proposition 3.2, with the full tensor constraint
and all quantifiers over the coordinate set retained. -/
theorem exists_admissible_matching_law (n : ℕ) (hn : Even n) :
    ∃ P : FinProb (Fin n → R × R), Posterior.Exchangeable P ∧
      ∀ i : Fin n, Posterior.LiftedCP (inputMargLinear (R := R)) (uniformW R) P i :=
  ⟨matchingLawFin n hn, prop_3_2 n hn⟩

end Paper06.Matching
