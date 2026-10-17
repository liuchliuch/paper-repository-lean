import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.SetLike.Fintype
import Mathlib.Tactic

/-!
# Counting actual two-dimensional vector subspaces

The Grassmannian in this file consists of actual submodules with the specified
finite dimension. Its cardinality is derived by counting incident one- and
two-dimensional subspaces in two orders.
-/

namespace K44K35Free
open Module
open scoped LinearAlgebra.Projectivization

variable (F V : Type*) [Field F] [AddCommGroup V] [Module F V]

/-- Actual vector subspaces of a fixed dimension. -/
abbrev Grassmann (d : ℕ) := {P : Submodule F V // finrank F P = d}

noncomputable instance grassmannFintype [Finite V] (d : ℕ) :
    Fintype (Grassmann F V d) := Fintype.ofFinite _

variable {F V}

/-- Restriction identifies subspaces of `P` with ambient subspaces contained in `P`. -/
noncomputable def grassmannInSubmoduleEquiv (P : Submodule F V) (d : ℕ) :
    Grassmann F P d ≃ {Q : Grassmann F V d // Q.1 ≤ P} where
  toFun Q := ⟨⟨Q.1.map P.subtype, (Submodule.finrank_map_subtype_eq P Q.1).trans Q.2⟩,
    by simpa using (LinearMap.map_le_range (f := P.subtype) (p := Q.1))⟩
  invFun Q := ⟨Q.1.1.comap P.subtype,
    (Submodule.comapSubtypeEquivOfLe Q.2).finrank_eq.trans Q.1.2⟩
  left_inv Q := by
    apply Subtype.ext
    exact Submodule.comap_map_eq_of_injective P.injective_subtype Q.1
  right_inv Q := by
    apply Subtype.ext
    apply Subtype.ext
    simpa [Submodule.map_comap_eq, Submodule.range_subtype] using inf_eq_left.mpr Q.2

/-- Rank-nullity for restriction of the quotient map to a containing subspace. -/
theorem finrank_map_mkQ_add [FiniteDimensional F V]
    (P Q : Submodule F V) (hPQ : P ≤ Q) :
    finrank F (Q.map P.mkQ) + finrank F P = finrank F Q := by
  have h := LinearMap.finrank_range_add_finrank_ker (P.mkQ.domRestrict Q)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, Submodule.ker_mkQ,
    (Submodule.comapSubtypeEquivOfLe hPQ).finrank_eq] at h
  exact h

/-- Two-dimensional spaces containing a fixed line correspond to lines in the quotient. -/
noncomputable def planesContainingLineEquiv [FiniteDimensional F V]
    (P : Grassmann F V 1) :
    {Q : Grassmann F V 2 // P.1 ≤ Q.1} ≃ Grassmann F (V ⧸ P.1) 1 where
  toFun Q := ⟨Q.1.1.map P.1.mkQ, by
    have h := finrank_map_mkQ_add P.1 Q.1.1 Q.2
    rw [P.2, Q.1.2] at h
    omega⟩
  invFun R := ⟨⟨R.1.comap P.1.mkQ, by
    have h := finrank_map_mkQ_add P.1 (R.1.comap P.1.mkQ) (P.1.le_comap_mkQ R.1)
    rw [Submodule.map_comap_eq_of_surjective P.1.mkQ_surjective, R.2, P.2] at h
    omega⟩, P.1.le_comap_mkQ R.1⟩
  left_inv Q := by
    apply Subtype.ext
    apply Subtype.ext
    simp only [Submodule.comap_map_mkQ, sup_of_le_right Q.2]
  right_inv R := by
    apply Subtype.ext
    exact Submodule.map_comap_eq_of_surjective P.1.mkQ_surjective R.1

/-- The projectivization counts the actual one-dimensional subspaces. -/
theorem card_grassmann_one [Finite F] [Finite V] {n : ℕ}
    (hV : finrank F V = n) :
    Nat.card (Grassmann F V 1) = ∑ i ∈ Finset.range n, Nat.card F ^ i := by
  rw [← Nat.card_congr (Projectivization.equivSubmodule F V)]
  exact Projectivization.card_of_finrank F V hV

/-- Transposition of a finite incidence relation. -/
def sigmaRelationSwap {A B : Type*} (R : A → B → Prop) :
    (Σ a : A, {b : B // R a b}) ≃ (Σ b : B, {a : A // R a b}) where
  toFun p := ⟨p.2.1, p.1, p.2.2⟩
  invFun p := ⟨p.2.1, p.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Flags can first be indexed by either their plane or their line. -/
noncomputable def planeLineFlagsEquiv :
    (Σ P : Grassmann F V 2, Grassmann F P.1 1) ≃
      (Σ L : Grassmann F V 1, {P : Grassmann F V 2 // L.1 ≤ P.1}) :=
  (Equiv.sigmaCongrRight fun P : Grassmann F V 2 => grassmannInSubmoduleEquiv P.1 1).trans
    (sigmaRelationSwap (fun (P : Grassmann F V 2) (L : Grassmann F V 1) => L.1 ≤ P.1))

/-- Projective lines have exactly `q+1` points. -/
theorem card_grassmann_one_dim_two [Finite F] [Finite V]
    (hV : finrank F V = 2) :
    Nat.card (Grassmann F V 1) = Nat.card F + 1 := by
  simpa [Finset.sum_range_succ, add_comm] using card_grassmann_one hV

/-- Double counting line-plane flags in an actual finite vector space. -/
theorem grassmann_two_flag_count [Finite F] [Finite V] [FiniteDimensional F V]
    {n : ℕ} (hV : finrank F V = n) :
    Nat.card (Grassmann F V 2) * (Nat.card F + 1) =
      (∑ i ∈ Finset.range n, Nat.card F ^ i) *
        (∑ i ∈ Finset.range (n - 1), Nat.card F ^ i) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  have hleft : Nat.card (Σ P : Grassmann F V 2, Grassmann F P.1 1) =
      Nat.card (Grassmann F V 2) * (Nat.card F + 1) := by
    rw [Nat.card_sigma]
    calc
      _ = ∑ _P : Grassmann F V 2, (Nat.card F + 1) := by
        apply Finset.sum_congr rfl
        intro P _
        exact card_grassmann_one_dim_two P.2
      _ = _ := by simp [Nat.card_eq_fintype_card]
  have hquot : ∀ L : Grassmann F V 1,
      Nat.card {P : Grassmann F V 2 // L.1 ≤ P.1} =
        ∑ i ∈ Finset.range (n - 1), Nat.card F ^ i := by
    intro L
    rw [Nat.card_congr (planesContainingLineEquiv L)]
    apply card_grassmann_one
    have h := L.1.finrank_quotient_add_finrank
    rw [L.2, hV] at h
    omega
  have hright : Nat.card (Σ L : Grassmann F V 1,
      {P : Grassmann F V 2 // L.1 ≤ P.1}) =
      (∑ i ∈ Finset.range n, Nat.card F ^ i) *
        (∑ i ∈ Finset.range (n - 1), Nat.card F ^ i) := by
    rw [Nat.card_sigma]
    simp_rw [hquot]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [← Nat.card_eq_fintype_card, card_grassmann_one hV]
  rw [← hleft, Nat.card_congr planeLineFlagsEquiv, hright]

/-- The actual number of two-dimensional subspaces of a four-dimensional space:
`[4 choose 2]_q = (q²+1)(q²+q+1)`. -/
theorem card_grassmann_two_dim_four [Finite F] [Finite V] [FiniteDimensional F V]
    (hV : finrank F V = 4) :
    Nat.card (Grassmann F V 2) =
      (Nat.card F ^ 2 + 1) * (Nat.card F ^ 2 + Nat.card F + 1) := by
  have h := grassmann_two_flag_count hV
  norm_num [Finset.sum_range_succ] at h
  apply Nat.mul_right_cancel (m := Nat.card F + 1) (by omega)
  rw [Nat.card_eq_fintype_card, h]
  ring

/-- Quotient correspondence for any dimension, with a fixed one-dimensional base. -/
noncomputable def grassmannContainingLineEquiv [FiniteDimensional F V]
    (L : Grassmann F V 1) (d : ℕ) :
    {P : Grassmann F V (d + 1) // L.1 ≤ P.1} ≃ Grassmann F (V ⧸ L.1) d where
  toFun P := ⟨P.1.1.map L.1.mkQ, by
    have h := finrank_map_mkQ_add L.1 P.1.1 P.2
    rw [L.2, P.1.2] at h
    omega⟩
  invFun R := ⟨⟨R.1.comap L.1.mkQ, by
    have h := finrank_map_mkQ_add L.1 (R.1.comap L.1.mkQ) (L.1.le_comap_mkQ R.1)
    rw [Submodule.map_comap_eq_of_surjective L.1.mkQ_surjective, R.2, L.2] at h
    omega⟩, L.1.le_comap_mkQ R.1⟩
  left_inv P := by
    apply Subtype.ext
    apply Subtype.ext
    simp only [Submodule.comap_map_mkQ, sup_of_le_right P.2]
  right_inv R := by
    apply Subtype.ext
    exact Submodule.map_comap_eq_of_surjective L.1.mkQ_surjective R.1

/-- The exact geometric count used in Lemma 7: projective planes through a point
in a projective four-space. Here `V` is its five-dimensional vector space. -/
theorem card_projective_planes_through_point [Finite F] [Finite V] [FiniteDimensional F V]
    (hV : finrank F V = 5) (L : Grassmann F V 1) :
    Nat.card {P : Grassmann F V 3 // L.1 ≤ P.1} =
      (Nat.card F ^ 2 + 1) * (Nat.card F ^ 2 + Nat.card F + 1) := by
  letI : Fintype V := Fintype.ofFinite V
  rw [Nat.card_congr (grassmannContainingLineEquiv L 2)]
  apply card_grassmann_two_dim_four
  have h := L.1.finrank_quotient_add_finrank
  rw [L.2, hV] at h
  omega

/-- Two-dimensional subspaces in dimension five, obtained from the same flag count. -/
theorem card_grassmann_two_dim_five [Finite F] [Finite V] [FiniteDimensional F V]
    (hV : finrank F V = 5) :
    Nat.card (Grassmann F V 2) =
      Nat.card F ^ 6 + Nat.card F ^ 5 + 2 * Nat.card F ^ 4 + 2 * Nat.card F ^ 3 +
        2 * Nat.card F ^ 2 + Nat.card F + 1 := by
  have h := grassmann_two_flag_count hV
  norm_num [Finset.sum_range_succ] at h
  apply Nat.mul_right_cancel (m := Nat.card F + 1) (by omega)
  rw [Nat.card_eq_fintype_card, h]
  ring

/-- Line-subspace flags in arbitrary fixed dimension. -/
noncomputable def grassmannLineFlagsEquiv (d : ℕ) :
    (Σ P : Grassmann F V d, Grassmann F P.1 1) ≃
      (Σ L : Grassmann F V 1, {P : Grassmann F V d // L.1 ≤ P.1}) :=
  (Equiv.sigmaCongrRight fun P : Grassmann F V d => grassmannInSubmoduleEquiv P.1 1).trans
    (sigmaRelationSwap (fun (P : Grassmann F V d) (L : Grassmann F V 1) => L.1 ≤ P.1))

/-- Projective planes have exactly `q²+q+1` points. -/
theorem card_grassmann_one_dim_three [Finite F] [Finite V]
    (hV : finrank F V = 3) :
    Nat.card (Grassmann F V 1) = Nat.card F ^ 2 + Nat.card F + 1 := by
  have h := card_grassmann_one hV
  norm_num [Finset.sum_range_succ] at h
  rw [Nat.card_eq_fintype_card, h]
  ring

/-- The true Gaussian count `[6 choose 3]_q`, as a polynomial with positive coefficients. -/
theorem card_grassmann_three_dim_six [Finite F] [Finite V] [FiniteDimensional F V]
    (hV : finrank F V = 6) :
    Nat.card (Grassmann F V 3) =
      Nat.card F ^ 9 + Nat.card F ^ 8 + 2 * Nat.card F ^ 7 + 3 * Nat.card F ^ 6 +
        3 * Nat.card F ^ 5 + 3 * Nat.card F ^ 4 + 3 * Nat.card F ^ 3 +
          2 * Nat.card F ^ 2 + Nat.card F + 1 := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  let q := Nat.card F
  let P₂ := q ^ 6 + q ^ 5 + 2 * q ^ 4 + 2 * q ^ 3 + 2 * q ^ 2 + q + 1
  have hleft : Nat.card (Σ P : Grassmann F V 3, Grassmann F P.1 1) =
      Nat.card (Grassmann F V 3) * (q ^ 2 + q + 1) := by
    rw [Nat.card_sigma]
    calc
      _ = ∑ _P : Grassmann F V 3, (q ^ 2 + q + 1) := by
        apply Finset.sum_congr rfl
        intro P _
        exact card_grassmann_one_dim_three P.2
      _ = _ := by simp [Nat.card_eq_fintype_card]
  have hquot : ∀ L : Grassmann F V 1,
      Nat.card {P : Grassmann F V 3 // L.1 ≤ P.1} = P₂ := by
    intro L
    rw [Nat.card_congr (grassmannContainingLineEquiv L 2)]
    apply card_grassmann_two_dim_five
    have h := L.1.finrank_quotient_add_finrank
    rw [L.2, hV] at h
    omega
  have hright : Nat.card (Σ L : Grassmann F V 1,
      {P : Grassmann F V 3 // L.1 ≤ P.1}) =
      (∑ i ∈ Finset.range 6, q ^ i) * P₂ := by
    rw [Nat.card_sigma]
    simp_rw [hquot]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [← Nat.card_eq_fintype_card, card_grassmann_one hV]
  have hflags : Nat.card (Grassmann F V 3) * (q ^ 2 + q + 1) =
      (∑ i ∈ Finset.range 6, q ^ i) * P₂ := by
    rw [← hleft, Nat.card_congr (grassmannLineFlagsEquiv 3), hright]
  apply Nat.mul_right_cancel (m := q ^ 2 + q + 1) (by omega)
  rw [hflags]
  norm_num [Finset.sum_range_succ]
  dsimp [P₂, q]
  ring

/-- Uniform `O(q⁹)` bound for the actual projective planes of projective five-space. -/
theorem card_grassmann_three_dim_six_le [Finite F] [Finite V] [FiniteDimensional F V]
    (hV : finrank F V = 6) :
    Nat.card (Grassmann F V 3) ≤ 20 * Nat.card F ^ 9 := by
  rw [card_grassmann_three_dim_six hV]
  have hq : 1 ≤ Nat.card F := le_of_lt (Finite.one_lt_card (α := F))
  have h₀ : 1 ≤ Nat.card F ^ 9 := one_le_pow₀ hq
  have h₁ : Nat.card F ≤ Nat.card F ^ 9 := by simpa using Nat.pow_le_pow_right hq (by norm_num : 1 ≤ 9)
  have h₂ : Nat.card F ^ 2 ≤ Nat.card F ^ 9 := Nat.pow_le_pow_right hq (by norm_num)
  have h₃ : Nat.card F ^ 3 ≤ Nat.card F ^ 9 := Nat.pow_le_pow_right hq (by norm_num)
  have h₄ : Nat.card F ^ 4 ≤ Nat.card F ^ 9 := Nat.pow_le_pow_right hq (by norm_num)
  have h₅ : Nat.card F ^ 5 ≤ Nat.card F ^ 9 := Nat.pow_le_pow_right hq (by norm_num)
  have h₆ : Nat.card F ^ 6 ≤ Nat.card F ^ 9 := Nat.pow_le_pow_right hq (by norm_num)
  have h₇ : Nat.card F ^ 7 ≤ Nat.card F ^ 9 := Nat.pow_le_pow_right hq (by norm_num)
  have h₈ : Nat.card F ^ 8 ≤ Nat.card F ^ 9 := Nat.pow_le_pow_right hq (by norm_num)
  omega

/-- Restricting to a containing space also preserves the incidence with a fixed subspace. -/
noncomputable def grassmannThroughInsideEquiv
    (H L : Submodule F V) (hLH : L ≤ H) (d : ℕ) :
    {P : Grassmann F V d // L ≤ P.1 ∧ P.1 ≤ H} ≃
      {Q : Grassmann F H d // L.comap H.subtype ≤ Q.1} where
  toFun P := ⟨⟨P.1.1.comap H.subtype,
      (Submodule.comapSubtypeEquivOfLe P.2.2).finrank_eq.trans P.1.2⟩,
    Submodule.comap_mono P.2.1⟩
  invFun Q := ⟨⟨Q.1.1.map H.subtype,
      (Submodule.finrank_map_subtype_eq H Q.1.1).trans Q.1.2⟩,
    ⟨by
      have hm := Submodule.map_mono (f := H.subtype) Q.2
      rw [Submodule.map_comap_eq, Submodule.range_subtype, inf_eq_right.mpr hLH] at hm
      exact hm,
      H.map_subtype_le Q.1.1⟩⟩
  left_inv P := by
    apply Subtype.ext
    apply Subtype.ext
    simpa [Submodule.map_comap_eq, Submodule.range_subtype] using inf_eq_left.mpr P.2.2
  right_inv Q := by
    apply Subtype.ext
    apply Subtype.ext
    exact Submodule.comap_map_eq_of_injective H.injective_subtype Q.1.1

/-- The ambient-space version of Lemma 7's geometric count, with both incidence
requirements explicitly present. -/
theorem card_projective_planes_through_point_in_hyperplane
    [Finite F] [Finite V] [FiniteDimensional F V]
    (H L : Submodule F V) (hH : finrank F H = 5) (hL : finrank F L = 1)
    (hLH : L ≤ H) :
    Nat.card {P : Grassmann F V 3 // L ≤ P.1 ∧ P.1 ≤ H} =
      (Nat.card F ^ 2 + 1) * (Nat.card F ^ 2 + Nat.card F + 1) := by
  rw [Nat.card_congr (grassmannThroughInsideEquiv H L hLH 3)]
  exact card_projective_planes_through_point hH
    ⟨L.comap H.subtype, (Submodule.comapSubtypeEquivOfLe hLH).finrank_eq.trans hL⟩

/-- Factored form of the total plane count in projective five-space. -/
theorem card_grassmann_three_dim_six_factor
    [Finite F] [Finite V] [FiniteDimensional F V] (hV : finrank F V = 6) :
    Nat.card (Grassmann F V 3) =
      (Nat.card F ^ 3 + 1) * (Nat.card F ^ 2 + 1) *
        (Nat.card F ^ 4 + Nat.card F ^ 3 + Nat.card F ^ 2 + Nat.card F + 1) := by
  rw [card_grassmann_three_dim_six hV]
  ring

/-- The exact number `[5 choose 2]_q` of planes through a point in projective five-space. -/
theorem card_projective_planes_through_point_dim_six
    [Finite F] [Finite V] [FiniteDimensional F V]
    (hV : finrank F V = 6) (L : Grassmann F V 1) :
    Nat.card {P : Grassmann F V 3 // L.1 ≤ P.1} =
      Nat.card F ^ 6 + Nat.card F ^ 5 + 2 * Nat.card F ^ 4 + 2 * Nat.card F ^ 3 +
        2 * Nat.card F ^ 2 + Nat.card F + 1 := by
  letI : Fintype V := Fintype.ofFinite V
  rw [Nat.card_congr (grassmannContainingLineEquiv L 2)]
  apply card_grassmann_two_dim_five
  have h := L.1.finrank_quotient_add_finrank
  rw [hV, L.2] at h
  omega

/-- The fraction of all projective planes containing a prescribed point is
`1/(q³+1)`, here expressed as an exact integral identity. -/
theorem card_planes_through_point_dim_six_mul
    [Finite F] [Finite V] [FiniteDimensional F V]
    (hV : finrank F V = 6) (L : Grassmann F V 1) :
    Nat.card {P : Grassmann F V 3 // L.1 ≤ P.1} * (Nat.card F ^ 3 + 1) =
      Nat.card (Grassmann F V 3) := by
  letI : Fintype V := Fintype.ofFinite V
  rw [Nat.card_congr (grassmannContainingLineEquiv L 2)]
  have hquot : finrank F (V ⧸ L.1) = 5 := by
    have h := L.1.finrank_quotient_add_finrank
    rw [hV, L.2] at h
    omega
  rw [card_grassmann_two_dim_five hquot, card_grassmann_three_dim_six hV]
  ring

/-- The main term in the exact Gaussian count is `q⁹`. -/
theorem pow_nine_le_card_grassmann_three_dim_six
    [Finite F] [Finite V] [FiniteDimensional F V] (hV : finrank F V = 6) :
    Nat.card F ^ 9 ≤ Nat.card (Grassmann F V 3) := by
  rw [card_grassmann_three_dim_six hV]
  omega

end K44K35Free
