import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import GeometricMedianCoresets.Basic
import GeometricMedianCoresets.FeatureMap

/-!
# Cost-difference identity (paper Lemma 2.2, equations (5)–(6))
-/

noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace GeometricMedianCoresets
namespace SquaredMetric

variable {X : Type*} (S : SquaredMetric X)

/-- `‖u - v‖^2 = ‖u‖^2 - 2⟪u,v⟫ + ‖v‖^2` over a real inner product space. -/
theorem norm_sub_sq_eq (u v : S.H) :
    ‖u - v‖ ^ 2 = ‖u‖ ^ 2 - 2 * ⟪u, v⟫ + ‖v‖ ^ 2 := by
  have h2 : ⟪u - v, u - v⟫ = ⟪u, u⟫ - 2 * ⟪u, v⟫ + ⟪v, v⟫ :=
    real_inner_sub_sub_self u v
  have h3 : ⟪u, u⟫ = ‖u‖ ^ 2 := real_inner_self_eq_norm_sq u
  have h4 : ⟪v, v⟫ = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
  calc ‖u - v‖ ^ 2 = ⟪u - v, u - v⟫ := (real_inner_self_eq_norm_sq (u - v)).symm
    _ = ⟪u, u⟫ - 2 * ⟪u, v⟫ + ⟪v, v⟫ := h2
    _ = ‖u‖ ^ 2 - 2 * ⟪u, v⟫ + ‖v‖ ^ 2 := by rw [h3, h4]

/-- Cost expansion (eq. (5)) for `n ≠ 0`. -/
theorem cost_eq_feature {n : ℕ} (hn : n ≠ 0) (A : Dataset X n) (z : X) :
    S.toDist.cost A z
      = ‖S.Φ z‖ ^ 2 - 2 * ⟪S.Φ z, S.v A⟫ + S.b A := by
  have hsum : (∑ i, S.d z (A i)) = ∑ i, ‖S.Φ z - S.Φ (A i)‖ ^ 2 :=
    Finset.sum_congr rfl (fun i _ => (S.dist_sq z (A i)).symm)
  have hsplit : ∑ i, ‖S.Φ z - S.Φ (A i)‖ ^ 2
      = (n : ℝ) * ‖S.Φ z‖ ^ 2
        - 2 * ⟪S.Φ z, ∑ i, S.Φ (A i)⟫
        + ∑ i, ‖S.Φ (A i)‖ ^ 2 := by
    have hinner : ∀ i : Fin n, ‖S.Φ z - S.Φ (A i)‖ ^ 2
        = ‖S.Φ z‖ ^ 2 - 2 * ⟪S.Φ z, S.Φ (A i)⟫ + ‖S.Φ (A i)‖ ^ 2 :=
      fun i => S.norm_sub_sq_eq (S.Φ z) (S.Φ (A i))
    rw [Finset.sum_congr rfl (fun i _ => hinner i)]
    have h1 : ∑ i : Fin n, (‖S.Φ z‖ ^ 2 - 2 * ⟪S.Φ z, S.Φ (A i)⟫ + ‖S.Φ (A i)‖ ^ 2)
        = ∑ i : Fin n, ‖S.Φ z‖ ^ 2
          + ∑ i : Fin n, (-2 * ⟪S.Φ z, S.Φ (A i)⟫)
          + ∑ i : Fin n, ‖S.Φ (A i)‖ ^ 2 := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    have hconst : ∑ _i : Fin n, ‖S.Φ z‖ ^ 2 = (n : ℝ) * ‖S.Φ z‖ ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hlin : ∑ i : Fin n, (-2 * ⟪S.Φ z, S.Φ (A i)⟫)
        = -2 * ⟪S.Φ z, ∑ i, S.Φ (A i)⟫ := by
      have hsuminner : ∑ i : Fin n, ⟪S.Φ z, S.Φ (A i)⟫
          = ⟪S.Φ z, ∑ i, S.Φ (A i)⟫ := by
        rw [← inner_sum]
      have hmul : ∑ i : Fin n, (-2 * ⟪S.Φ z, S.Φ (A i)⟫)
          = -2 * ∑ i : Fin n, ⟪S.Φ z, S.Φ (A i)⟫ := by
        rw [← Finset.mul_sum]
      rw [hmul, hsuminner]
    rw [h1, hconst, hlin]
    ring
  have hv : S.v A = (n : ℝ)⁻¹ • ∑ i, S.Φ (A i) := by
    show (if n = 0 then 0 else (n : ℝ)⁻¹ • ∑ i, S.Φ (A i)) = _
    rw [if_neg hn]
  have hb : S.b A = (n : ℝ)⁻¹ * ∑ i, ‖S.Φ (A i)‖ ^ 2 := by
    show (if n = 0 then 0 else (n : ℝ)⁻¹ * ∑ i, ‖S.Φ (A i)‖ ^ 2) = _
    rw [if_neg hn]
  show (∑ i, S.toDist.d z (A i)) / n = _
  have hd : S.toDist.d = S.d := rfl
  rw [hd, hsum, hsplit, hv, hb]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hsmul : ⟪S.Φ z, (n : ℝ)⁻¹ • ∑ i, S.Φ (A i)⟫
      = (n : ℝ)⁻¹ * ⟪S.Φ z, ∑ i, S.Φ (A i)⟫ :=
    real_inner_smul_right (S.Φ z) (∑ i, S.Φ (A i)) (n : ℝ)⁻¹
  rw [hsmul]
  field_simp

/-- Pairwise comparison error (eq. (6)). -/
theorem delta_eq_inner {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0)
    (P : Dataset X n) (Q : Dataset X m) (x y : X) :
    S.toDist.delta P Q x y
      = 2 * ⟪S.Φ x - S.Φ y, S.v Q - S.v P⟫ := by
  have hPz := fun z => S.cost_eq_feature hn P z
  have hQz := fun z => S.cost_eq_feature hm Q z
  unfold Dist.delta
  rw [hPz x, hPz y, hQz x, hQz y]
  have hcancel :
      (‖S.Φ x‖ ^ 2 - 2 * ⟪S.Φ x, S.v P⟫ + S.b P
        - (‖S.Φ y‖ ^ 2 - 2 * ⟪S.Φ y, S.v P⟫ + S.b P))
      - (‖S.Φ x‖ ^ 2 - 2 * ⟪S.Φ x, S.v Q⟫ + S.b Q
        - (‖S.Φ y‖ ^ 2 - 2 * ⟪S.Φ y, S.v Q⟫ + S.b Q))
      = 2 * ⟪S.Φ x - S.Φ y, S.v Q - S.v P⟫ := by
    have hinner : 2 * ⟪S.Φ x - S.Φ y, S.v Q - S.v P⟫
        = 2 * (⟪S.Φ x, S.v Q⟫ - ⟪S.Φ x, S.v P⟫
              - ⟪S.Φ y, S.v Q⟫ + ⟪S.Φ y, S.v P⟫) := by
      rw [inner_sub_left, inner_sub_right, inner_sub_right]
      ring
    rw [hinner]
    ring
  exact hcancel

theorem delta_anchor {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0)
    (P : Dataset X n) (Q : Dataset X m) (μ x : X) :
    S.toDist.delta P Q x μ
      = 2 * ⟪S.Φ x - S.Φ μ, S.v Q - S.v P⟫ :=
  S.delta_eq_inner hn hm P Q x μ

theorem b_eq_avg_norm_sq {n : ℕ} (hn : n ≠ 0) (A : Dataset X n) :
    S.b A = (n : ℝ)⁻¹ * ∑ i, ‖S.Φ (A i)‖ ^ 2 := by
  show (if n = 0 then 0 else (n : ℝ)⁻¹ * ∑ i, ‖S.Φ (A i)‖ ^ 2) = _
  rw [if_neg hn]

end SquaredMetric
end GeometricMedianCoresets
