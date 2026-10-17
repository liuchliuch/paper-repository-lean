/-
Copyright (c) 2026. Field-uniform canonical-path comparison, Appendix A.2.
-/
import Paper09.Ising
import Paper09.SoftShell
import Paper09.Dynamics
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

open Finset BigOperators Classical Real

noncomputable section
namespace Paper09
namespace CanonicalPath

variable {V : Type*} [Fintype V]

/-- Replace the coordinates in `D` by those of the terminal configuration. -/
def hybrid (D : Finset V) (α γ : Config V) : Config V :=
  fun x => if x ∈ D then γ x else α x

/-- The two directed orientations of each interaction crossing the cut. -/
def cutEdges (Λ : Lattice V) (D : Finset V) : Finset (V × V) :=
  univ.filter fun e => Λ.adj e.1 e.2 ∧ ¬ (e.1 ∈ D ↔ e.2 ∈ D)

theorem field_cancellation (h : V → ℝ) (B D : Finset V) (α γ : Config V) :
    Lattice.fieldEnergy h B α + Lattice.fieldEnergy h B γ =
      Lattice.fieldEnergy h B (hybrid D α γ) +
        Lattice.fieldEnergy h B (hybrid D γ α) := by
  simp only [Lattice.fieldEnergy, ← sum_add_distrib]
  apply sum_congr rfl
  intro x hx
  by_cases hd : x ∈ D <;> simp [hybrid, hd] <;> ring

theorem boundary_cancellation (Λ : Lattice V) (β : ℝ) (B S D : Finset V)
    (φ α γ : Config V) :
    Lattice.boundEnergy Λ β B S φ α + Lattice.boundEnergy Λ β B S φ γ =
      Lattice.boundEnergy Λ β B S φ (hybrid D α γ) +
        Lattice.boundEnergy Λ β B S φ (hybrid D γ α) := by
  simp only [Lattice.boundEnergy, ← mul_add, ← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro x hx
  apply sum_congr rfl
  intro y hy
  by_cases hd : x ∈ D <;> by_cases he : Λ.adj x y <;>
    simp [hybrid, hd, he] <;> ring

theorem abs_spinVal_sub_le (s t : Spin) : |spinVal s - spinVal t| ≤ 2 := by
  unfold spinVal
  split_ifs <;> norm_num

private theorem interaction_term_le (Λ : Lattice V) (D : Finset V)
    (α γ : Config V) (x y : V) :
    (if Λ.adj x y then spinVal (α x) * spinVal (α y) else 0) +
      (if Λ.adj x y then spinVal (γ x) * spinVal (γ y) else 0) -
      (if Λ.adj x y then spinVal (hybrid D α γ x) *
        spinVal (hybrid D α γ y) else 0) -
      (if Λ.adj x y then spinVal (hybrid D γ α x) *
        spinVal (hybrid D γ α y) else 0) ≤
      if Λ.adj x y ∧ ¬ (x ∈ D ↔ y ∈ D) then 4 else 0 := by
  by_cases he : Λ.adj x y
  · simp only [if_pos he, he, true_and]
    by_cases hx : x ∈ D <;> by_cases hy : y ∈ D
    · simp [hybrid, hx, hy] <;> ring_nf <;> exact le_refl _
    · simp only [hybrid, if_pos hx, if_neg hy]
      simp only [if_true]
      rw [if_pos (by simp [hx, hy])]
      have h := abs_mul (spinVal (α x) - spinVal (γ x))
        (spinVal (α y) - spinVal (γ y))
      have hb := mul_le_mul (abs_spinVal_sub_le (α x) (γ x))
        (abs_spinVal_sub_le (α y) (γ y)) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2)
      have ha := le_abs_self ((spinVal (α x) - spinVal (γ x)) *
        (spinVal (α y) - spinVal (γ y)))
      nlinarith
    · simp only [hybrid, if_neg hx, if_pos hy]
      simp only [if_true]
      rw [if_pos (by simp [hx, hy])]
      have h := abs_mul (spinVal (α x) - spinVal (γ x))
        (spinVal (α y) - spinVal (γ y))
      have hb := mul_le_mul (abs_spinVal_sub_le (α x) (γ x))
        (abs_spinVal_sub_le (α y) (γ y)) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2)
      have ha := le_abs_self ((spinVal (α x) - spinVal (γ x)) *
        (spinVal (α y) - spinVal (γ y)))
      nlinarith
    · simp [hybrid, hx, hy] <;> ring_nf <;> exact le_refl _
  · simp [he]

/-- The logarithmic interaction loss only charges edges crossing the cut.
`cutEdges` counts both orientations, so this is `4 β` per undirected edge. -/
theorem interaction_cancellation_bound (Λ : Lattice V) (β : ℝ) (hβ : 0 ≤ β)
    (D : Finset V) (α γ : Config V) :
    Lattice.interaction Λ β univ α + Lattice.interaction Λ β univ γ -
      Lattice.interaction Λ β univ (hybrid D α γ) -
      Lattice.interaction Λ β univ (hybrid D γ α) ≤
      2 * β * (cutEdges Λ D).card := by
  have hsum : (∑ x : V, ∑ y : V,
      ((if Λ.adj x y then spinVal (α x) * spinVal (α y) else 0) +
        (if Λ.adj x y then spinVal (γ x) * spinVal (γ y) else 0) -
        (if Λ.adj x y then spinVal (hybrid D α γ x) *
          spinVal (hybrid D α γ y) else 0) -
        (if Λ.adj x y then spinVal (hybrid D γ α x) *
          spinVal (hybrid D γ α y) else 0))) ≤
      ∑ x : V, ∑ y : V,
        if Λ.adj x y ∧ ¬ (x ∈ D ↔ y ∈ D) then (4:ℝ) else 0 :=
    sum_le_sum fun x _ => sum_le_sum fun y _ => interaction_term_le Λ D α γ x y
  have hcard : (∑ x : V, ∑ y : V,
      if Λ.adj x y ∧ ¬ (x ∈ D ↔ y ∈ D) then (4:ℝ) else 0) =
      4 * (cutEdges Λ D).card := by
    have hh := Fintype.sum_prod_type (fun e : V × V =>
      if Λ.adj e.1 e.2 ∧ ¬ (e.1 ∈ D ↔ e.2 ∈ D) then (4:ℝ) else 0)
    rw [← hh]
    change (∑ e : V × V, if Λ.adj e.1 e.2 ∧ ¬ (e.1 ∈ D ↔ e.2 ∈ D) then (4:ℝ) else 0) = _
    rw [← sum_filter]
    simp [cutEdges, mul_comm]
  rw [hcard] at hsum
  have hmul := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ β / 2)
  simp only [Lattice.interaction, mem_univ, sum_add_distrib, sum_sub_distrib] at *
  nlinarith [hmul]

/-- Field- and boundary-uniform Gibbs product comparison at any cut. -/
theorem gibbs_product_le (Λ : Lattice V) (h : V → ℝ) (β : ℝ)
    (hβ : 0 ≤ β) (S D : Finset V) (φ α γ : Config V) :
    (gibbs Λ h β univ S φ).w α * (gibbs Λ h β univ S φ).w γ ≤
      exp (2 * β * (cutEdges Λ D).card) *
        ((gibbs Λ h β univ S φ).w (hybrid D α γ) *
          (gibbs Λ h β univ S φ).w (hybrid D γ α)) := by
  have hi := interaction_cancellation_bound Λ β hβ D α γ
  have hf := field_cancellation h univ D α γ
  have hb := boundary_cancellation Λ β univ S D φ α γ
  have he :
      (Lattice.interaction Λ β univ α + Lattice.fieldEnergy h univ α +
        Lattice.boundEnergy Λ β univ S φ α) +
      (Lattice.interaction Λ β univ γ + Lattice.fieldEnergy h univ γ +
        Lattice.boundEnergy Λ β univ S φ γ) ≤
      2 * β * (cutEdges Λ D).card +
      ((Lattice.interaction Λ β univ (hybrid D α γ) +
        Lattice.fieldEnergy h univ (hybrid D α γ) +
        Lattice.boundEnergy Λ β univ S φ (hybrid D α γ)) +
      (Lattice.interaction Λ β univ (hybrid D γ α) +
        Lattice.fieldEnergy h univ (hybrid D γ α) +
        Lattice.boundEnergy Λ β univ S φ (hybrid D γ α))) := by linarith
  have hexp := exp_le_exp.mpr he
  simp only [exp_add] at hexp
  unfold gibbs
  dsimp
  simp only [isingWeight]
  have hz := isingZ_pos Λ h β univ S φ
  convert mul_le_mul_of_nonneg_right hexp (inv_nonneg.mpr (le_of_lt (mul_pos hz hz))) using 1 <;>
    dsimp [isingWeight] <;> simp only [exp_add] <;> field_simp <;> ring

/-- Fixing one hybrid configuration makes the complementary encoding injective. -/
theorem companion_injective (D : Finset V) (z : Config V)
    (s : Finset (Config V × Config V))
    (hz : ∀ p ∈ s, hybrid D p.1 p.2 = z) :
    Set.InjOn (fun p : Config V × Config V => hybrid D p.2 p.1) s := by
  intro p hp q hq he
  have hez := (hz p hp).trans (hz q hq).symm
  apply Prod.ext
  · funext x
    have h1 := congrFun he x
    have h2 := congrFun hez x
    by_cases hx : x ∈ D
    · simpa [hybrid, hx] using h1
    · simpa [hybrid, hx] using h2
  · funext x
    have h1 := congrFun he x
    have h2 := congrFun hez x
    by_cases hx : x ∈ D
    · simpa [hybrid, hx] using h2
    · simpa [hybrid, hx] using h1

/-- Injectivity bounds the total Gibbs mass of complementary encodings by one. -/
theorem companion_mass_le_one (μ : FinProb (Config V)) (D : Finset V)
    (z : Config V) (s : Finset (Config V × Config V))
    (hz : ∀ p ∈ s, hybrid D p.1 p.2 = z) :
    ∑ p ∈ s, μ.w (hybrid D p.2 p.1) ≤ 1 := by
  rw [← sum_image (companion_injective D z s hz)]
  calc ∑ ξ ∈ s.image (fun p => hybrid D p.2 p.1), μ.w ξ ≤ ∑ ξ, μ.w ξ :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun ξ _ _ => μ.nonneg ξ)
    _ = 1 := μ.sum_one

/-- Sum of all path-pair weights using a fixed edge is bounded by its
heat-bath conductance. The only assumptions on the cuts are geometric. -/
theorem edge_congestion (Λ : Lattice V) (h : V → ℝ) (β : ℝ)
    (hβ : 0 ≤ β) (S D D' : Finset V) (φ z z' : Config V)
    (W : ℝ) (hD : ((cutEdges Λ D).card : ℝ) ≤ W)
    (hD' : ((cutEdges Λ D').card : ℝ) ≤ W)
    (s : Finset (Config V × Config V))
    (hz : ∀ p ∈ s, hybrid D p.1 p.2 = z)
    (hz' : ∀ p ∈ s, hybrid D' p.1 p.2 = z') :
    ∑ p ∈ s, (gibbs Λ h β univ S φ).w p.1 *
        (gibbs Λ h β univ S φ).w p.2 ≤
      2 * exp (2 * β * W) * conductance (gibbs Λ h β univ S φ) z z' := by
  let μ := gibbs Λ h β univ S φ
  let E := exp (2 * β * W)
  let M := ∑ p ∈ s, μ.w p.1 * μ.w p.2
  have hbnd (C : Finset V) (v : Config V)
      (hC : ((cutEdges Λ C).card : ℝ) ≤ W)
      (hv : ∀ p ∈ s, hybrid C p.1 p.2 = v) : M ≤ E * μ.w v := by
    have he : exp (2 * β * (cutEdges Λ C).card) ≤ E :=
      exp_le_exp.mpr (mul_le_mul_of_nonneg_left hC (by positivity))
    calc M ≤ ∑ p ∈ s, E * (μ.w v * μ.w (hybrid C p.2 p.1)) := by
          apply sum_le_sum
          intro p hp
          have hc := gibbs_product_le Λ h β hβ S C φ p.1 p.2
          rw [hv p hp] at hc
          exact hc.trans (mul_le_mul_of_nonneg_right he
            (mul_nonneg (μ.nonneg v) (μ.nonneg _)))
      _ = (E * μ.w v) * ∑ p ∈ s, μ.w (hybrid C p.2 p.1) := by
          simp only [mul_sum]; apply sum_congr rfl; intro p hp; ring
      _ ≤ (E * μ.w v) * 1 :=
          mul_le_mul_of_nonneg_left (companion_mass_le_one μ C v s hv)
            (mul_nonneg (exp_nonneg _) (μ.nonneg v))
      _ = E * μ.w v := mul_one _
  have h1 := hbnd D z hD hz
  have h2 := hbnd D' z' hD' hz'
  have hzp : 0 < μ.w z := div_pos (isingWeight_pos _ _ _ _ _ _ _) (isingZ_pos _ _ _ _ _ _)
  have hz'p : 0 < μ.w z' := div_pos (isingWeight_pos _ _ _ _ _ _ _) (isingZ_pos _ _ _ _ _ _)
  have hsum : 0 < μ.w z + μ.w z' := add_pos hzp hz'p
  change M ≤ 2 * E * (μ.w z * μ.w z' / (μ.w z + μ.w z'))
  rw [← mul_div_assoc, le_div_iff₀ hsum]
  nlinarith [mul_le_mul_of_nonneg_right h1 (le_of_lt hz'p),
    mul_le_mul_of_nonneg_right h2 (le_of_lt hzp)]

/-- The initial segment before coordinate `k` in a chosen ordering. -/
def initialSegment {q : ℕ} (order : Fin q ≃ V) (k : ℕ) : Finset V :=
  univ.filter fun x => (order.symm x).val < k

@[simp] theorem initialSegment_zero {q : ℕ} (order : Fin q ≃ V) : initialSegment order 0 = ∅ := by
  simp [initialSegment]

@[simp] theorem initialSegment_end {q : ℕ} (order : Fin q ≃ V) : initialSegment order q = univ := by
  ext x
  simp [initialSegment, (order.symm x).isLt]

@[simp] theorem hybrid_empty (α γ : Config V) : hybrid ∅ α γ = α := by
  funext x; simp [hybrid]

@[simp] theorem hybrid_univ (α γ : Config V) : hybrid univ α γ = γ := by
  funext x; simp [hybrid]

/-- An oriented edge updating the indicated coordinate only. -/
def siteEdge (x : V) (z z' : Config V) : Prop :=
  z x ≠ z' x ∧ ∀ y, y ≠ x → z y = z' y

/-- A nonconstant step of the ordered path really is a one-site edge. -/
theorem path_step_siteEdge {q : ℕ} (order : Fin q ≃ V)
    (k : Fin q) (α γ : Config V)
    (hne : hybrid (initialSegment order k.val) α γ ≠
      hybrid (initialSegment order (k.val + 1)) α γ) :
    siteEdge (order k) (hybrid (initialSegment order k.val) α γ)
      (hybrid (initialSegment order (k.val + 1)) α γ) := by
  have hrest : ∀ y, y ≠ order k →
      hybrid (initialSegment order k.val) α γ y =
        hybrid (initialSegment order (k.val + 1)) α γ y := by
    intro y hy
    have hk : order.symm y ≠ k := by
      intro hh
      exact hy (by simpa using congrArg order hh)
    have hkval : (order.symm y).val ≠ k.val := fun hh => hk (Fin.ext hh)
    simp only [hybrid, initialSegment, mem_filter, mem_univ, true_and]
    have he : (order.symm y).val < k.val ↔ (order.symm y).val < k.val + 1 := by omega
    simp only [he]
  refine ⟨?_, hrest⟩
  intro heq
  apply hne
  funext y
  by_cases hy : y = order k
  · simpa [hy] using heq
  · exact hrest y hy

/-- Distinct updating coordinates cannot describe the same nonconstant edge. -/
theorem siteEdge_unique {x y : V} {z z' : Config V}
    (hx : siteEdge x z z') (hy : siteEdge y z z') : x = y := by
  by_contra hxy
  exact hx.1 (hy.2 x hxy)

/-- Telescoping and Cauchy-Schwarz along the actual ordered configuration path. -/
theorem telescope_bound {q : ℕ} (order : Fin q ≃ V) (α γ : Config V)
    (f : Config V → ℝ) :
    (f α - f γ)^2 ≤ (q : ℝ) * ∑ k : Fin q,
      (f (hybrid (initialSegment order k.val) α γ) -
        f (hybrid (initialSegment order (k.val + 1)) α γ))^2 := by
  let a := fun k : ℕ => f (hybrid (initialSegment order k) α γ)
  have htel : (∑ k ∈ range q, (a k - a (k+1))) = f α - f γ := by
    have ht := sum_range_sub a q
    simp only [a, initialSegment_end, initialSegment_zero, hybrid_univ, hybrid_empty, sum_sub_distrib] at *
    linarith
  have hc := sq_sum_le_card_mul_sum_sq (s := range q) (f := fun k => a k - a (k+1))
  rw [htel, card_range] at hc
  rw [← Fin.sum_univ_eq_sum_range (fun k => (a k - a (k+1))^2) q] at hc
  exact hc

/-- The exact pairwise representation of variance used in the path argument. -/
theorem variance_pairwise {A : Type*} [Fintype A] (μ : FinProb A) (f : A → ℝ) :
    FinProb.variance μ f = (1/2) * ∑ a : A, ∑ b : A,
      μ.w a * μ.w b * (f a - f b)^2 := by
  let m := μ.expect f
  let T := ∑ a, μ.w a * (f a)^2
  have hv : FinProb.variance μ f = T - m^2 := by
    unfold FinProb.variance FinProb.expect
    calc (∑ a, μ.w a * ((f a - m) * (f a - m))) =
        ∑ a, (μ.w a * (f a)^2 - (2*m) * (μ.w a * f a) + m^2 * μ.w a) := by
          apply sum_congr rfl; intro a ha; ring
      _ = T - m^2 := by
          simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, μ.sum_one, mul_one]
          change T - (2*m)*m + m^2 = T - m^2
          ring
  have hp : (∑ a : A, ∑ b : A, μ.w a * μ.w b * (f a - f b)^2) = 2*(T-m^2) := by
    calc (∑ a : A, ∑ b : A, μ.w a * μ.w b * (f a - f b)^2) =
        ∑ a : A, ∑ b : A, ((μ.w a * (f a)^2) * μ.w b -
          (2 * (μ.w a * f a)) * (μ.w b * f b) + μ.w a * (μ.w b * (f b)^2)) := by
            apply sum_congr rfl; intro a ha
            apply sum_congr rfl; intro b hb; ring
      _ = 2*(T-m^2) := by
          simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, μ.sum_one, mul_one]
          change T - (∑ a, 2 * (μ.w a * f a) * m) + (∑ a, μ.w a * T) = _
          have hm : (∑ a, 2 * (μ.w a * f a) * m) = (2*m)*m := by
            calc (∑ a, 2 * (μ.w a * f a) * m) =
                (2*m)*(∑ a, μ.w a * f a) := by
                  rw [mul_sum]
                  apply sum_congr rfl; intro a ha; ring
              _ = (2*m)*m := rfl
          rw [hm, ← sum_mul, μ.sum_one]
          ring
  rw [hv, hp]; ring

private theorem sum_fibers {A B : Type*} [Fintype A] [Fintype B]
    (g : A → B) (w : A → ℝ) (F : B → ℝ) :
    (∑ b, (∑ a ∈ univ.filter (fun a => g a = b), w a) * F b) =
      ∑ a, w a * F (g a) := by
  simp only [sum_filter, sum_mul, ite_mul, zero_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro a ha
  simp

/-- An ordered edge belongs to precisely one site-update graph. -/
theorem sum_site_edges {q : ℕ} (order : Fin q ≃ V) (z z' : Config V) (c : ℝ) :
    (∑ k : Fin q, if siteEdge (order k) z z' then c else 0) =
      if ∃ x, siteEdge x z z' then c else 0 := by
  by_cases he : ∃ x, siteEdge x z z'
  · obtain ⟨x, hx⟩ := he
    rw [if_pos ⟨x, hx⟩]
    rw [sum_eq_single (order.symm x)]
    · simp only [Equiv.apply_symm_apply, if_pos hx]
    · intro k hk hne
      rw [if_neg]
      intro hh
      apply hne
      apply order.injective
      simpa using siteEdge_unique hh hx
    · simp
  · rw [if_neg he]
    apply sum_eq_zero
    intro k hk
    exact if_neg (fun hh => he ⟨order k, hh⟩)

/-- The congestion bound after reindexing the pairs by their actual path edge. -/
theorem path_step_sum_le (Λ : Lattice V) (h : V → ℝ) (β : ℝ)
    (hβ : 0 ≤ β) (S : Finset V) (φ : Config V)
    {q : ℕ} (order : Fin q ≃ V) (k : Fin q) (W : ℝ)
    (hwidth : ∀ j ≤ q, ((cutEdges Λ (initialSegment order j)).card : ℝ) ≤ W)
    (f : Config V → ℝ) :
    (∑ p : Config V × Config V,
      (gibbs Λ h β univ S φ).w p.1 * (gibbs Λ h β univ S φ).w p.2 *
        (f (hybrid (initialSegment order k.val) p.1 p.2) -
          f (hybrid (initialSegment order (k.val+1)) p.1 p.2))^2) ≤
      2 * exp (2*β*W) * ∑ e : Config V × Config V,
        if siteEdge (order k) e.1 e.2 then
          conductance (gibbs Λ h β univ S φ) e.1 e.2 * (f e.1-f e.2)^2 else 0 := by
  classical
  let μ := gibbs Λ h β univ S φ
  let g : (Config V × Config V) → (Config V × Config V) :=
    fun p => (hybrid (initialSegment order k.val) p.1 p.2,
      hybrid (initialSegment order (k.val+1)) p.1 p.2)
  let w := fun p : Config V × Config V => μ.w p.1 * μ.w p.2
  let F := fun e : Config V × Config V => (f e.1 - f e.2)^2
  change (∑ p, w p * F (g p)) ≤ _
  rw [← sum_fibers g w F, mul_sum]
  apply sum_le_sum
  intro e he
  by_cases hs : siteEdge (order k) e.1 e.2
  · rw [if_pos hs]
    have hc := edge_congestion Λ h β hβ S (initialSegment order k.val)
      (initialSegment order (k.val+1)) φ e.1 e.2 W
      (hwidth k.val (Nat.le_of_lt k.isLt)) (hwidth (k.val+1) k.isLt)
      (univ.filter (fun p => g p = e))
      (fun p hp => congrArg Prod.fst (mem_filter.mp hp).2)
      (fun p hp => congrArg Prod.snd (mem_filter.mp hp).2)
    have hh := mul_le_mul_of_nonneg_right hc (sq_nonneg (f e.1-f e.2))
    convert hh using 1 <;> simp only [w, F, μ, mul_assoc]
    congr 2
    ext a
    simp
  · rw [if_neg hs, mul_zero]
    by_cases hself : e.1 = e.2
    · simp [F, hself]
    · have hempty : (univ.filter (fun p => g p = e)) = ∅ := by
        apply eq_empty_iff_forall_not_mem.mpr
        intro p hp
        have hg := (mem_filter.mp hp).2
        have hnepath : (g p).1 ≠ (g p).2 := by simpa only [hg] using hself
        have hh : siteEdge (order k) (g p).1 (g p).2 :=
          path_step_siteEdge order k p.1 p.2 hnepath
        rw [hg] at hh
        exact hs hh
      have hh : (∑ p ∈ univ.filter (fun p => g p = e), w p) = 0 := by rw [hempty, sum_empty]
      convert (by rw [hh, zero_mul] : (∑ p ∈ univ.filter (fun p => g p = e), w p) * F e ≤ 0) using 1
      congr 2
      ext a
      simp

/-- Appendix A.2: actual canonical paths give the field-uniform Poincaré
inequality for rate-one single-site heat-bath dynamics. The bound `W` counts
both directed orientations of every crossing interaction. -/
theorem poincare (Λ : Lattice V) (h : V → ℝ) (β : ℝ)
    (hβ : 0 ≤ β) (S : Finset V) (φ : Config V)
    {q : ℕ} (order : Fin q ≃ V) (W : ℝ)
    (hwidth : ∀ j ≤ q, ((cutEdges Λ (initialSegment order j)).card : ℝ) ≤ W)
    (f : Config V → ℝ) :
    FinProb.variance (gibbs Λ h β univ S φ) f ≤
      2 * (q : ℝ) * exp (2*β*W) * dirichletForm (gibbs Λ h β univ S φ) f := by
  classical
  let μ := gibbs Λ h β univ S φ
  let w := fun p : Config V × Config V => μ.w p.1 * μ.w p.2
  let F := fun k : Fin q => fun p : Config V × Config V =>
    (f (hybrid (initialSegment order k.val) p.1 p.2) -
      f (hybrid (initialSegment order (k.val+1)) p.1 p.2))^2
  let E := exp (2*β*W)
  have hv : FinProb.variance μ f = (1/2) * ∑ p : Config V × Config V,
      w p * (f p.1-f p.2)^2 := by
    rw [variance_pairwise]
    congr 1
    exact (Fintype.sum_prod_type (fun p : Config V × Config V => w p * (f p.1-f p.2)^2)).symm
  have htel : (∑ p : Config V × Config V, w p * (f p.1-f p.2)^2) ≤
      (q : ℝ) * ∑ k : Fin q, ∑ p : Config V × Config V, w p * F k p := by
    calc (∑ p : Config V × Config V, w p * (f p.1-f p.2)^2) ≤
        ∑ p : Config V × Config V, w p * ((q : ℝ) * ∑ k : Fin q, F k p) := by
          apply sum_le_sum
          intro p hp
          exact mul_le_mul_of_nonneg_left (telescope_bound order p.1 p.2 f)
            (mul_nonneg (μ.nonneg p.1) (μ.nonneg p.2))
      _ = (q : ℝ) * ∑ k : Fin q, ∑ p : Config V × Config V, w p * F k p := by
          simp only [mul_sum]
          rw [sum_comm]
          apply sum_congr rfl; intro k hk
          apply sum_congr rfl; intro p hp; ring
  have hsteps : (∑ k : Fin q, ∑ p : Config V × Config V, w p * F k p) ≤
      2*E * (heatBathGraph V).dirichlet μ f := by
    calc (∑ k : Fin q, ∑ p : Config V × Config V, w p * F k p) ≤
        ∑ k : Fin q, 2*E * ∑ e : Config V × Config V,
          if siteEdge (order k) e.1 e.2 then conductance μ e.1 e.2 * (f e.1-f e.2)^2 else 0 := by
            apply sum_le_sum
            intro k hk
            exact path_step_sum_le Λ h β hβ S φ order k W hwidth f
      _ = 2*E * ∑ e : Config V × Config V,
          if ∃ x, siteEdge x e.1 e.2 then conductance μ e.1 e.2 * (f e.1-f e.2)^2 else 0 := by
            rw [← mul_sum]
            congr 1
            rw [sum_comm]
            apply sum_congr rfl; intro e he
            exact sum_site_edges order e.1 e.2 _
      _ = 2*E * (heatBathGraph V).dirichlet μ f := by
            congr 1
            rw [UpdateGraph.dirichlet]
            convert Fintype.sum_prod_type (fun e : Config V × Config V =>
              if ∃ x, siteEdge x e.1 e.2 then conductance μ e.1 e.2 * (f e.1-f e.2)^2 else 0) using 1
            apply sum_congr rfl; intro a ha
            apply sum_congr rfl; intro b hb
            congr 1
  have hh := mul_le_mul_of_nonneg_left hsteps (Nat.cast_nonneg q : (0:ℝ) ≤ q)
  have ht := mul_le_mul_of_nonneg_left (htel.trans hh) (by norm_num : (0:ℝ) ≤ 1/2)
  rw [hv]
  change _ ≤ 2 * (q : ℝ) * E * ((1/2) * (heatBathGraph V).dirichlet μ f)
  nlinarith [ht]

/-- A nonempty finite Ising system has a statistic of strictly positive
variance, so the Rayleigh infimum is over a nonempty set. -/
theorem gibbs_rayleigh_nonempty (Λ : Lattice V) (h : V → ℝ) (β : ℝ)
    (S : Finset V) (φ : Config V) (x : V) :
    (rayleighValues (gibbs Λ h β univ S φ)).Nonempty := by
  let μ := gibbs Λ h β univ S φ
  let f := fun η : Config V => spinVal (η x)
  have hμ (η : Config V) : 0 < μ.w η :=
    div_pos (isingWeight_pos _ _ _ _ _ _ _) (isingZ_pos _ _ _ _ _ _)
  have hs : 0 < ∑ a : Config V, ∑ b : Config V,
      μ.w a * μ.w b * (f a-f b)^2 := by
    apply sum_pos' (fun a ha => sum_nonneg fun b hb =>
      mul_nonneg (mul_nonneg (μ.nonneg a) (μ.nonneg b)) (sq_nonneg _))
    refine ⟨(fun _ => 0), mem_univ _, ?_⟩
    apply sum_pos' (fun b hb =>
      mul_nonneg (mul_nonneg (μ.nonneg _) (μ.nonneg b)) (sq_nonneg _))
    refine ⟨(fun _ => 1), mem_univ _, ?_⟩
    dsimp only [f]
    rw [spinVal_zero, spinVal_one]
    exact mul_pos (mul_pos (hμ _) (hμ _)) (by norm_num)
  have hv : 0 < FinProb.variance μ f := by
    rw [variance_pairwise]
    exact mul_pos (by norm_num) hs
  exact ⟨dirichletForm μ f / FinProb.variance μ f, f, hv, rfl⟩

/-- Appendix A.2's field-uniform local gap estimate in terms of a proved
ordering cut bound. With `W = 2w`, the denominator is `2q exp(4βw)`. -/
theorem gap_lower_bound (Λ : Lattice V) (h : V → ℝ) (β : ℝ)
    (hβ : 0 ≤ β) (S : Finset V) (φ : Config V)
    {q : ℕ} (hq : 0 < q) (order : Fin q ≃ V) (W : ℝ)
    (hwidth : ∀ j ≤ q, ((cutEdges Λ (initialSegment order j)).card : ℝ) ≤ W) :
    1 / (2 * (q : ℝ) * exp (2*β*W)) ≤ spectralGap (gibbs Λ h β univ S φ) := by
  have hA : 0 < 2 * (q : ℝ) * exp (2*β*W) := by positivity
  apply le_spectralGap _ (gibbs_rayleigh_nonempty Λ h β S φ (order ⟨0, hq⟩))
  intro f
  rw [one_div_mul_eq_div, div_le_iff₀ hA]
  have hp := poincare Λ h β hβ S φ order W hwidth f
  simpa only [mul_comm] using hp

end CanonicalPath
end Paper09
