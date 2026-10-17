import Paper06.Incidence
import Paper06.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset

open Real Set BigOperators
open scoped Classical

namespace Paper06

noncomputable def incidenceNeighbours {F : Type*} [Fintype F] [Field F]
    (f g : F → F) (x : F) : Finset F :=
  Finset.univ.filter fun y => f x + g y = x * y

/-- Distinct graph points determine at most one slope, over any field. -/
theorem incidence_unique_slope {F : Type*} [Field F] (f g : F → F)
    {x x' y z : F} (hyz : y ≠ z)
    (hxy : f x + g y = x * y) (hxz : f x + g z = x * z)
    (hx'y : f x' + g y = x' * y) (hx'z : f x' + g z = x' * z) : x = x' := by
  have h : (x - x') * (y - z) = 0 := by linear_combination -hxy + hxz + hx'y - hx'z
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hyz))

/-- Ordered pairs of distinct neighbours occur for at most one slope. -/
theorem incidence_pair_count {F : Type*} [Fintype F] [Field F] (f g : F → F) :
    ∑ x : F, (incidenceNeighbours f g x).offDiag.card ≤
      (Fintype.card F) * (Fintype.card F) - Fintype.card F := by
  classical
  let S := Finset.univ.sigma fun x : F => (incidenceNeighbours f g x).offDiag
  have hcard : S.card ≤ (Finset.univ : Finset F).offDiag.card := by
    apply Finset.card_le_card_of_injOn (fun p : (x : F) × (F × F) => p.2)
    · intro p hp
      have hp' := (Finset.mem_sigma.mp hp).2
      exact Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _,
        (Finset.mem_offDiag.mp hp').2.2⟩
    · intro p hp p' hp' he
      obtain ⟨x, y, z⟩ := p
      obtain ⟨x', y', z'⟩ := p'
      have he' : (y, z) = (y', z') := he
      cases he'
      have hp1 := Finset.mem_offDiag.mp ((Finset.mem_sigma.mp hp).2)
      have hp2 := Finset.mem_offDiag.mp ((Finset.mem_sigma.mp hp').2)
      have hx : x = x' := incidence_unique_slope f g hp1.2.2
        (Finset.mem_filter.mp hp1.1).2 (Finset.mem_filter.mp hp1.2.1).2
        (Finset.mem_filter.mp hp2.1).2 (Finset.mem_filter.mp hp2.2.1).2
      subst x'
      rfl
  simpa [S, Finset.card_sigma, Finset.offDiag_card] using hcard

/-- The paper's ordered-pair bound in its literal `t_x(t_x-1)` form. -/
theorem incidence_pair_count_mul {F : Type*} [Fintype F] [Field F] (f g : F → F) :
    (∑ x : F, (incidenceNeighbours f g x).card * ((incidenceNeighbours f g x).card - 1)) ≤
      Fintype.card F * (Fintype.card F - 1) := by
  simpa only [Finset.offDiag_card, Nat.mul_sub_left_distrib, Nat.mul_one] using
    incidence_pair_count f g

/-- Incidences are the sum of the sizes of their slope fibres. -/
theorem Ifg_eq_sum_neighbours {F : Type*} [Fintype F] [Field F] (f g : F → F) :
    Ifg f g = ∑ x : F, (incidenceNeighbours f g x).card := by
  classical
  simp only [Ifg, gameWin, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  simp only [incidenceNeighbours, Finset.sum_filter]

/-- The incidence quadratic follows from the actual finite-field pair count. -/
theorem incidence_quadratic {F : Type*} [Fintype F] [Field F] (f g : F → F) :
    (Ifg f g : ℝ) * Ifg f g ≤ (Fintype.card F : ℝ) * Ifg f g +
      (Fintype.card F : ℝ) * Fintype.card F * ((Fintype.card F : ℝ) - 1) := by
  classical
  let t : F → ℕ := fun x => (incidenceNeighbours f g x).card
  have hsum : (Ifg f g : ℝ) = ∑ x : F, (t x : ℝ) := by
    exact_mod_cast Ifg_eq_sum_neighbours f g
  have hc : ∀ s : Finset F, (s.card : ℝ) ^ 2 = s.card + (s.offDiag.card : ℝ) := by
    intro s
    have h : s.card + s.offDiag.card = s.card * s.card := by
      rw [Finset.offDiag_card]
      have : s.card ≤ s.card * s.card := by nlinarith
      omega
    have hR : (s.card : ℝ) * s.card = s.card + (s.offDiag.card : ℝ) := by exact_mod_cast h.symm
    simpa only [pow_two] using hR
  have hcard : 1 ≤ Fintype.card F := Fintype.card_pos_iff.mpr inferInstance
  have hn : ((Fintype.card F * Fintype.card F - Fintype.card F : ℕ) : ℝ)
      = (Fintype.card F : ℝ) * Fintype.card F - Fintype.card F := by
    rw [Nat.cast_sub (by nlinarith : Fintype.card F ≤ Fintype.card F * Fintype.card F)]
    simp
  have hpair : (∑ x : F, ((incidenceNeighbours f g x).offDiag.card : ℝ)) ≤
      (Fintype.card F : ℝ) * Fintype.card F - Fintype.card F := by
    rw [← hn]
    exact_mod_cast incidence_pair_count f g
  have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset F))
    (f := fun x => (t x : ℝ))
  have hsq : (∑ x : F, (t x : ℝ) ^ 2) = (Ifg f g : ℝ) +
      ∑ x : F, ((incidenceNeighbours f g x).offDiag.card : ℝ) := by
    simp only [t, hc, Finset.sum_add_distrib, ← hsum]
  simp only [Finset.card_univ] at hcs
  rw [← hsum, hsq] at hcs
  have hn0 : (0 : ℝ) ≤ Fintype.card F := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left hpair hn0
  nlinarith

/-- Actual deterministic game bound, with no incidence estimate assumed. -/
theorem deterministic_win_le_beta {F : Type*} [Fintype F] [Field F] (f g : F → F) :
    (Ifg f g : ℝ) / (Fintype.card F * Fintype.card F) ≤ betaR (Fintype.card F) :=
  quadratic_root_bound_beta _ _ (Fintype.card_pos_iff.mpr inferInstance)
    (incidence_quadratic f g)

/-- The classical value: the maximum number of winning pairs divided by `|F|²`. -/
noncomputable def omegaR (F : Type*) [Fintype F] [Field F] : ℝ :=
  ((Finset.univ : Finset ((F → F) × (F → F))).sup (fun p => Ifg p.1 p.2) : ℕ) /
    ((Fintype.card F : ℝ) * Fintype.card F)

theorem omegaR_nonneg {F : Type*} [Fintype F] [Field F] : 0 ≤ omegaR F := by
  unfold omegaR
  positivity

theorem deterministic_win_le_omega {F : Type*} [Fintype F] [Field F] (f g : F → F) :
    (Ifg f g : ℝ) / ((Fintype.card F : ℝ) * Fintype.card F) ≤ omegaR F := by
  classical
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast (Finset.le_sup (s := (Finset.univ : Finset ((F → F) × (F → F))))
    (f := fun p => Ifg p.1 p.2) (Finset.mem_univ (f, g)))

/-- The classical value is positive: constant-zero strategies win at `(0,0)`. -/
theorem omegaR_pos {F : Type*} [Fintype F] [Field F] : 0 < omegaR F := by
  classical
  have hmem : ((0 : F), (0 : F)) ∈ gameWin (fun _ : F => 0) (fun _ : F => 0) := by
    simp [gameWin]
  have hI : 0 < Ifg (fun _ : F => 0) (fun _ : F => 0) :=
    Finset.card_pos.mpr ⟨((0 : F), (0 : F)), hmem⟩
  have hn : (0 : ℝ) < Fintype.card F := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card F)
  have hscore : 0 < (Ifg (fun _ : F => 0) (fun _ : F => 0) : ℝ) /
      ((Fintype.card F : ℝ) * Fintype.card F) :=
    div_pos (by exact_mod_cast hI) (mul_pos hn hn)
  exact hscore.trans_le (deterministic_win_le_omega _ _)

theorem omegaR_le_beta {F : Type*} [Fintype F] [Field F] :
    omegaR F ≤ betaR (Fintype.card F) := by
  classical
  obtain ⟨p, hp, he⟩ := Finset.exists_mem_eq_sup
    (Finset.univ : Finset ((F → F) × (F → F)))
    ⟨(fun _ => 0, fun _ => 0), Finset.mem_univ _⟩ (fun p => Ifg p.1 p.2)
  unfold omegaR
  rw [he]
  exact deterministic_win_le_beta p.1 p.2

/-- Product distribution on complete deterministic response functions. -/
noncomputable def channelLambda {X A : Type*} [Fintype X] [Fintype A]
    (s : X → FinProb A) (f : X → A) : ℝ := ∏ x, (s x).w (f x)

theorem channelLambda_nonneg {X A : Type*} [Fintype X] [Fintype A]
    (s : X → FinProb A) (f : X → A) : 0 ≤ channelLambda s f :=
  Finset.prod_nonneg fun _ _ => (s _).nonneg _

theorem channelLambda_sum {X A : Type*} [Fintype X] [DecidableEq X] [Fintype A]
    (s : X → FinProb A) : ∑ f : X → A, channelLambda s f = 1 := by
  classical
  unfold channelLambda
  rw [← Fintype.prod_sum]
  simp only [FinProb.sum_eq_one, Finset.prod_const_one]

/-- Each coordinate of the random response function has the original channel law. -/
theorem channelLambda_expect {X A : Type*} [Fintype X] [DecidableEq X] [Fintype A]
    (s : X → FinProb A) (x : X) (h : A → ℝ) :
    ∑ f : X → A, channelLambda s f * h (f x) = ∑ a, (s x).w a * h a := by
  classical
  have hprod (f : X → A) :
      channelLambda s f * h (f x) =
      ∏ i, ((s i).w (f i) * if i = x then h (f i) else 1) := by
    rw [Finset.prod_mul_distrib]
    congr 1
    symm
    exact Fintype.prod_ite_eq' x (fun i => h (f i))
  simp_rw [hprod]
  rw [← Fintype.prod_sum (fun (i : X) (a : A) =>
    (s i).w a * if i = x then h a else 1)]
  rw [Finset.prod_eq_single x]
  · simp
  · intro i hi hix
    simp only [hix, ↓reduceIte, mul_one]
    exact (s i).sum_eq_one
  · simp

/-- Explicit mixture identity for a stochastic channel, as in the paper. -/
theorem channelLambda_marginal {X A : Type*} [Fintype X] [DecidableEq X] [Fintype A]
    (s : X → FinProb A) (x : X) (a : A) :
    ∑ f : X → A, channelLambda s f * (if f x = a then 1 else 0) = (s x).w a := by
  classical
  rw [channelLambda_expect s x (fun b => if b = a then 1 else 0)]
  simp

/-- Average winning probability of two channels with independent uniform inputs. -/
noncomputable def channelWin {F : Type*} [Fintype F] [Field F]
    (s t : F → FinProb F) : ℝ :=
  (∑ x : F, ∑ y : F, ∑ a : F, ∑ b : F,
    (s x).w a * (t y).w b * (if a + b = x * y then 1 else 0)) /
      ((Fintype.card F : ℝ) * Fintype.card F)

/-- Deterministic winning probabilities are exactly incidence counts. -/
theorem Ifg_eq_win_sum {F : Type*} [Fintype F] [Field F] (f g : F → F) :
    (Ifg f g : ℝ) = ∑ x : F, ∑ y : F, (if f x + g y = x * y then 1 else 0) := by
  classical
  unfold Ifg gameWin
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  simp only [Finset.sum_filter, Nat.cast_one]
  exact Fintype.sum_prod_type _

/-- Randomisation is an explicit mixture of deterministic pairs of strategies. -/
theorem channelWin_eq_mixture {F : Type*} [Fintype F] [Field F]
    (s t : F → FinProb F) :
    channelWin s t = ∑ f : F → F, ∑ g : F → F,
      channelLambda s f * channelLambda t g *
        ((Ifg f g : ℝ) / ((Fintype.card F : ℝ) * Fintype.card F)) := by
  classical
  unfold channelWin
  simp_rw [← mul_div_assoc, ← Finset.sum_div]
  congr 1
  simp_rw [Ifg_eq_win_sum, Finset.mul_sum]
  have hexchange : (∑ f : F → F, ∑ g : F → F, ∑ x : F, ∑ y : F,
      channelLambda s f * channelLambda t g *
        (if f x + g y = x * y then 1 else 0)) =
      ∑ x : F, ∑ y : F, ∑ f : F → F, ∑ g : F → F,
      channelLambda s f * channelLambda t g *
        (if f x + g y = x * y then 1 else 0) := by
    simpa only [Fintype.sum_prod_type] using
      (Finset.sum_comm (s := (Finset.univ : Finset ((F → F) × (F → F))))
        (t := (Finset.univ : Finset (F × F)))
        (f := fun p q => channelLambda s p.1 * channelLambda t p.2 *
          (if p.1 q.1 + p.2 q.2 = q.1 * q.2 then (1 : ℝ) else 0)))
  rw [hexchange]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  symm
  calc
    _ = ∑ f : F → F, channelLambda s f *
        (∑ b : F, (t y).w b * (if f x + b = x * y then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro f hf
      simp only [mul_assoc, ← Finset.mul_sum]
      rw [channelLambda_expect t y (fun b => if f x + b = x * y then 1 else 0)]
    _ = ∑ a : F, (s x).w a *
        (∑ b : F, (t y).w b * (if a + b = x * y then 1 else 0)) :=
      channelLambda_expect s x (fun a =>
        ∑ b : F, (t y).w b * (if a + b = x * y then 1 else 0))
    _ = _ := by simp only [Finset.mul_sum, mul_assoc]

/-- Every pair of stochastic channels wins with probability at most the classical value. -/
theorem channelWin_le_omega {F : Type*} [Fintype F] [Field F]
    (s t : F → FinProb F) : channelWin s t ≤ omegaR F := by
  classical
  rw [channelWin_eq_mixture]
  calc
    _ ≤ ∑ f : F → F, ∑ g : F → F,
        channelLambda s f * channelLambda t g * omegaR F := by
      apply Finset.sum_le_sum
      intro f hf
      apply Finset.sum_le_sum
      intro g hg
      exact mul_le_mul_of_nonneg_left (deterministic_win_le_omega f g)
        (mul_nonneg (channelLambda_nonneg s f) (channelLambda_nonneg t g))
    _ = omegaR F := by
      simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, channelLambda_sum]
      ring

/-- The affine feasibility constraint: the input coordinate is uniform. -/
def UniformInput {F : Type*} [Fintype F] (q : FinProb (F × F)) : Prop :=
  ∀ x : F, ∑ a : F, q.w (x, a) = 1 / (Fintype.card F : ℝ)

/-- The output channel recovered from a feasible law. -/
noncomputable def feasibleChannel {F : Type*} [Fintype F] [Field F]
    (q : FinProb (F × F)) (hq : UniformInput q) (x : F) : FinProb F where
  w a := (Fintype.card F : ℝ) * q.w (x, a)
  nonneg a := mul_nonneg (Nat.cast_nonneg _) (q.nonneg _)
  sum_eq_one := by
    rw [← Finset.mul_sum, hq x]
    have hn : (Fintype.card F : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card F ≠ 0)
    field_simp

/-- Probability that two independent sites satisfy the finite-field game equation. -/
noncomputable def productWin {F : Type*} [Fintype F] [Field F]
    (q q' : FinProb (F × F)) : ℝ :=
  ∑ z : (F × F) × (F × F),
    if z.1.2 + z.2.2 = z.1.1 * z.2.1 then (prod q q').w z else 0

theorem productWin_expanded {F : Type*} [Fintype F] [Field F]
    (q q' : FinProb (F × F)) :
    productWin q q' = ∑ x : F, ∑ y : F, ∑ a : F, ∑ b : F,
      (if a + b = x * y then q.w (x, a) * q'.w (y, b) else 0) := by
  classical
  unfold productWin
  simp only [Fintype.sum_prod_type, prod_w]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_comm]

/-- Uniform-input independent laws are precisely the uniform-input channel experiment. -/
theorem productWin_eq_channelWin {F : Type*} [Fintype F] [Field F]
    (q q' : FinProb (F × F)) (hq : UniformInput q) (hq' : UniformInput q') :
    productWin q q' = channelWin (feasibleChannel q hq) (feasibleChannel q' hq') := by
  classical
  rw [productWin_expanded]
  unfold channelWin
  simp_rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have hn : (Fintype.card F : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card F ≠ 0)
  by_cases h : a + b = x * y
  · simp only [h, ↓reduceIte, feasibleChannel, mul_one]
    field_simp
  · simp [h]

/-- First inequality of Lemma 3.3, for every pair of feasible laws. -/
theorem feasible_product_win_le_omega {F : Type*} [Fintype F] [Field F]
    (q q' : FinProb (F × F)) (hq : UniformInput q) (hq' : UniformInput q') :
    productWin q q' ≤ omegaR F := by
  rw [productWin_eq_channelWin q q' hq hq']
  exact channelWin_le_omega _ _

/-- **Lemma 3.3** in full, for every finite field and arbitrary feasible independent laws. -/
theorem lemma_3_3_full {F : Type*} [Fintype F] [Field F]
    (q q' : FinProb (F × F)) (hq : UniformInput q) (hq' : UniformInput q') :
    productWin q q' ≤ omegaR F ∧
      omegaR F ≤ betaR (Fintype.card F) ∧
      betaR (Fintype.card F) ≤ 3 / (2 * Real.sqrt (Fintype.card F)) := by
  refine ⟨feasible_product_win_le_omega q q' hq hq', omegaR_le_beta, ?_⟩
  apply betaR_le
  exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty F))

end Paper06
