import Paper09.Ising
import Paper09.Defects
import Paper09.SoftShell
import Mathlib.Tactic

open Finset BigOperators Classical Real
noncomputable section
namespace Paper09

/-- The other value of an Ising spin. -/
def otherSpin (s : Spin) : Spin := Equiv.swap 0 1 s

@[simp] theorem otherSpin_otherSpin (s : Spin) : otherSpin (otherSpin s) = s := by
  simp [otherSpin]

@[simp] theorem otherSpin_ne (s : Spin) : otherSpin s ≠ s := by
  fin_cases s <;> norm_num [otherSpin]

@[simp] theorem spinVal_otherSpin (s : Spin) : spinVal (otherSpin s) = -spinVal s := by
  fin_cases s <;> norm_num [otherSpin]

/-- Flipping a single coordinate, as a genuine bijection of configuration space. -/
def spinFlip {V : Type*} [DecidableEq V] (x : V) (η : V → Spin) : V → Spin :=
  Function.update η x (otherSpin (η x))

@[simp] theorem spinFlip_self {V : Type*} [DecidableEq V] (x : V) (η : V → Spin) :
    spinFlip x η x = otherSpin (η x) := by simp [spinFlip]

@[simp] theorem spinFlip_of_ne {V : Type*} [DecidableEq V] {x y : V} (hy : y ≠ x)
    (η : V → Spin) : spinFlip x η y = η y := by simp [spinFlip, hy]

@[simp] theorem spinFlip_involutive {V : Type*} [DecidableEq V] (x : V)
    (η : V → Spin) : spinFlip x (spinFlip x η) = η := by
  funext y
  by_cases hy : y = x
  · subst y; simp
  · simp [hy]

def spinFlipEquiv {V : Type*} [DecidableEq V] (x : V) : (V → Spin) ≃ (V → Spin) where
  toFun := spinFlip x
  invFun := spinFlip x
  left_inv := spinFlip_involutive x
  right_inv := spinFlip_involutive x

/-- Real-valued defect indicator. -/
def defectIndicator {V : Type*} (ζ η : V → Spin) (x : V) : ℝ :=
  if η x ≠ ζ x then 1 else 0

@[simp] theorem defectIndicator_nonneg {V : Type*} (ζ η : V → Spin) (x : V) :
    0 ≤ defectIndicator ζ η x := by unfold defectIndicator; split_ifs <;> norm_num

@[simp] theorem defectIndicator_flip {V : Type*} [DecidableEq V]
    (ζ η : V → Spin) (x : V) :
    defectIndicator ζ (spinFlip x η) x = 1 - defectIndicator ζ η x := by
  unfold defectIndicator
  simp only [spinFlip_self]
  generalize η x = a
  generalize ζ x = b
  fin_cases a <;> fin_cases b <;> norm_num [otherSpin]

/-- A full single-site conditional bound, expressed without a division by a possible zero. -/
def defectConditionalBound {V : Type*} [Fintype V] (p : FinProb (V → Spin))
    (ζ : V → Spin) (x : V) (q : ℝ) : Prop :=
  ∀ η, η x ≠ ζ x → p.w η ≤ q * (p.w η + p.w (spinFlip x η))

/-- The full conditional bound also bounds the defect probability after multiplying
by any nonnegative statistic of the other coordinates. This is the averaging
step which retains dependencies in the shell law. -/
theorem weighted_defect_bound {V : Type*} [Fintype V]
    (p : FinProb (V → Spin)) (ζ : V → Spin) (x : V) (q : ℝ)
    (_hq : 0 ≤ q) (hlocal : defectConditionalBound p ζ x q)
    (g : (V → Spin) → ℝ) (hg : ∀ η, 0 ≤ g η)
    (hinv : ∀ η, g (spinFlip x η) = g η) :
    p.expect (fun η => defectIndicator ζ η x * g η) ≤ q * p.expect g := by
  have hpair : ∀ η,
      p.w η * defectIndicator ζ η x +
        p.w (spinFlip x η) * defectIndicator ζ (spinFlip x η) x
        ≤ q * (p.w η + p.w (spinFlip x η)) := by
    intro η
    by_cases hd : η x ≠ ζ x
    · have hD : defectIndicator ζ η x = 1 := by simp [defectIndicator, hd]
      rw [defectIndicator_flip, hD]
      simpa using hlocal η hd
    · have hd' : spinFlip x η x ≠ ζ x := by
        simp [not_ne_iff.mp hd]
      have h := hlocal (spinFlip x η) hd'
      have hD : defectIndicator ζ η x = 0 := by simp [defectIndicator, hd]
      rw [defectIndicator_flip, hD]
      simpa [add_comm] using h
  have hreindex (f : (V → Spin) → ℝ) : (∑ η, f (spinFlip x η)) = ∑ η, f η :=
    Equiv.sum_comp (spinFlipEquiv x) f
  have hh := Finset.sum_le_sum (s := (univ : Finset (V → Spin)))
    (fun η _ => mul_le_mul_of_nonneg_right (hpair η) (hg η))
  have hleft :
      (∑ η, (p.w η * defectIndicator ζ η x +
        p.w (spinFlip x η) * defectIndicator ζ (spinFlip x η) x) * g η)
      = 2 * p.expect (fun η => defectIndicator ζ η x * g η) := by
    simp only [add_mul, sum_add_distrib, FinProb.expect]
    have hflip : (∑ η, p.w (spinFlip x η) * defectIndicator ζ (spinFlip x η) x * g η)
        = ∑ η, p.w η * defectIndicator ζ η x * g η := by
      calc
        _ = ∑ η, p.w (spinFlip x η) * defectIndicator ζ (spinFlip x η) x *
              g (spinFlip x η) := by simp only [hinv]
        _ = _ := hreindex (fun η => p.w η * defectIndicator ζ η x * g η)
    rw [hflip]
    simp only [mul_assoc]
    ring
  have hright : (∑ η, (q * (p.w η + p.w (spinFlip x η))) * g η)
      = 2 * (q * p.expect g) := by
    simp only [mul_add, add_mul, sum_add_distrib, FinProb.expect]
    have hflip : (∑ η, q * p.w (spinFlip x η) * g η) = ∑ η, q * p.w η * g η := by
      calc
        _ = ∑ η, q * p.w (spinFlip x η) * g (spinFlip x η) := by simp only [hinv]
        _ = _ := hreindex (fun η => q * p.w η * g η)
    rw [hflip]
    simp_rw [mul_assoc]
    rw [← mul_sum]
    ring
  rw [hleft, hright] at hh
  linarith

/-- A product of shell factors; each actual defect contributes `s`. -/
def defectProduct {V : Type*} (S : Finset V) (ζ η : V → Spin) (s : ℝ) : ℝ :=
  ∏ x ∈ S, (1 + (s - 1) * defectIndicator ζ η x)

theorem defectProduct_nonneg {V : Type*} (S : Finset V) (ζ η : V → Spin)
    (s : ℝ) (hs : 1 ≤ s) : 0 ≤ defectProduct S ζ η s := by
  apply Finset.prod_nonneg
  intro x hx
  have h := defectIndicator_nonneg ζ η x
  exact add_nonneg (by norm_num) (mul_nonneg (sub_nonneg.mpr hs) h)

theorem defectProduct_flip {V : Type*} [DecidableEq V] (S : Finset V)
    (ζ η : V → Spin) (x : V) (hx : x ∉ S) (s : ℝ) :
    defectProduct S ζ (spinFlip x η) s = defectProduct S ζ η s := by
  apply Finset.prod_congr rfl
  intro y hy
  have hyx : y ≠ x := by intro h; subst y; exact hx hy
  simp [defectIndicator, hyx]

/-- Product moment domination for any dependent finite spin law. Only true
single-site conditional bounds are required; no independence or MGF assumption. -/
theorem defect_product_moment_bound {V : Type*} [Fintype V]
    (p : FinProb (V → Spin)) (S : Finset V) (ζ : V → Spin) (q s : ℝ)
    (hq : 0 ≤ q) (hs : 1 ≤ s)
    (hlocal : ∀ x ∈ S, defectConditionalBound p ζ x q) :
    p.expect (fun η => defectProduct S ζ η s) ≤ (1 + q * (s - 1)) ^ S.card := by
  induction S using Finset.induction_on with
  | empty => simp [defectProduct]
  | @insert x S hx ih =>
    have ih' := ih (fun y hy => hlocal y (mem_insert_of_mem hy))
    have hl := weighted_defect_bound p ζ x q hq (hlocal x (mem_insert_self _ _))
      (fun η => defectProduct S ζ η s) (fun η => defectProduct_nonneg _ _ _ _ hs)
      (fun η => defectProduct_flip S ζ η x hx s)
    have heq : p.expect (fun η => defectProduct (insert x S) ζ η s)
        = p.expect (fun η => defectProduct S ζ η s) +
          (s - 1) * p.expect (fun η => defectIndicator ζ η x * defectProduct S ζ η s) := by
      simp only [defectProduct, prod_insert hx]
      simp_rw [add_mul, one_mul, mul_assoc]
      rw [FinProb.expect_add, FinProb.expect_smul]
    rw [heq, card_insert_of_notMem hx, pow_succ]
    have hmul := mul_le_mul_of_nonneg_left hl (sub_nonneg.mpr hs)
    have hbase : 0 ≤ 1 + q * (s - 1) :=
      add_nonneg (by norm_num) (mul_nonneg hq (sub_nonneg.mpr hs))
    have hi := mul_le_mul_of_nonneg_left ih' hbase
    nlinarith

/-- The product statistic is exactly `s` to the actual dependent defect count. -/
theorem defectProduct_eq_pow {V : Type*} [Fintype V]
    (S : Finset V) (ζ η : V → Spin) (s : ℝ) :
    defectProduct S ζ η s = s ^ defectCount S ζ η := by
  induction S using Finset.induction_on with
  | empty => simp [defectProduct, defectCount]
  | @insert x S hx ih =>
    have hx' : x ∉ S.filter (fun y => η y ≠ ζ y) := by simp [hx]
    by_cases hd : η x ≠ ζ x
    · have hc : defectCount (insert x S) ζ η = defectCount S ζ η + 1 := by
        simp only [defectCount, Finset.filter_insert, if_pos hd,
          card_insert_of_notMem hx']
      rw [hc, pow_succ]
      simp only [defectProduct, prod_insert hx] at ih ⊢
      rw [ih]
      simp [defectIndicator, hd, mul_comm]
    · have hc : defectCount (insert x S) ζ η = defectCount S ζ η := by
        simp only [defectCount, Finset.filter_insert, if_neg hd]
      rw [hc]
      simp only [defectProduct, prod_insert hx] at ih ⊢
      rw [ih]
      simp [defectIndicator, hd]

/-- A mean bound for the actual dependent shell defect count. -/
theorem defect_mean_bound {V : Type*} [Fintype V]
    (p : FinProb (V → Spin)) (S : Finset V) (ζ : V → Spin) (q : ℝ)
    (hq : 0 ≤ q) (hlocal : ∀ x ∈ S, defectConditionalBound p ζ x q) :
    p.expect (fun η => (defectCount S ζ η : ℝ)) ≤ (S.card : ℝ) * q := by
  have hcount : ∀ η, (defectCount S ζ η : ℝ) = ∑ x ∈ S, defectIndicator ζ η x := by
    intro η
    classical
    rw [defectCount, ← Finset.sum_boole]
    simp only [defectIndicator]
  simp only [FinProb.expect, hcount, mul_sum]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ x ∈ S, q := by
      apply sum_le_sum
      intro x hx
      have hh := weighted_defect_bound p ζ x q hq (hlocal x hx)
        (fun _ => 1) (fun _ => by norm_num) (fun _ => rfl)
      simpa only [mul_one, FinProb.expect_const] using hh
    _ = _ := by simp

/-- Both paper (2.5) moment estimates for a dependent finite spin law. -/
theorem dependent_defect_moments {V : Type*} [Fintype V]
    (p : FinProb (V → Spin)) (S : Finset V) (ζ : V → Spin) (q b : ℝ)
    (hq : 0 ≤ q) (hb : 0 ≤ b)
    (hlocal : ∀ x ∈ S, defectConditionalBound p ζ x q) :
    p.expect (fun η => exp (b * (defectCount S ζ η : ℝ)))
      ≤ exp ((S.card : ℝ) * q * (exp b - 1)) ∧
    exp (-b * (S.card : ℝ) * q) ≤
      p.expect (fun η => exp (-b * (defectCount S ζ η : ℝ))) := by
  constructor
  · apply defect_exp_moment_upper_of_mgf S.card q b hq hb
      univ p.w (defectCount S ζ) (fun η _ => p.nonneg η) p.sum_one
    intro s hs
    simpa only [FinProb.expect, defectProduct_eq_pow] using
      defect_product_moment_bound p S ζ q s hq hs hlocal
  · apply defect_exp_moment_lower_jensen S.card q b hb hq
      univ p.w (fun η => (defectCount S ζ η : ℝ)) (fun η _ => p.nonneg η) p.sum_one
    exact defect_mean_bound p S ζ q hq hlocal

/-- The exact nearest-neighbor field acting on one site, including a fixed exterior. -/
def localField {V : Type*} [Fintype V] (Λ : Lattice V) (h : V → ℝ) (β : ℝ)
    (B T : Finset V) (φ η : V → Spin) (x : V) : ℝ :=
  h x + β * ((∑ y ∈ B, if Λ.adj x y then spinVal (η y) else 0) +
    ∑ y ∈ T, if Λ.adj x y then spinVal (φ y) else 0)

theorem interaction_flip_sub {V : Type*} [Fintype V] (Λ : Lattice V)
    (β : ℝ) (B : Finset V) (η : V → Spin) (x : V) (hx : x ∈ B) :
    Λ.interaction β B (spinFlip x η) - Λ.interaction β B η =
      -2 * β * spinVal (η x) * ∑ y ∈ B, if Λ.adj x y then spinVal (η y) else 0 := by
  have hadj : ∀ u v, Λ.adj u v ↔ Λ.adj v u := fun u v => ⟨Λ.symm, Λ.symm⟩
  have he : ∀ u v,
      (if Λ.adj u v then spinVal (spinFlip x η u) * spinVal (spinFlip x η v) else 0) -
        (if Λ.adj u v then spinVal (η u) * spinVal (η v) else 0) =
      (if u = x then (-2 * spinVal (η x)) *
        (if Λ.adj x v then spinVal (η v) else 0) else 0) +
      (if v = x then (-2 * spinVal (η x)) *
        (if Λ.adj x u then spinVal (η u) else 0) else 0) := by
    intro u v
    by_cases hu : u = x <;> by_cases hv : v = x
    · subst u; subst v; simp [Λ.irrefl]
    · subst u; by_cases ha : Λ.adj x v <;> simp [hv, ha] <;> ring
    · subst v; by_cases ha : Λ.adj x u <;>
        simp [hu, ha, hadj u x] <;> ring
    · simp [hu, hv]
  unfold Lattice.interaction
  rw [← mul_sub, ← sum_sub_distrib]
  simp_rw [← sum_sub_distrib, he, sum_add_distrib]
  have hfirst : (∑ u ∈ B, ∑ v ∈ B,
      if u = x then (-2 * spinVal (η x)) *
        (if Λ.adj x v then spinVal (η v) else 0) else 0) =
      (-2 * spinVal (η x)) * ∑ v ∈ B, if Λ.adj x v then spinVal (η v) else 0 := by
    simp_rw [Finset.sum_ite_irrel]
    simp [hx, mul_sum]
  have hsecond : (∑ u ∈ B, ∑ v ∈ B,
      if v = x then (-2 * spinVal (η x)) *
        (if Λ.adj x u then spinVal (η u) else 0) else 0) =
      (-2 * spinVal (η x)) * ∑ u ∈ B, if Λ.adj x u then spinVal (η u) else 0 := by
    simp [hx, mul_sum]
  rw [hfirst, hsecond]
  ring

theorem fieldEnergy_flip_sub {V : Type*} [Fintype V] (h : V → ℝ)
    (B : Finset V) (η : V → Spin) (x : V) (hx : x ∈ B) :
    Lattice.fieldEnergy h B (spinFlip x η) - Lattice.fieldEnergy h B η =
      -2 * h x * spinVal (η x) := by
  unfold Lattice.fieldEnergy
  rw [← sum_sub_distrib]
  have he : ∀ y ∈ B, h y * spinVal (spinFlip x η y) - h y * spinVal (η y) =
      if y = x then -2 * h x * spinVal (η x) else 0 := by
    intro y hy
    by_cases hxy : y = x
    · subst y; simp; ring
    · simp [hxy]
  rw [sum_congr rfl he]
  simp [hx]

theorem boundEnergy_flip_sub {V : Type*} [Fintype V] (Λ : Lattice V)
    (β : ℝ) (B T : Finset V) (φ η : V → Spin) (x : V) (hx : x ∈ B) :
    Λ.boundEnergy β B T φ (spinFlip x η) - Λ.boundEnergy β B T φ η =
      -2 * β * spinVal (η x) * ∑ y ∈ T, if Λ.adj x y then spinVal (φ y) else 0 := by
  unfold Lattice.boundEnergy
  rw [← mul_sub, ← sum_sub_distrib]
  simp_rw [← sum_sub_distrib]
  have he : ∀ u v,
      (if Λ.adj u v then spinVal (spinFlip x η u) * spinVal (φ v) else 0) -
        (if Λ.adj u v then spinVal (η u) * spinVal (φ v) else 0) =
      if u = x then (-2 * spinVal (η x)) *
        (if Λ.adj x v then spinVal (φ v) else 0) else 0 := by
    intro u v
    by_cases hu : u = x
    · subst u; by_cases ha : Λ.adj x v <;> simp [ha] <;> ring
    · simp [hu]
  simp_rw [he, Finset.sum_ite_irrel]
  simp [hx, mul_sum]
  ring

/-- Flipping a spin changes the actual corrected Ising energy by twice the
spin times its local field. -/
theorem isingWeight_flip_ratio {V : Type*} [Fintype V] (Λ : Lattice V)
    (h : V → ℝ) (β : ℝ) (B T : Finset V) (φ η : V → Spin)
    (x : V) (hx : x ∈ B) :
    isingWeight Λ h β B T φ (spinFlip x η) =
      isingWeight Λ h β B T φ η * exp (-2 * spinVal (η x) * localField Λ h β B T φ η x) := by
  have hi := interaction_flip_sub Λ β B η x hx
  have hf := fieldEnergy_flip_sub h B η x hx
  have hb := boundEnergy_flip_sub Λ β B T φ η x hx
  unfold isingWeight
  rw [← exp_add]
  congr 1
  unfold localField
  linarith

@[simp] theorem abs_spinVal (s : Spin) : |spinVal s| = 1 := by
  fin_cases s <;> norm_num

theorem neighbor_sum_abs_le {V : Type*} [Fintype V] (Λ : Lattice V)
    (D : Finset V) (η : V → Spin) (x : V) :
    |∑ y ∈ D, if Λ.adj x y then spinVal (η y) else 0| ≤
      ((D.filter (Λ.adj x)).card : ℝ) := by
  calc
    _ ≤ ∑ y ∈ D, |if Λ.adj x y then spinVal (η y) else 0| := abs_sum_le_sum_abs _ _
    _ = ∑ y ∈ D, if Λ.adj x y then (1 : ℝ) else 0 := by
      apply sum_congr rfl
      intro y hy
      split_ifs <;> simp
    _ = _ := by rw [← Finset.sum_boole]

theorem neighbor_two_sum_abs_le {V : Type*} [Fintype V] (Λ : Lattice V)
    (B T : Finset V) (hBT : Disjoint B T) (φ η : V → Spin) (x : V) :
    |(∑ y ∈ B, if Λ.adj x y then spinVal (η y) else 0) +
      ∑ y ∈ T, if Λ.adj x y then spinVal (φ y) else 0| ≤ (Λ.maxDegree : ℝ) := by
  have hdis : Disjoint (B.filter (Λ.adj x)) (T.filter (Λ.adj x)) :=
    hBT.mono (filter_subset _ _) (filter_subset _ _)
  have hsub : (B ∪ T).filter (Λ.adj x) ⊆ univ.filter (Λ.adj x) := by
    intro y hy
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hy).2⟩
  have hc : (B.filter (Λ.adj x)).card + (T.filter (Λ.adj x)).card ≤ Λ.maxDegree := by
    calc
      _ = ((B ∪ T).filter (Λ.adj x)).card := by
        rw [filter_union, card_union_of_disjoint hdis]
      _ ≤ (univ.filter (Λ.adj x)).card := card_le_card hsub
      _ ≤ _ := Λ.degree_le x
  have hB := neighbor_sum_abs_le Λ B η x
  have hT := neighbor_sum_abs_le Λ T φ x
  have ht := abs_add_le
    (∑ y ∈ B, if Λ.adj x y then spinVal (η y) else 0)
    (∑ y ∈ T, if Λ.adj x y then spinVal (φ y) else 0)
  have hc' : ((B.filter (Λ.adj x)).card : ℝ) +
      ((T.filter (Λ.adj x)).card : ℝ) ≤ (Λ.maxDegree : ℝ) := by exact_mod_cast hc
  linarith

/-- The signed local field is bounded below uniformly over all the other
spins and all fixed boundary conditions. -/
theorem localField_direction_ge {V : Type*} [Fintype V] (Λ : Lattice V)
    (h : V → ℝ) (β H d : ℝ) (B T : Finset V) (hBT : Disjoint B T)
    (φ η ζ : V → Spin) (x : V) (hβ : 0 ≤ β)
    (hdeg : (Λ.maxDegree : ℝ) ≤ 2 * d) (hh : H ≤ spinVal (ζ x) * h x) :
    H - 2 * d * β ≤ spinVal (ζ x) * localField Λ h β B T φ η x := by
  have hn := neighbor_two_sum_abs_le Λ B T hBT φ η x
  have hn' : |spinVal (ζ x) *
      ((∑ y ∈ B, if Λ.adj x y then spinVal (η y) else 0) +
        ∑ y ∈ T, if Λ.adj x y then spinVal (φ y) else 0)| ≤ 2 * d := by
    simpa only [abs_mul, abs_spinVal, one_mul] using hn.trans hdeg
  have hlo := (abs_le.mp hn').1
  unfold localField
  nlinarith [mul_le_mul_of_nonneg_left hlo hβ]

/-- Distinct spins have opposite real values. -/
theorem spinVal_eq_neg_of_ne {a b : Spin} (h : a ≠ b) : spinVal a = -spinVal b := by
  fin_cases a <;> fin_cases b <;> simp_all

/-- The actual Ising Gibbs law satisfies the uniform single-site defect
probability bound of Lemma 2.3, with arbitrary fixed exterior spins. -/
theorem gibbs_defect_conditional_bound {V : Type*} [Fintype V]
    (Λ : Lattice V) (h : V → ℝ) (β H d : ℝ) (B T : Finset V)
    (hBT : Disjoint B T) (φ ζ : V → Spin) (x : V) (hx : x ∈ B)
    (hβ : 0 ≤ β) (hdeg : (Λ.maxDegree : ℝ) ≤ 2 * d)
    (hh : H ≤ spinVal (ζ x) * h x) :
    defectConditionalBound (gibbs Λ h β B T φ) ζ x (qH H d β) := by
  intro η hd
  have hl := localField_direction_ge Λ h β H d B T hBT φ η ζ x hβ hdeg hh
  have he : exp (2 * (H - 2 * d * β)) ≤
      exp (-2 * spinVal (η x) * localField Λ h β B T φ η x) := by
    apply exp_le_exp.mpr
    rw [spinVal_eq_neg_of_ne hd]
    linarith
  have hw := isingWeight_flip_ratio Λ h β B T φ η x hx
  have hwpos := isingWeight_pos Λ h β B T φ η
  have hzpos := isingZ_pos Λ h β B T φ
  have hwle : isingWeight Λ h β B T φ η * exp (2 * (H - 2 * d * β)) ≤
      isingWeight Λ h β B T φ (spinFlip x η) := by
    rw [hw]
    exact mul_le_mul_of_nonneg_left he hwpos.le
  have hbase : isingWeight Λ h β B T φ η ≤ qH H d β *
      (isingWeight Λ h β B T φ η + isingWeight Λ h β B T φ (spinFlip x η)) := by
    unfold qH
    have hepos : 0 < 1 + exp (2 * (H - 2 * d * β)) := by positivity
    rw [one_div, inv_mul_eq_div]
    apply (le_div_iff₀ hepos).2
    nlinarith
  change isingWeight Λ h β B T φ η / isingZ Λ h β B T φ ≤
    qH H d β * (isingWeight Λ h β B T φ η / isingZ Λ h β B T φ +
      isingWeight Λ h β B T φ (spinFlip x η) / isingZ Λ h β B T φ)
  simpa only [add_div, mul_div_assoc] using div_le_div_of_nonneg_right hbase hzpos.le

/-- Lemma 2.3 for the actual finite Ising measure. Shell spins may be fully
dependent. All premises describe the graph, its physical parameters, and fields. -/
theorem lemma_2_3_gibbs {V : Type*} [Fintype V]
    (Λ : Lattice V) (h : V → ℝ) (β H d b : ℝ) (B T S : Finset V)
    (hBT : Disjoint B T) (hSB : S ⊆ B) (φ ζ : V → Spin)
    (hβ : 0 ≤ β) (hb : 0 ≤ b) (hdeg : (Λ.maxDegree : ℝ) ≤ 2 * d)
    (hh : ∀ x ∈ S, H ≤ spinVal (ζ x) * h x) :
    (gibbs Λ h β B T φ).expect (fun η => exp (b * (defectCount S ζ η : ℝ)))
      ≤ exp ((S.card : ℝ) * qH H d β * (exp b - 1)) ∧
    exp (-b * (S.card : ℝ) * qH H d β) ≤
      (gibbs Λ h β B T φ).expect (fun η => exp (-b * (defectCount S ζ η : ℝ))) := by
  apply dependent_defect_moments _ S ζ _ b (qH_pos H d β).le hb
  intro x hx
  exact gibbs_defect_conditional_bound Λ h β H d B T hBT φ ζ x (hSB hx)
    hβ hdeg (hh x hx)

/-- Defect count as a sum of the actual indicators. -/
theorem defectCount_eq_sum_indicator {V : Type*} [Fintype V]
    (S : Finset V) (ζ η : V → Spin) :
    (defectCount S ζ η : ℝ) = ∑ x ∈ S, defectIndicator ζ η x := by
  rw [defectCount, ← Finset.sum_boole]
  rfl

theorem fieldEnergy_abs_le {V : Type*} [Fintype V] (h : V → ℝ)
    (B : Finset V) (η : V → Spin) : |Lattice.fieldEnergy h B η| ≤ fieldMass h B := by
  unfold Lattice.fieldEnergy fieldMass
  calc
    _ ≤ ∑ x ∈ B, |h x * spinVal (η x)| := abs_sum_le_sum_abs _ _
    _ = _ := by simp only [abs_mul, abs_spinVal, mul_one]

/-- Exact difference of boundary energies, grouped by boundary site. -/
theorem boundEnergy_sub_eq {V : Type*} [Fintype V] (Λ : Lattice V)
    (β : ℝ) (B S : Finset V) (ζ τ η : V → Spin) :
    Λ.boundEnergy β B S τ η - Λ.boundEnergy β B S ζ η =
      β * ∑ y ∈ S, (spinVal (τ y) - spinVal (ζ y)) *
        ∑ x ∈ B, if Λ.adj y x then spinVal (η x) else 0 := by
  have hadj : ∀ u v, Λ.adj u v ↔ Λ.adj v u := fun u v => ⟨Λ.symm, Λ.symm⟩
  unfold Lattice.boundEnergy
  rw [← mul_sub, ← sum_sub_distrib]
  simp_rw [← sum_sub_distrib]
  rw [sum_comm]
  congr 1
  apply sum_congr rfl
  intro y hy
  rw [mul_sum]
  apply sum_congr rfl
  intro x hx
  by_cases ha : Λ.adj y x <;> simp [ha, hadj x y] <;> ring

/-- Maximum number of interior neighbors of a shell site, with value zero
for an empty shell. This is the exact combinatorial constant in paper (2.2). -/
def shellDegree {V : Type*} [Fintype V] (Λ : Lattice V) (B S : Finset V) : ℕ :=
  S.sup (fun y => (B.filter (Λ.adj y)).card)

theorem shellDegree_le_maxDegree {V : Type*} [Fintype V] (Λ : Lattice V)
    (B S : Finset V) : shellDegree Λ B S ≤ Λ.maxDegree := by
  apply Finset.sup_le
  intro y hy
  apply (card_le_card ?_).trans (Λ.degree_le y)
  intro z hz
  exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hz).2⟩

/-- A defective boundary spin costs at most two times the number of its
incident edges in absolute tilt. -/
theorem boundEnergy_sub_abs_le {V : Type*} [Fintype V] (Λ : Lattice V)
    (β : ℝ) (hβ : 0 ≤ β) (B S : Finset V) (ζ τ η : V → Spin) :
    |Λ.boundEnergy β B S τ η - Λ.boundEnergy β B S ζ η| ≤
      2 * β * (shellDegree Λ B S : ℝ) * (defectCount S ζ τ : ℝ) := by
  rw [boundEnergy_sub_eq, abs_mul, abs_of_nonneg hβ]
  have he : ∀ y ∈ S,
      |(spinVal (τ y) - spinVal (ζ y)) *
        ∑ x ∈ B, if Λ.adj y x then spinVal (η x) else 0| ≤
      2 * (shellDegree Λ B S : ℝ) * defectIndicator ζ τ y := by
    intro y hy
    have hs : |spinVal (τ y) - spinVal (ζ y)| = 2 * defectIndicator ζ τ y := by
      unfold defectIndicator
      generalize τ y = a
      generalize ζ y = b
      fin_cases a <;> fin_cases b <;> norm_num
    have hn : |∑ x ∈ B, if Λ.adj y x then spinVal (η x) else 0| ≤
        (shellDegree Λ B S : ℝ) := by
      apply (neighbor_sum_abs_le Λ B η y).trans
      exact_mod_cast (Finset.le_sup (f := fun y => (B.filter (Λ.adj y)).card) hy)
    rw [abs_mul, hs]
    have hh := mul_le_mul_of_nonneg_left hn
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (defectIndicator_nonneg ζ τ y))
    nlinarith
  calc
    _ ≤ β * ∑ y ∈ S, |(spinVal (τ y) - spinVal (ζ y)) *
        ∑ x ∈ B, if Λ.adj y x then spinVal (η x) else 0| :=
      mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) hβ
    _ ≤ β * ∑ y ∈ S, 2 * (shellDegree Λ B S : ℝ) * defectIndicator ζ τ y :=
      mul_le_mul_of_nonneg_left (sum_le_sum he) hβ
    _ = _ := by rw [← mul_sum, ← defectCount_eq_sum_indicator]; ring

/-- The actual unnormalized logarithmic tilt of a conditional box relative
to the zero-field box with the prescribed shell. -/
def shellTilt {V : Type*} [Fintype V] (Λ : Lattice V) (h : V → ℝ)
    (β : ℝ) (B S : Finset V) (ζ τ η : V → Spin) : ℝ :=
  Lattice.fieldEnergy h B η + Λ.boundEnergy β B S τ η - Λ.boundEnergy β B S ζ η

theorem shellTilt_abs_le {V : Type*} [Fintype V] (Λ : Lattice V)
    (h : V → ℝ) (β : ℝ) (hβ : 0 ≤ β) (B S : Finset V) (ζ τ η : V → Spin) :
    |shellTilt Λ h β B S ζ τ η| ≤
      fieldMass h B + 2 * β * (shellDegree Λ B S : ℝ) * (defectCount S ζ τ : ℝ) := by
  have hf := fieldEnergy_abs_le h B η
  have hb := boundEnergy_sub_abs_le Λ β hβ B S ζ τ η
  have ht := abs_add_le (Lattice.fieldEnergy h B η)
    (Λ.boundEnergy β B S τ η - Λ.boundEnergy β B S ζ η)
  unfold shellTilt
  rw [add_sub_assoc]
  linarith

/-- The paper's oscillation estimate, proved from the actual Gibbs Hamiltonian. -/
theorem shellTilt_oscillation {V : Type*} [Fintype V] (Λ : Lattice V)
    (h : V → ℝ) (β : ℝ) (hβ : 0 ≤ β) (B S : Finset V) (ζ τ η ξ : V → Spin) :
    shellTilt Λ h β B S ζ τ η - shellTilt Λ h β B S ζ τ ξ ≤
      2 * fieldMass h B + 4 * β * (shellDegree Λ B S : ℝ) * (defectCount S ζ τ : ℝ) := by
  have hη := abs_le.mp (shellTilt_abs_le Λ h β hβ B S ζ τ η)
  have hξ := abs_le.mp (shellTilt_abs_le Λ h β hβ B S ζ τ ξ)
  linarith

/-- A finite normalization argument: bounded logarithmic oscillation gives
the normalized density bound, with no assumed density certificate. -/
theorem normalized_exp_density_upper {α : Type*} [Fintype α] [Nonempty α]
    (f g : α → ℝ) (D : ℝ)
    (hosc : ∀ x y, (f x - g x) - (f y - g y) ≤ D) (x : α) :
    exp (f x) / (∑ y, exp (f y)) ≤
      exp D * (exp (g x) / ∑ y, exp (g y)) := by
  have hZf : 0 < ∑ y, exp (f y) := sum_pos (fun y _ => exp_pos _) univ_nonempty
  have hZg : 0 < ∑ y, exp (g y) := sum_pos (fun y _ => exp_pos _) univ_nonempty
  have hp : ∀ y, exp (f x) * exp (g y) ≤ exp D * exp (g x) * exp (f y) := by
    intro y
    rw [← exp_add, ← exp_add, ← exp_add]
    exact exp_le_exp.mpr (by linarith [hosc x y])
  have hh := sum_le_sum (s := (univ : Finset α)) (fun y _ => hp y)
  rw [← mul_sum, ← mul_sum] at hh
  apply (div_le_iff₀ hZf).2
  have hh' := (le_div_iff₀ hZg).2 hh
  convert hh' using 1 <;> ring

/-- Pointwise density sandwich for the actual Gibbs laws, supplying the
missing unconditional hypotheses in the soft-shell comparison. -/
theorem gibbs_shell_density {V : Type*} [Fintype V] (Λ : Lattice V)
    (h : V → ℝ) (β : ℝ) (hβ : 0 ≤ β) (B S : Finset V) (ζ τ : V → Spin) :
    let D := 2 * fieldMass h B + 4 * β * (shellDegree Λ B S : ℝ) * (defectCount S ζ τ : ℝ)
    ∀ η, exp (-D) * (pureGibbs Λ β B S ζ).w η ≤ (gibbs Λ h β B S τ).w η ∧
      (gibbs Λ h β B S τ).w η ≤ exp D * (pureGibbs Λ β B S ζ).w η := by
  dsimp only
  let f := fun η => Λ.interaction β B η + Lattice.fieldEnergy h B η +
    Λ.boundEnergy β B S τ η
  let g := fun η => Λ.interaction β B η + Lattice.fieldEnergy (fun _ => 0) B η +
    Λ.boundEnergy β B S ζ η
  let D := 2 * fieldMass h B + 4 * β * (shellDegree Λ B S : ℝ) * (defectCount S ζ τ : ℝ)
  have ht : ∀ η, f η - g η = shellTilt Λ h β B S ζ τ η := by
    intro η
    simp only [f, g, shellTilt, Lattice.fieldEnergy, zero_mul, sum_const_zero]
    ring
  have ho : ∀ η ξ, (f η - g η) - (f ξ - g ξ) ≤ D := by
    intro η ξ
    rw [ht, ht]
    exact shellTilt_oscillation Λ h β hβ B S ζ τ η ξ
  have ho' : ∀ η ξ, (g η - f η) - (g ξ - f ξ) ≤ D := by
    intro η ξ
    have hh := ho ξ η
    linarith
  intro η
  have hu := normalized_exp_density_upper f g D ho η
  have hl := normalized_exp_density_upper g f D ho' η
  change exp (-D) * (exp (g η) / ∑ ξ, exp (g ξ)) ≤ exp (f η) / ∑ ξ, exp (f ξ) ∧
    exp (f η) / ∑ ξ, exp (f ξ) ≤ exp D * (exp (g η) / ∑ ξ, exp (g ξ))
  constructor
  · have hh := mul_le_mul_of_nonneg_left hl (exp_pos (-D)).le
    rw [← mul_assoc, ← exp_add] at hh
    simpa using hh
  · exact hu

/-- The usual ratio form of the single-site Gibbs conditional probability. -/
theorem gibbs_defect_conditional_probability {V : Type*} [Fintype V]
    (Λ : Lattice V) (h : V → ℝ) (β H d : ℝ) (B T : Finset V)
    (hBT : Disjoint B T) (φ ζ : V → Spin) (x : V) (hx : x ∈ B)
    (hβ : 0 ≤ β) (hdeg : (Λ.maxDegree : ℝ) ≤ 2 * d)
    (hh : H ≤ spinVal (ζ x) * h x) (η : V → Spin) (hd : η x ≠ ζ x) :
    (gibbs Λ h β B T φ).w η /
      ((gibbs Λ h β B T φ).w η + (gibbs Λ h β B T φ).w (spinFlip x η)) ≤ qH H d β := by
  have hη : 0 < (gibbs Λ h β B T φ).w η :=
    div_pos (isingWeight_pos _ _ _ _ _ _ _) (isingZ_pos _ _ _ _ _ _)
  apply (div_le_iff₀ (add_pos_of_pos_of_nonneg hη ((gibbs Λ h β B T φ).nonneg _))).2
  exact gibbs_defect_conditional_bound Λ h β H d B T hBT φ ζ x hx hβ hdeg hh η hd

/-- Paper (2.3) and (2.4), instantiated to the actual Gibbs energies and the
exact shell-to-interior degree. Neither density comparison is a premise. -/
theorem gibbs_shell_energy_variance {V : Type*} [Fintype V] (Λ : Lattice V)
    (h : V → ℝ) (β : ℝ) (hβ : 0 ≤ β) (B S : Finset V) (ζ τ : V → Spin)
    (G : UpdateGraph (V → Spin)) (f : (V → Spin) → ℝ) :
    let D := 2 * fieldMass h B + 4 * β * (shellDegree Λ B S : ℝ) * (defectCount S ζ τ : ℝ)
    exp (-D) * FinProb.variance (pureGibbs Λ β B S ζ) f ≤
      FinProb.variance (gibbs Λ h β B S τ) f ∧
    G.dirichlet (gibbs Λ h β B S τ) f ≤
      exp D * G.dirichlet (pureGibbs Λ β B S ζ) f := by
  dsimp only
  have hd := gibbs_shell_density Λ h β hβ B S ζ τ
  exact ⟨FinProb.variance_of_density_lower (fun η => (hd η).1) f,
    UpdateGraph.dirichlet_le_of_density (exp_nonneg _) (fun η => (hd η).2) G f⟩

end Paper09
