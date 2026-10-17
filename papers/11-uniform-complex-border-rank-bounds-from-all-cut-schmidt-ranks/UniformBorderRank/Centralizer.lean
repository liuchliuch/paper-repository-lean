import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Tactic

/-!
# Lemma 2.3: Centralizer bound

If finitely many unital subalgebras `𝒜_i ⊆ End(ℂ^r)` pairwise commute across
sites, then at most `r^2 - 1` of them are noncommutative.

Proof (paper): list the noncommutative algebras `𝒜_{q_1},…,𝒜_{q_b}` and set
`Z_0 = End(ℂ^r)`, `Z_k = ⋂_{j≤k} Comm(𝒜_{q_j})`.  Cross-site commutation gives
`𝒜_{q_k} ⊆ Z_{k-1}`.  Noncommutativity of `𝒜_{q_k}` yields `x,y ∈ 𝒜_{q_k}`
with `x*y ≠ y*x`; then `x ∈ Z_{k-1} \ Z_k`, so the chain strictly decreases.
Every `Z_k` contains the scalars, so at most `r^2 - 1` strict drops occur.
-/

noncomputable section

namespace UniformBorderRank

open Submodule

/-- Endomorphisms of `ℂ^r` as `r × r` complex matrices. -/
abbrev EndMat (r : ℕ) := Matrix (Fin r) (Fin r) ℂ

/-- Centralizer of `S` as a `ℂ`-subspace of `End(ℂ^r)`. -/
def centralizer {r : ℕ} (S : Set (Matrix (Fin r) (Fin r) ℂ)) :
    Submodule ℂ (Matrix (Fin r) (Fin r) ℂ) where
  carrier := { z | ∀ x ∈ S, z * x = x * z }
  zero_mem' := by
    intro x _hx; simp
  add_mem' := by
    intro a b ha hb x hx
    rw [add_mul, mul_add, ha x hx, hb x hx]
  smul_mem' := by
    intro c a ha x hx
    have ha' := ha x hx
    have h1 : (c • a) * x = c • (a * x) := smul_mul_assoc c a x
    have h2 : x * (c • a) = c • (x * a) := by
      ext i j
      simp only [Matrix.mul_apply]
      have hsmul : ∀ k : Fin r, (c • a) k j = c * a k j := fun _ => rfl
      conv_lhs => simp only [hsmul]
      show ∑ k, x i k * (c * a k j) = _
      have hR : (c • (x * a)) i j = c * ∑ k, x i k * a k j := rfl
      rw [hR, Finset.mul_sum]
      congr 1
      ext k
      ring
    have h3 : (c • a) * x = x * (c • a) := by
      rw [h1, h2, ha']
    exact h3

lemma one_mem_centralizer {r : ℕ} (S : Set (Matrix (Fin r) (Fin r) ℂ)) :
    (1 : Matrix (Fin r) (Fin r) ℂ) ∈ centralizer S := by
  intro x _hx; simp

lemma finrank_matrix_sq (r : ℕ) :
    Module.finrank ℂ (Matrix (Fin r) (Fin r) ℂ) = r ^ 2 := by
  have h := Module.finrank_matrix (m := Fin r) (n := Fin r) (R := ℂ) (M := ℂ)
  calc Module.finrank ℂ (Matrix (Fin r) (Fin r) ℂ)
      = Fintype.card (Fin r) * Fintype.card (Fin r) * Module.finrank ℂ ℂ := h
    _ = r * r * 1 := by simp [Fintype.card_fin, Module.finrank_self]
    _ = r ^ 2 := by ring

/-- A set of matrices is noncommutative if some pair fails to commute. -/
def IsNoncommutative {r : ℕ} (A : Set (Matrix (Fin r) (Fin r) ℂ)) : Prop :=
  ∃ x ∈ A, ∃ y ∈ A, x * y ≠ y * x

/-- Cross-site commutation. -/
def CrossComm {r : ℕ} (A B : Set (Matrix (Fin r) (Fin r) ℂ)) : Prop :=
  ∀ x ∈ A, ∀ y ∈ B, x * y = y * x

/-- If `z ∈ Z` does not commute with some `x ∈ S`, then `Z ⊓ centralizer S < Z`. -/
lemma inf_centralizer_lt_of_not_mem {r : ℕ}
    (Z : Submodule ℂ (Matrix (Fin r) (Fin r) ℂ))
    (S : Set (Matrix (Fin r) (Fin r) ℂ))
    (z : Matrix (Fin r) (Fin r) ℂ)
    (hz : z ∈ Z) (hnot : ¬ (z ∈ centralizer S)) :
    Z ⊓ centralizer S < Z := by
  refine lt_of_le_of_ne inf_le_left ?_
  intro h
  have hz2 : z ∈ (Z ⊓ centralizer S) := by
    rw [h]; exact hz
  exact hnot hz2.2

/-- A noncommutative algebra `A ⊆ Z` witnesses a strict drop `Z ⊓ Comm(A) < Z`. -/
lemma strict_drop_of_noncomm {r : ℕ}
    (Z : Submodule ℂ (Matrix (Fin r) (Fin r) ℂ))
    (A : Set (Matrix (Fin r) (Fin r) ℂ))
    (hA : IsNoncommutative A)
    (hAZ : ∀ x ∈ A, x ∈ Z) :
    Z ⊓ centralizer A < Z := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hA
  have hz : x ∈ Z := hAZ x hx
  have hnot : ¬ (x ∈ centralizer A) := by
    intro hc
    exact hxy (hc y hy)
  exact inf_centralizer_lt_of_not_mem Z A x hz hnot

/-- Centralizer chain `Z_0 = ⊤`, `Z_{k+1} = Z_k ⊓ centralizer (q k)`. -/
def Zchain {r : ℕ} (q : ℕ → Set (Matrix (Fin r) (Fin r) ℂ)) :
    ℕ → Submodule ℂ (Matrix (Fin r) (Fin r) ℂ)
  | 0 => ⊤
  | k + 1 => Zchain q k ⊓ centralizer (q k)

lemma one_mem_Zchain {r : ℕ} (q : ℕ → Set (Matrix (Fin r) (Fin r) ℂ)) (k : ℕ) :
    (1 : Matrix (Fin r) (Fin r) ℂ) ∈ Zchain q k := by
  induction k with
  | zero => simp [Zchain]
  | succ k ih =>
    show (1 : Matrix (Fin r) (Fin r) ℂ) ∈ Zchain q k ⊓ centralizer (q k)
    exact ⟨ih, one_mem_centralizer (q k)⟩

lemma Zchain_succ_lt {r : ℕ} (q : ℕ → Set (Matrix (Fin r) (Fin r) ℂ)) (k : ℕ)
    (hnc : IsNoncommutative (q k))
    (hsub : ∀ x ∈ q k, x ∈ Zchain q k) :
    Zchain q (k + 1) < Zchain q k := by
  show Zchain q k ⊓ centralizer (q k) < Zchain q k
  exact strict_drop_of_noncomm (Zchain q k) (q k) hnc hsub

/-- If `x` lies in `centralizer (q j)` for all `j < k`, then `x ∈ Zchain q k`. -/
lemma mem_Zchain_of_commutes {r : ℕ}
    (q : ℕ → Set (Matrix (Fin r) (Fin r) ℂ))
    (k : ℕ) (x : Matrix (Fin r) (Fin r) ℂ)
    (h : ∀ j < k, x ∈ centralizer (q j)) :
    x ∈ Zchain q k := by
  induction k with
  | zero => simp [Zchain]
  | succ n ihn =>
    show x ∈ Zchain q n ⊓ centralizer (q n)
    exact ⟨ihn (fun j hj => h j (by omega)), h n (by omega)⟩

/-- Each strict step drops `finrank` by at least 1. -/
lemma finrank_Zchain_le {r : ℕ}
    (q : ℕ → Set (Matrix (Fin r) (Fin r) ℂ))
    (b : ℕ)
    (hdrop : ∀ k < b, Zchain q (k + 1) < Zchain q k) :
    Module.finrank ℂ (Zchain q b) + b ≤ Module.finrank ℂ (Zchain q 0) := by
  induction b with
  | zero => simp
  | succ n ih =>
    have hlt := hdrop n (by omega)
    have h1 : Module.finrank ℂ (Zchain q (n + 1)) < Module.finrank ℂ (Zchain q n) :=
      @finrank_lt_finrank_of_lt ℂ (Fin r → Fin r → ℂ) _ _ _
        (Zchain q (n + 1)) (Zchain q n) _ hlt
    have := ih (fun k hk => hdrop k (by omega))
    omega

/-- **Lemma 2.3 (Centralizer bound).**
    At most `r^2 - 1` of the mutually commuting unital subalgebras of
    `End(ℂ^r)` are noncommutative. -/
theorem centralizer_bound {r : ℕ} (hr : 1 ≤ r)
    (q : ℕ → Set (Matrix (Fin r) (Fin r) ℂ))
    (b : ℕ)
    (hcomm : ∀ i j, i < b → j < b → i ≠ j → CrossComm (q i) (q j))
    (hnc : ∀ k < b, IsNoncommutative (q k)) :
    b ≤ r ^ 2 - 1 := by
  have hsub : ∀ k < b, ∀ x ∈ q k, x ∈ Zchain q k := by
    intro k hk x hx
    apply mem_Zchain_of_commutes
    intro j hj y hy
    exact hcomm k j hk (by omega) (by omega) x hx y hy
  have hdrop : ∀ k < b, Zchain q (k + 1) < Zchain q k := by
    intro k hk
    exact Zchain_succ_lt q k (hnc k hk) (hsub k hk)
  have hchain := finrank_Zchain_le q b hdrop
  have hfin0 : Module.finrank ℂ (Zchain q 0) = r ^ 2 := by
    show Module.finrank ℂ (⊤ : Submodule ℂ (Matrix (Fin r) (Fin r) ℂ)) = _
    rw [finrank_top, finrank_matrix_sq]
  have hone0 : (1 : Matrix (Fin r) (Fin r) ℂ) ≠ 0 := by
    have hr0 : 0 < r := by omega
    have h11 : (1 : Matrix (Fin r) (Fin r) ℂ) ⟨0, hr0⟩ ⟨0, hr0⟩ = 1 := rfl
    have h10 : (0 : Matrix (Fin r) (Fin r) ℂ) ⟨0, hr0⟩ ⟨0, hr0⟩ = 0 := rfl
    intro h
    have := h11
    rw [h, h10] at this
    exact absurd this (by norm_num)
  have hne_bot : Zchain q b ≠ ⊥ := by
    intro h
    have h1 : (1 : Matrix (Fin r) (Fin r) ℂ) ∈ Zchain q b := one_mem_Zchain q b
    rw [h, Submodule.mem_bot] at h1
    exact hone0 h1
  have hone : 1 ≤ Module.finrank ℂ (Zchain q b) := by
    have hiff := @Submodule.one_le_finrank_iff
    exact (hiff (R := ℂ) (M := Fin r → Fin r → ℂ) (S := Zchain q b)).2 hne_bot
  rw [hfin0] at hchain
  omega

/-- The ambient matrix dimension (not the generated-algebra assertion). -/
lemma commutative_generated_dim_le (r : ℕ) :
    Module.finrank ℂ (Matrix (Fin r) (Fin r) ℂ) ≤ r ^ 2 := by
  rw [finrank_matrix_sq]

/-- The matrices belonging to commutative sites. -/
def goodGenerators {ι : Type*} {r : ℕ}
    (A : ι → Subalgebra ℂ (EndMat r)) : Set (EndMat r) :=
  {x | ∃ i, ¬ IsNoncommutative (A i : Set (EndMat r)) ∧ x ∈ A i}

/-- Cross-site commutation extends to the algebras generated by the sites. -/
theorem crossComm_adjoin {r : ℕ} {S T : Set (EndMat r)}
    (h : CrossComm S T) :
    CrossComm (Algebra.adjoin ℂ S : Set (EndMat r))
      (Algebra.adjoin ℂ T : Set (EndMat r)) := by
  intro x hx y hy
  exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hy (fun t ht =>
    (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hx (fun s hs =>
      (show Commute s t from h s hs t ht).symm)).symm)).eq

lemma goodGenerators_commute {ι : Type*} {r : ℕ}
    (A : ι → Subalgebra ℂ (EndMat r))
    (hcomm : ∀ i j, i ≠ j → CrossComm (A i : Set (EndMat r)) (A j : Set (EndMat r))) :
    ∀ x ∈ goodGenerators A, ∀ y ∈ goodGenerators A, x * y = y * x := by
  rintro x ⟨i, hi, hx⟩ y ⟨j, hj, hy⟩
  by_cases hij : i = j
  · subst j
    by_contra hn
    exact hi ⟨x, hx, y, hy, hn⟩
  · exact hcomm i j hij x hx y hy

/-- The algebra generated by the commutative sites is actually commutative. -/
theorem goodAlgebra_commutative {ι : Type*} {r : ℕ}
    (A : ι → Subalgebra ℂ (EndMat r))
    (hcomm : ∀ i j, i ≠ j → CrossComm (A i : Set (EndMat r)) (A j : Set (EndMat r))) :
    ∀ x ∈ Algebra.adjoin ℂ (goodGenerators A),
      ∀ y ∈ Algebra.adjoin ℂ (goodGenerators A), x * y = y * x := by
  intro x hx y hy
  letI := Algebra.adjoinCommRingOfComm ℂ (goodGenerators_commute A hcomm)
  exact congrArg Subtype.val (mul_comm
    (⟨x, hx⟩ : Algebra.adjoin ℂ (goodGenerators A)) ⟨y, hy⟩)

theorem goodAlgebra_finrank_le {ι : Type*} {r : ℕ}
    (A : ι → Subalgebra ℂ (EndMat r)) :
    Module.finrank ℂ (Algebra.adjoin ℂ (goodGenerators A)) ≤ r ^ 2 := by
  let S := Algebra.adjoin ℂ (goodGenerators A)
  let f : S →ₗ[ℂ] (Fin r → Fin r → ℂ) :=
    { toFun := fun x => x.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext h
  have h := f.finrank_le_finrank_of_injective hf
  simpa [Module.finrank_pi_fintype, pow_two] using h

def noncommutativeSites {ι : Type*} [Fintype ι] {r : ℕ}
    (A : ι → Subalgebra ℂ (EndMat r)) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => IsNoncommutative (A i : Set (EndMat r)))

/-- Full finite-family centralizer bound: count the exceptional sites, and
retain a commutative generated algebra of bounded dimension. -/
theorem centralizer_algebras {ι : Type*} [Fintype ι] {r : ℕ} (hr : 1 ≤ r)
    (A : ι → Subalgebra ℂ (EndMat r))
    (hcomm : ∀ i j, i ≠ j → CrossComm (A i : Set (EndMat r)) (A j : Set (EndMat r))) :
    (noncommutativeSites A).card ≤ r ^ 2 - 1 ∧
    (∀ x ∈ Algebra.adjoin ℂ (goodGenerators A),
      ∀ y ∈ Algebra.adjoin ℂ (goodGenerators A), x * y = y * x) ∧
    Module.finrank ℂ (Algebra.adjoin ℂ (goodGenerators A)) ≤ r ^ 2 := by
  classical
  refine ⟨?_, goodAlgebra_commutative A hcomm, goodAlgebra_finrank_le A⟩
  let Q := Finset.univ.filter (fun i => IsNoncommutative (A i : Set (EndMat r)))
  let e := (Fintype.equivFin Q).symm
  let q : ℕ → Set (EndMat r) := fun k =>
    if h : k < Fintype.card Q then (A (e ⟨k, h⟩) : Set (EndMat r)) else ∅
  have hcross : ∀ i j, i < Fintype.card Q → j < Fintype.card Q → i ≠ j →
      CrossComm (q i) (q j) := by
    intro i j hi hj hij
    simp only [q, dif_pos hi, dif_pos hj]
    apply hcomm
    intro he
    have he' : e ⟨i, hi⟩ = e ⟨j, hj⟩ := Subtype.ext he
    have := congrArg Fin.val (e.injective he')
    exact hij this
  have hnc : ∀ k < Fintype.card Q, IsNoncommutative (q k) := by
    intro k hk
    simp only [q, dif_pos hk]
    exact (Finset.mem_filter.mp (e ⟨k, hk⟩).property).2
  simpa only [Fintype.card_coe, noncommutativeSites] using centralizer_bound hr q (Fintype.card Q) hcross hnc

end UniformBorderRank
