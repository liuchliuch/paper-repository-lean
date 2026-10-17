import UniformBorderRank.Flattening
import UniformBorderRank.FdRank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Genuine consequences of the all-cut rank hypothesis. -/
noncomputable section
namespace UniformBorderRank
open Finset

lemma rank_one_cross {α β : Type*} [Fintype β] (A : α → β → ℂ)
    (h : Module.finrank ℂ (Submodule.span ℂ (Set.range A)) ≤ 1)
    (a b : α) (c e : β) : A a c * A b e = A a e * A b c := by
  classical
  let W := Submodule.span ℂ (Set.range A)
  change Module.finrank ℂ W ≤ 1 at h
  have ha : A a ∈ W := Submodule.subset_span ⟨a, rfl⟩
  have hb : A b ∈ W := Submodule.subset_span ⟨b, rfl⟩
  by_cases hn : A a = 0
  · simp [hn]
  · have hx : (⟨A a, ha⟩ : W) ≠ 0 := by
      intro hh
      exact hn (congrArg Subtype.val hh)
    have hdim : Module.finrank ℂ W = 1 := by
      have hbot : W ≠ ⊥ := by
        intro hh
        have : A a = 0 := by simpa [hh] using ha
        exact hn this
      have := Submodule.one_le_finrank_iff.mpr hbot
      omega
    obtain ⟨z, hz⟩ := exists_smul_eq_of_finrank_eq_one hdim hx (⟨A b, hb⟩ : W)
    have heq : A b = z • A a := (congrArg Subtype.val hz).symm
    rw [heq]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

def mixIndex {N : ℕ} {d : Fin N → ℕ} (u v : ∀ i, Fin (d i))
    (S : Finset (Fin N)) : ∀ i, Fin (d i) := fun i => if i ∈ S then u i else v i

@[simp] lemma mixIndex_empty {N : ℕ} {d : Fin N → ℕ} (u v : ∀ i, Fin (d i)) :
    mixIndex u v ∅ = v := by funext i; simp [mixIndex]

@[simp] lemma mixIndex_univ {N : ℕ} {d : Fin N → ℕ} (u v : ∀ i, Fin (d i)) :
    mixIndex u v univ = u := by funext i; simp [mixIndex]

lemma schmidtRank_one_cross {N : ℕ} {d : Fin N → ℕ} (T : Coeffs d)
    (S : Finset (Fin N)) (h : schmidtRank d T S ≤ 1)
    (u v : ∀ i, Fin (d i)) :
    T u * T v = T (mixIndex u v S) * T (mixIndex v u S) := by
  have hc := rank_one_cross
    (fun row : ∀ i ∈ S, Fin (d i) => fun col : ∀ i ∈ Sᶜ, Fin (d i) =>
      flatCoeff d T S row col) h
    (fun i _ => u i) (fun i _ => v i) (fun i _ => u i) (fun i _ => v i)
  have he (w : ∀ i, Fin (d i)) :
      flatCoeff d T S (fun i _ => w i) (fun i _ => w i) = T w := by
    change T (fun i => if h : i ∈ S then w i else w i) = T w
    apply congrArg T
    funext i
    split_ifs <;> rfl
  rw [he, he] at hc
  exact hc

lemma singleton_rank_one_factor {N : ℕ} {d : Fin N → ℕ} (T : Coeffs d)
    (i : Fin N) (h : schmidtRank d T {i} ≤ 1)
    (u v : ∀ i, Fin (d i)) (hu : T u ≠ 0) :
    T v = (T (Function.update u i (v i)) / T u) * T (Function.update v i (u i)) := by
  classical
  have hc := schmidtRank_one_cross T {i} h u v
  have hm (u v : ∀ i, Fin (d i)) : mixIndex u v {i} = Function.update v i (u i) := by
    ext j
    by_cases hj : j = i
    · subst j; simp [mixIndex]
    · simp [mixIndex, hj]
  rw [hm, hm] at hc
  field_simp
  linear_combination hc

/-- Singleton ranks one force a tensor to be a product, with no restriction
on the local dimensions.  This is the rank-one case of Theorem 1.1. -/
theorem isProduct_of_singleton_rank_one {N : ℕ} {d : Fin N → ℕ}
    (hN : 0 < N) (T : Coeffs d)
    (h : ∀ i, schmidtRank d T {i} ≤ 1) (hT : T ≠ 0) : isProduct T := by
  classical
  have hu : ∃ u, T u ≠ 0 := by
    by_contra! hh
    exact hT (funext hh)
  obtain ⟨u, hu⟩ := hu
  let a : ∀ i, Fin (d i) → ℂ := fun i x => T (Function.update u i x) / T u
  have hprod (v : ∀ i, Fin (d i)) (S : Finset (Fin N)) :
      T (mixIndex v u S) = T u * ∏ i ∈ S, a i (v i) := by
    induction S using Finset.induction_on with
    | empty => simp only [mixIndex_empty, prod_empty, mul_one]
    | @insert i S hi ih =>
      have hf := singleton_rank_one_factor T i (h i) u (mixIndex v u (insert i S)) hu
      have he : Function.update (mixIndex v u (insert i S)) i (u i) = mixIndex v u S := by
        ext j
        by_cases hj : j = i
        · subst j; simp [mixIndex, hi]
        · simp [mixIndex, hj]
      rw [he, ih] at hf
      simpa [a, mixIndex, prod_insert hi, mul_assoc, mul_left_comm, mul_comm] using hf
  have hval (v : ∀ i, Fin (d i)) : T v = T u * ∏ i, a i (v i) := by
    simpa only [mixIndex_univ] using hprod v univ
  refine ⟨fun i x => if i = (⟨0, hN⟩ : Fin N) then T u * a i x else a i x, ?_⟩
  intro v
  rw [hval v]
  exact prod_scalar_absorb ⟨0, hN⟩ (fun i => a i (v i)) (T u)

theorem isProduct_of_allCutLe_one {N : ℕ} {d : Fin N → ℕ}
    (hN : 2 ≤ N) (T : Coeffs d) (h : allCutLe d T 1) (hT : T ≠ 0) : isProduct T := by
  apply isProduct_of_singleton_rank_one (by omega) T _ hT
  intro i
  apply h {i} (by simp)
  intro he
  have hc := congrArg Finset.card he
  simp only [card_singleton, card_univ, Fintype.card_fin] at hc
  omega

lemma allCutLe_of_maxSchmidtRank_le {N : ℕ} {d : Fin N → ℕ}
    (T : Coeffs d) (D : ℕ) (h : maxSchmidtRank d T ≤ D) : allCutLe d T D := by
  classical
  intro S he hu
  have hb : BddAbove (Set.range (fun S : Finset (Fin N) =>
      if S ≠ ∅ ∧ S ≠ univ then schmidtRank d T S else 0)) := (Set.finite_range _).bddAbove
  have hx : (if S ≠ ∅ ∧ S ≠ univ then schmidtRank d T S else 0) ≤ maxSchmidtRank d T :=
    le_csSup hb ⟨S, rfl⟩
  rw [if_pos ⟨he, hu⟩] at hx
  exact hx.trans h

theorem isProduct_of_maxSchmidtRank_one {N : ℕ} {d : Fin N → ℕ}
    (hN : 2 ≤ N) (T : Coeffs d) (hT : T ≠ 0) (h : maxSchmidtRank d T = 1) :
    isProduct T :=
  isProduct_of_allCutLe_one hN T (allCutLe_of_maxSchmidtRank_le T 1 h.le) hT

lemma schmidtRank_pos_of_ne_zero {N : ℕ} {d : Fin N → ℕ}
    (T : Coeffs d) (hT : T ≠ 0) (S : Finset (Fin N)) : 1 ≤ schmidtRank d T S := by
  classical
  obtain ⟨u, hu⟩ : ∃ u, T u ≠ 0 := by
    by_contra! h
    exact hT (funext h)
  let row : ∀ i ∈ S, Fin (d i) := fun i _ => u i
  let col : ∀ i ∈ Sᶜ, Fin (d i) := fun i _ => u i
  have he : flatCoeff d T S row col = T u := by
    change T (fun i => if h : i ∈ S then u i else u i) = T u
    congr 1
    ext i
    split_ifs <;> rfl
  have hn : (fun col => flatCoeff d T S row col) ≠ 0 := by
    intro h
    have hh := congrFun h col
    rw [he] at hh
    exact hu hh
  apply Submodule.one_le_finrank_iff.mpr
  intro hh
  have hr : (fun col => flatCoeff d T S row col) ∈ Submodule.span ℂ
      (Set.range (fun row : ∀ i ∈ S, Fin (d i) => fun col => flatCoeff d T S row col)) :=
    Submodule.subset_span ⟨row, rfl⟩
  rw [hh] at hr
  exact hn hr

lemma maxSchmidtRank_pos {N : ℕ} {d : Fin N → ℕ}
    (hN : 2 ≤ N) (T : Coeffs d) (hT : T ≠ 0) : 1 ≤ maxSchmidtRank d T := by
  classical
  let i : Fin N := ⟨0, by omega⟩
  have hu : ({i} : Finset (Fin N)) ≠ univ := by
    intro hh
    have hc := congrArg Finset.card hh
    simp only [card_singleton, card_univ, Fintype.card_fin] at hc
    omega
  have hm := allCutLe_of_maxSchmidtRank_le T (maxSchmidtRank d T) le_rfl {i} (by simp) hu
  exact (schmidtRank_pos_of_ne_zero T hT {i}).trans hm

lemma maxSchmidtRank_attained {N : ℕ} {d : Fin N → ℕ}
    (hN : 2 ≤ N) (T : Coeffs d) (hT : T ≠ 0) :
    ∃ S : Finset (Fin N), S ≠ ∅ ∧ S ≠ univ ∧ schmidtRank d T S = maxSchmidtRank d T := by
  classical
  let f : Finset (Fin N) → ℕ := fun S =>
    if S ≠ ∅ ∧ S ≠ univ then schmidtRank d T S else 0
  have hb : BddAbove (Set.range f) := (Set.finite_range f).bddAbove
  obtain ⟨S, hS⟩ := Nat.sSup_mem (Set.range_nonempty f) hb
  have hp := maxSchmidtRank_pos hN T hT
  have hcut : S ≠ ∅ ∧ S ≠ univ := by
    by_contra h
    have he : f S = 0 := by simp only [f, if_neg h]
    rw [he] at hS
    change 1 ≤ sSup (Set.range f) at hp
    omega
  refine ⟨S, hcut.1, hcut.2, ?_⟩
  simpa only [f, if_pos hcut] using hS

end UniformBorderRank
