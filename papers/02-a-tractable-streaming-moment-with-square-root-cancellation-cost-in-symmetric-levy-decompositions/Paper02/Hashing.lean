import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Logic.Equiv.Prod

/-! # Explicit pairwise independent binary affine hashes

A seed is precisely a binary matrix and a binary offset.  The bijections below
prove its uniform marginal and pair distributions by actual finite sums, rather
than assuming independence as a field of an algorithm certificate.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

namespace Paper02.Hashing

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F]

abbrev RowSeed (ι F : Type*) := (ι → F) × F

def rowHash (u : ι → F) (s : RowSeed ι F) : F :=
  ∑ i, s.1 i * u i + s.2

/-- For each fixed matrix, the offset translates the output bijectively. -/
def rowSingleEquiv (u : ι → F) : RowSeed ι F ≃ (ι → F) × F where
  toFun s := (s.1, rowHash u s)
  invFun s := (s.1, s.2 - ∑ i, s.1 i * u i)
  left_inv s := by simp [rowHash]
  right_inv s := by simp [rowHash]

/-- A nonsingular two-by-two affine map. -/
def affinePairEquiv (u v su sv : F) (h : v - u ≠ 0) : F × F ≃ F × F where
  toFun s := (s.1 * u + s.2 + su, s.1 * v + s.2 + sv)
  invFun t :=
    let a := ((t.2 - sv) - (t.1 - su)) / (v - u)
    (a, t.1 - su - a * u)
  left_inv s := by
    dsimp
    apply Prod.ext <;> field_simp <;> ring
  right_inv t := by
    dsimp
    apply Prod.ext <;> field_simp <;> ring

/-- Exposing one matrix entry and two hash outputs is a bijection whenever the
input vectors differ at that entry. -/
def rowPairEquiv (u v : ι → F) (c : ι) (hc : u c ≠ v c) :
    RowSeed ι F ≃ ({i : ι // i ≠ c} → F) × F × F :=
  let rest (a : {i : ι // i ≠ c} → F) (w : ι → F) := ∑ i, a i * w i
  let pair (a : {i : ι // i ≠ c} → F) :=
    affinePairEquiv (u c) (v c) (rest a u) (rest a v) (sub_ne_zero.mpr hc.symm)
  { toFun := fun s =>
      let a := fun i : {i : ι // i ≠ c} => s.1 i
      (a, pair a (s.1 c, s.2))
    invFun := fun s =>
      let ab := (pair s.1).symm s.2
      ((Equiv.funSplitAt c F).symm (ab.1, s.1), ab.2)
    left_inv := by
      intro s
      dsimp only
      simp only [Equiv.symm_apply_apply]
      apply Prod.ext
      · exact (Equiv.funSplitAt c F).symm_apply_apply s.1
      · rfl
    right_inv := by
      intro s
      dsimp only
      have hrest : (fun i : {i : ι // i ≠ c} =>
          (Equiv.funSplitAt c F).symm (((pair s.1).symm s.2).1, s.1) i) = s.1 := by
        funext i
        simp [Equiv.funSplitAt, Equiv.piSplitAt, i.property]
      have hfirst : (Equiv.funSplitAt c F).symm
          (((pair s.1).symm s.2).1, s.1) c = ((pair s.1).symm s.2).1 := by
        simp [Equiv.funSplitAt, Equiv.piSplitAt]
      simp only [hrest, hfirst]
      exact congrArg (fun x => (s.1, x)) ((pair s.1).apply_symm_apply s.2) }

lemma rowPairEquiv_outputs (u v : ι → F) (c : ι) (hc : u c ≠ v c)
    (s : RowSeed ι F) :
    (rowPairEquiv u v c hc s).2 = (rowHash u s, rowHash v s) := by
  apply Prod.ext <;> dsimp [rowPairEquiv, affinePairEquiv, rowHash]
  · rw [Fintype.sum_eq_add_sum_subtype_ne (fun i => s.1 i * u i) c]
    ring
  · rw [Fintype.sum_eq_add_sum_subtype_ne (fun i => s.1 i * v i) c]
    ring

/-- A matrix with `J` rows, each with its own one-bit offset. -/
abbrev Seed (J ℓ : ℕ) := Fin J → RowSeed (Fin ℓ) (ZMod 2)

def hash {J ℓ : ℕ} (u : Fin ℓ → ZMod 2) (s : Seed J ℓ) : Fin J → ZMod 2 :=
  fun r => rowHash u (s r)

/-- Exactly `J(ℓ+1)` random bits, including the offsets. -/
lemma card_seed (J ℓ : ℕ) : Fintype.card (Seed J ℓ) = 2 ^ (J * (ℓ + 1)) := by
  simp only [Seed, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, ZMod.card]
  rw [← pow_succ, ← pow_mul]
  congr 1
  exact Nat.mul_comm _ _

/-- A uniform output vector, independent of all matrix entries. -/
def singleEquiv (J ℓ : ℕ) (u : Fin ℓ → ZMod 2) :
    Seed J ℓ ≃ (Fin J → Fin ℓ → ZMod 2) × (Fin J → ZMod 2) where
  toFun s := (fun r => (rowSingleEquiv u (s r)).1,
    fun r => (rowSingleEquiv u (s r)).2)
  invFun t := fun r => (rowSingleEquiv u).symm (t.1 r, t.2 r)
  left_inv s := by
    funext r
    exact (rowSingleEquiv u).symm_apply_apply (s r)
  right_inv t := by
    apply Prod.ext <;> funext r
    · exact congrArg Prod.fst ((rowSingleEquiv u).apply_symm_apply (t.1 r, t.2 r))
    · exact congrArg Prod.snd ((rowSingleEquiv u).apply_symm_apply (t.1 r, t.2 r))

lemma singleEquiv_output (J ℓ : ℕ) (u : Fin ℓ → ZMod 2) (s : Seed J ℓ) :
    (singleEquiv J ℓ u s).2 = hash u s := rfl

/-- Two independent uniform output vectors, with the other matrix entries
carried as a residual factor in the explicit bijection. -/
def pairEquiv (J ℓ : ℕ) (u v : Fin ℓ → ZMod 2) (c : Fin ℓ)
    (hc : u c ≠ v c) :
    Seed J ℓ ≃ (Fin J → {i : Fin ℓ // i ≠ c} → ZMod 2) ×
      (Fin J → ZMod 2) × (Fin J → ZMod 2) where
  toFun s :=
    (fun r => (rowPairEquiv u v c hc (s r)).1,
      (fun r => (rowPairEquiv u v c hc (s r)).2.1),
      (fun r => (rowPairEquiv u v c hc (s r)).2.2))
  invFun t := fun r => (rowPairEquiv u v c hc).symm (t.1 r, t.2.1 r, t.2.2 r)
  left_inv s := by
    funext r
    exact (rowPairEquiv u v c hc).symm_apply_apply (s r)
  right_inv t := by
    apply Prod.ext
    · funext r
      exact congrArg Prod.fst ((rowPairEquiv u v c hc).apply_symm_apply
        (t.1 r, t.2.1 r, t.2.2 r))
    · apply Prod.ext <;> funext r
      · exact congrArg (fun x => x.2.1) ((rowPairEquiv u v c hc).apply_symm_apply
          (t.1 r, t.2.1 r, t.2.2 r))
      · exact congrArg (fun x => x.2.2) ((rowPairEquiv u v c hc).apply_symm_apply
          (t.1 r, t.2.1 r, t.2.2 r))

lemma pairEquiv_outputs (J ℓ : ℕ) (u v : Fin ℓ → ZMod 2) (c : Fin ℓ)
    (hc : u c ≠ v c) (s : Seed J ℓ) :
    (pairEquiv J ℓ u v c hc s).2 = (hash u s, hash v s) := by
  apply Prod.ext <;> funext r
  · exact congrArg Prod.fst (rowPairEquiv_outputs u v c hc (s r))
  · exact congrArg Prod.snd (rowPairEquiv_outputs u v c hc (s r))

/-- The actual binary representation of an index. -/
def binaryVector (ℓ n : ℕ) : Fin ℓ → ZMod 2 :=
  fun i => if n.testBit i.val then 1 else 0

lemma binaryVector_injective (ℓ : ℕ) :
    Function.Injective (fun n : Fin (2 ^ ℓ) => binaryVector ℓ n.val) := by
  intro x y h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < ℓ
  · have hh := congrFun h ⟨i, hi⟩
    dsimp [binaryVector] at hh
    cases hx : x.val.testBit i <;> cases hy : y.val.testBit i <;> simp_all
  · have hpow : 2 ^ ℓ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le x.isLt hpow),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le y.isLt hpow)]

/-- A sampled vector has its first `j` hash bits equal to zero. -/
def PrefixZero {J : ℕ} (j : ℕ) (v : Fin J → ZMod 2) : Prop :=
  ∀ r, r.val < j → v r = 0

def prefixEquiv {J j : ℕ} (hj : j ≤ J) :
    {v : Fin J → ZMod 2 // PrefixZero j v} ≃ (Fin (J - j) → ZMod 2) where
  toFun v r := v.1 ⟨j + r.val, by omega⟩
  invFun v := ⟨fun r => if h : r.val < j then 0 else v ⟨r.val - j, by omega⟩,
    by intro r hr; simp [hr]⟩
  left_inv v := by
    apply Subtype.ext
    funext r
    dsimp only
    split_ifs with hr
    · exact (v.2 r hr).symm
    · apply congrArg v.1
      apply Fin.ext
      dsimp only
      omega
  right_inv v := by
    funext r
    simp only
    rw [dif_neg (by omega)]
    apply congrArg v
    apply Fin.ext
    dsimp only
    omega

lemma card_prefixZero {J j : ℕ} (hj : j ≤ J) :
    Fintype.card {v : Fin J → ZMod 2 // PrefixZero j v} = 2 ^ (J - j) := by
  rw [Fintype.card_congr (prefixEquiv hj)]
  simp [Fintype.card_fun, ZMod.card]

/-- Uniform marginal sums, with every unused seed counted explicitly. -/
lemma hash_sum (J ℓ : ℕ) (u : Fin ℓ → ZMod 2)
    (g : (Fin J → ZMod 2) → ℝ) :
    (∑ s : Seed J ℓ, g (hash u s)) =
      Fintype.card (Fin J → Fin ℓ → ZMod 2) * ∑ v, g v := by
  let e := singleEquiv J ℓ u
  calc
    _ = ∑ s : Seed J ℓ, (fun t => g t.2) (e s) := rfl
    _ = ∑ t : (Fin J → Fin ℓ → ZMod 2) × (Fin J → ZMod 2), g t.2 :=
      e.sum_comp (fun t => g t.2)
    _ = _ := by simp [Fintype.sum_prod_type]

/-- Uniform pair sums prove independence as a consequence of the seed, rather
than a hypothesis of the estimator. -/
lemma hash_pair_sum (J ℓ : ℕ) (u v : Fin ℓ → ZMod 2) (c : Fin ℓ)
    (hc : u c ≠ v c) (g : (Fin J → ZMod 2) → (Fin J → ZMod 2) → ℝ) :
    (∑ s : Seed J ℓ, g (hash u s) (hash v s)) =
      Fintype.card (Fin J → {i : Fin ℓ // i ≠ c} → ZMod 2) *
        ∑ x, ∑ y, g x y := by
  let e := pairEquiv J ℓ u v c hc
  calc
    _ = ∑ s : Seed J ℓ, (fun t => g t.2.1 t.2.2) (e s) := by
      apply Finset.sum_congr rfl
      intro s _
      change g (hash u s) (hash v s) = g (e s).2.1 (e s).2.2
      rw [show (e s).2 = (hash u s, hash v s) from
        pairEquiv_outputs J ℓ u v c hc s]
    _ = ∑ t : (Fin J → {i : Fin ℓ // i ≠ c} → ZMod 2) ×
        (Fin J → ZMod 2) × (Fin J → ZMod 2), g t.2.1 t.2.2 :=
      e.sum_comp (fun t => g t.2.1 t.2.2)
    _ = _ := by simp [Fintype.sum_prod_type]

lemma prefixZero_indicator_sum {J j : ℕ} (hj : j ≤ J) :
    (∑ v : Fin J → ZMod 2, if PrefixZero j v then (1 : ℝ) else 0) =
      (2 : ℝ) ^ (J - j) := by
  have hc := card_prefixZero hj
  rw [Fintype.card_subtype, Finset.card_filter] at hc
  exact_mod_cast hc

lemma prefixZero_pair_indicator_sum {J j : ℕ} (hj : j ≤ J) :
    (∑ x : Fin J → ZMod 2, ∑ y : Fin J → ZMod 2,
      (if PrefixZero j x then (1 : ℝ) else 0) *
        (if PrefixZero j y then (1 : ℝ) else 0)) =
      ((2 : ℝ) ^ (J - j)) ^ 2 := by
  rw [← Finset.sum_mul_sum]
  rw [prefixZero_indicator_sum hj]
  ring

/-- Integer coordinate labels fit in the claimed number of binary columns. -/
lemma coordinate_binary_injective {d ℓ : ℕ} (hd : d ≤ 2 ^ ℓ) :
    Function.Injective (fun i : Fin d => binaryVector ℓ i.val) := by
  intro i k h
  have he := binaryVector_injective ℓ
    (a₁ := ⟨i.val, lt_of_lt_of_le i.isLt hd⟩)
    (a₂ := ⟨k.val, lt_of_lt_of_le k.isLt hd⟩) h
  apply Fin.ext
  exact congrArg (fun x : Fin (2 ^ ℓ) => x.val) he

end Paper02.Hashing
