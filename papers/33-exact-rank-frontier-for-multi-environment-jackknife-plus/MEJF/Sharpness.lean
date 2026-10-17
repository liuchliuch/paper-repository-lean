import MEJF.Incidence
import MEJF.ExtremalGraph
import MEJF.PredictionTable
import MEJF.PredictionModel
import Mathlib.Data.Fin.SuccPred
import Mathlib.Logic.Equiv.Fin.Basic

/-! The actual graph-and-incidence sharpness construction of Section 5. -/
namespace MEJF.Sharpness
open Finset Incidence
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Extend the actual finite matrix by zero rows. -/
def extendRows {F n : ℕ} {C : Type*} (B : Fin F → C → Prop) (j : Fin n) (c : C) : Bool :=
  if hj : j.val < F then decide (B ⟨j.val, hj⟩ c) else false

lemma extendRows_active {F n : ℕ} {C : Type*} (B : Fin F → C → Prop)
    (j : Fin n) (hj : j.val < F) (c : C) :
    extendRows B j c = decide (B ⟨j.val, hj⟩ c) := by simp [extendRows, hj]

lemma extendRows_inactive {F n : ℕ} {C : Type*} (B : Fin F → C → Prop)
    (j : Fin n) (hj : ¬ j.val < F) (c : C) : extendRows B j c = false := by
  simp [extendRows, hj]

/-- Zero extension preserves the exact column degree. -/
lemma extendRows_column {F n : ℕ} {C : Type*} (hFn : F ≤ n)
    (B : Fin F → C → Prop) (c : C) :
    (univ.filter fun j : Fin n => extendRows B j c = true).card = colSum B c := by
  classical
  have hset : (univ.filter fun j : Fin n => extendRows B j c = true) =
      (univ.filter fun j : Fin F => B j c).image (Fin.castLE hFn) := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro hj
      have hactive : j.val < F := by
        by_contra h
        simp [extendRows, h] at hj
      have hb : B ⟨j.val, hactive⟩ c := by simpa [extendRows, hactive] using hj
      exact ⟨⟨j.val, hactive⟩, hb, Fin.ext rfl⟩
    · rintro ⟨r, hr, rfl⟩
      simp [extendRows, r.is_lt, hr]
  rw [hset, card_image_of_injective _ (Fin.castLE_injective hFn)]
  simp [colSum]

/-- The canonical enumeration of every label other than `u`. -/
def otherEquiv {m : ℕ} (u : Fin (m+1)) : Fin m ≃ {v : Fin (m+1) // v ≠ u} :=
  Equiv.ofBijective (fun k => ⟨u.succAbove k, Fin.succAbove_ne u k⟩) (by
    constructor
    · intro i j hij
      exact Fin.succAbove_right_injective (congrArg Subtype.val hij)
    · intro v
      obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq v.property
      exact ⟨k, Subtype.ext hk⟩)

@[simp] lemma otherEquiv_apply {m : ℕ} (u : Fin (m+1)) (k : Fin m) :
    (otherEquiv u k).val = u.succAbove k := rfl

@[simp] lemma otherEquiv_inverse {m : ℕ} (u : Fin (m+1)) (k : Fin m) :
    (otherEquiv u).symm ⟨u.succAbove k, Fin.succAbove_ne u k⟩ = k :=
  (otherEquiv u).symm_apply_apply k

/-- Turn each genuine `F × m` matrix into the paper's type-indexed Boolean
array, with zero diagonal and zero rows after the first `F` coordinates. -/
def typeBits {m F n : ℕ} (A : Fin (m+1) → Fin F → Fin m → Prop)
    (u : Fin (m+1)) (j : Fin n) (v : Fin (m+1)) : Bool :=
  if hv : v ≠ u then extendRows (A u) j ((otherEquiv u).symm ⟨v, hv⟩) else false

@[simp] lemma typeBits_other {m F n : ℕ} (A : Fin (m+1) → Fin F → Fin m → Prop)
    (u : Fin (m+1)) (j : Fin n) (k : Fin m) :
    typeBits A u j (u.succAbove k) = extendRows (A u) j k := by
  simp [typeBits]

@[simp] lemma typeBits_self {m F n : ℕ} (A : Fin (m+1) → Fin F → Fin m → Prop)
    (u : Fin (m+1)) (j : Fin n) : typeBits A u j u = false := by simp [typeBits]

lemma typeBits_column {m F n : ℕ} (hFn : F ≤ n)
    (A : Fin (m+1) → Fin F → Fin m → Prop) (u : Fin (m+1)) (k : Fin m) :
    PredictionTable.markedCount (typeBits (n := n) A) u (u.succAbove k) = colSum (A u) k := by
  simp only [PredictionTable.markedCount, typeBits_other]
  exact extendRows_column hFn (A u) k

lemma marked_card_eq_degree {m : ℕ} (R : Fin (m+1) → Fin (m+1) → Prop)
    (hasym : ∀ u v, R u v → ¬ R v u) (u : Fin (m+1)) :
    (univ.filter fun k : Fin m => R u (u.succAbove k)).card = ExtremalGraph.outdegree R u := by
  classical
  unfold ExtremalGraph.outdegree
  apply Finset.card_bij (fun k _ => u.succAbove k)
  · intro k hk
    simpa only [mem_filter, mem_univ, true_and] using hk
  · intro k hk l hl hkl
    exact Fin.succAbove_right_injective hkl
  · intro v hv
    have hvu : v ≠ u := by
      intro h; subst v
      exact hasym u u (mem_filter.mp hv).2 (mem_filter.mp hv).2
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hvu
    exact ⟨k, by simpa only [mem_filter, mem_univ, true_and] using hv, rfl⟩

/-- Actual extremal graph and actual matrices, chosen simultaneously for every
block type. Unselected types receive the identically zero matrix. -/
theorem exists_graph_matrices (m F t ell : ℕ) (hm : 1 ≤ m) (ht : 1 ≤ t)
    (he : 1 ≤ ell ∧ ell ≤ m) :
    let w := if F < t then 0 else threshold F m (m+1-ell) t
    ∃ (R : Fin (m+1) → Fin (m+1) → Prop) (S : Finset (Fin (m+1)))
      (A : Fin (m+1) → Fin F → Fin m → Prop),
      (∀ u v, R u v → ¬ R v u) ∧
      S.card = min (m+1) (2*((m+1)-w)-1) ∧
      (∀ u ∈ S, ∀ r, rowSum (A u) r = m+1-ell) ∧
      (∀ u k, R u (u.succAbove k) → t ≤ colSum (A u) k) ∧
      (∀ u k, ¬ R u (u.succAbove k) → colSum (A u) k ≤ t-1) ∧
      (∀ u ∉ S, ∀ r k, ¬ A u r k) := by
  classical
  dsimp only
  let w := if F < t then 0 else threshold F m (m+1-ell) t
  have hw : w ≤ m := by
    dsimp [w]
    split_ifs with h
    · omega
    · exact (threshold_le_row F m (m+1-ell) t ht (by omega) (by omega)).trans (by omega)
  obtain ⟨R, S, hasym, hScard, hdeg, hout⟩ :=
    ExtremalGraph.exists_extremal_oriented_graph (m+1) w (by omega) (by omega)
  have hno : ∀ u ∉ S, ∀ v, ¬ R u v := by
    intro u hu v hv
    have hpos : 0 < ExtremalGraph.outdegree R u := by
      exact card_pos.mpr ⟨v, by simp [hv]⟩
    rw [hout u hu] at hpos
    omega
  have hmats : ∀ u : Fin (m+1), ∃ M : Fin F → Fin m → Prop,
      (u ∈ S → (∀ r, rowSum M r = m+1-ell) ∧
        (∀ k, R u (u.succAbove k) → t ≤ colSum M k) ∧
        (∀ k, ¬ R u (u.succAbove k) → colSum M k ≤ t-1)) ∧
      (u ∉ S → ∀ r k, ¬ M r k) := by
    intro u
    by_cases hu : u ∈ S
    · let marked : Finset (Fin m) := univ.filter fun k => R u (u.succAbove k)
      have hmarked : marked.card = if F < t then 0 else threshold F (Fintype.card (Fin m)) (m+1-ell) t := by
        simpa [marked, w] using (marked_card_eq_degree R hasym u).trans (hdeg u hu)
      obtain ⟨M, hrow, hmark, hunmark⟩ :=
        realize_frontier F (m+1-ell) t marked ht (by simp; omega) hmarked
      refine ⟨M, fun _ => ⟨hrow, ?_, ?_⟩, by simp [hu]⟩
      · intro k hk; exact hmark k (by simp [marked, hk])
      · intro k hk; exact hunmark k (by simp [marked, hk])
    · exact ⟨fun _ _ => False, by simp [hu], by simp⟩
  choose A hA using hmats
  refine ⟨R, S, A, hasym, hScard, ?_, ?_, ?_, ?_⟩
  · intro u hu; exact ((hA u).1 hu).1
  · intro u k hk
    by_cases hu : u ∈ S
    · exact ((hA u).1 hu).2.1 k hk
    · exact False.elim (hno u hu _ hk)
  · intro u k hk
    by_cases hu : u ∈ S
    · exact ((hA u).1 hu).2.2 k hk
    · have hz : colSum (A u) k = 0 := by
        simp [colSum, (hA u).2 hu]
      simp [hz]
  · intro u hu; exact (hA u).2 hu

/-- Boolean row count needed for the actual outer lower order statistic. -/
lemma typeBits_false_count {m F n ell : ℕ}
    (A : Fin (m+1) → Fin F → Fin m → Prop) (u : Fin (m+1)) (j : Fin n)
    (hj : j.val < F) (he : 1 ≤ ell ∧ ell ≤ m)
    (hrow : rowSum (A u) ⟨j.val, hj⟩ = m+1-ell) :
    (univ.filter fun k : Fin m => typeBits A u j (u.succAbove k) = false).card = ell-1 := by
  have htrue : (univ.filter fun k : Fin m => typeBits A u j (u.succAbove k) = true).card = m+1-ell := by
    simpa [typeBits_other, extendRows, hj, rowSum] using hrow
  have hpart := filter_card_add_filter_neg_card_eq_card (s := (univ : Finset (Fin m)))
    (p := fun k => typeBits A u j (u.succAbove k) = true)
  simp only [Bool.not_eq_true, card_univ, Fintype.card_fin] at hpart
  omega

/-- The constructed Boolean array is zero away from the selected coordinates. -/
lemma typeBits_zero_row {m F n : ℕ} (A : Fin (m+1) → Fin F → Fin m → Prop)
    (u : Fin (m+1)) (j : Fin n) (hj : ¬ j.val < F) (k : Fin m) :
    typeBits A u j (u.succAbove k) = false := by simp [extendRows, hj]

/-- Choose the graph, matrices, and actual type-indexed Boolean incidence table
with all hypotheses of the fitted prediction-table sharpness theorem proved. -/
theorem exists_sharpness_array (m n F t ell : ℕ) (hm : 1 ≤ m) (hFn : F ≤ n)
    (ht : 1 ≤ t) (he : 1 ≤ ell ∧ ell ≤ m) :
    let w := if F < t then 0 else threshold F m (m+1-ell) t
    ∃ (R : Fin (m+1) → Fin (m+1) → Prop) (S : Finset (Fin (m+1)))
      (B : Fin (m+1) → Fin n → Fin (m+1) → Bool),
      (∀ u v, R u v → ¬ R v u) ∧
      S.card = min (m+1) (2*((m+1)-w)-1) ∧
      (∀ u v, R u v → t ≤ PredictionTable.markedCount B u v) ∧
      (∀ u v, ¬ R u v → PredictionTable.markedCount B u v < t) ∧
      (∀ u ∈ S, ∀ j : Fin n, j.val < F →
        (univ.filter fun k : Fin m => B u j (u.succAbove k) = false).card = ell-1) ∧
      (∀ u j, (u ∉ S ∨ F ≤ j.val) → ∀ k : Fin m, B u j (u.succAbove k) = false) := by
  classical
  obtain ⟨R, S, A, hasym, hScard, hrow, hmark, hunmark, hzero⟩ :=
    exists_graph_matrices m F t ell hm ht he
  refine ⟨R, S, typeBits A, hasym, hScard, ?_, ?_, ?_, ?_⟩
  · intro u v huv
    have hvu : v ≠ u := by
      intro h; subst v; exact hasym u u huv huv
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hvu
    rw [typeBits_column hFn]
    exact hmark u k huv
  · intro u v huv
    by_cases hvu : v = u
    · subst v
      simp [PredictionTable.markedCount]
      omega
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hvu
      rw [typeBits_column hFn]
      have := hunmark u k huv
      omega
  · intro u hu j hj
    exact typeBits_false_count A u j hj he (hrow u hu _)
  · intro u j hor k
    rcases hor with hu | hj
    · by_cases hj : j.val < F
      · simp [typeBits_other, extendRows, hj, hzero u hu]
      · exact typeBits_zero_row A u j hj k
    · exact typeBits_zero_row A u j (by omega) k

/-- Exactly the first `F` coordinates are designated for failure. -/
def firstRows (F n : ℕ) : Finset (Fin n) := univ.filter fun j => j.val < F

lemma firstRows_card {F n : ℕ} (hFn : F ≤ n) : (firstRows F n).card = F := by
  have hset : firstRows F n = (univ : Finset (Fin F)).image (Fin.castLE hFn) := by
    ext j
    simp only [firstRows, mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro hj; exact ⟨⟨j.val, hj⟩, Fin.ext rfl⟩
    · rintro ⟨r, rfl⟩; exact r.is_lt
  rw [hset, card_image_of_injective _ (Fin.castLE_injective hFn)]
  simp

/-- The extremal graph size in the paper's rank notation. -/
lemma graph_size_formula (m F t ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) :
    let w := if F < t then 0 else threshold F m (m+1-ell) t
    min (m+1) (2*((m+1)-w)-1) =
      if F < t then m+1 else min (m+1) (2*min m (F*(ell-1)/(F-t+1))+1) := by
  dsimp only
  by_cases hFt : F < t
  · simp only [if_pos hFt, Nat.sub_zero]
    omega
  · simp only [if_neg hFt, threshold]
    have hmd : m-(m+1-ell) = ell-1 := by omega
    rw [hmd]
    have hmin : min m (F*(ell-1)/(F-t+1)) ≤ m := min_le_left _ _
    congr 1
    omega

/-- Section 5's fully fitted deterministic sharpness model. This constructs a
jointly measurable multiset learner on any ambient space admitting the finite
covariate embedding, and proves its exact label failure set. -/
theorem exists_exact_failure_model {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (m n F t ell : ℕ) (hm : 1 ≤ m) (hF : 1 ≤ F) (hFn : F ≤ n)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m)
    (emb : Fin (m+1) × Fin n → X) (hinj : Function.Injective emb) :
    ∃ (R : Fin (m+1) → Fin (m+1) → Prop)
      (B : Fin (m+1) → Fin n → Fin (m+1) → Bool) (S : Finset (Fin (m+1))),
      S.card = (if F < t then m+1 else min (m+1) (2*min m (F*(ell-1)/(F-t+1))+1)) ∧
      ∀ u : Fin (m+1),
        Setup.failure (PredictionTable.tableLearner (PredictionTable.incidenceTable R B) emb)
          (PredictionTable.modelData emb) u F t ell ht he ↔ u ∈ S := by
  classical
  obtain ⟨R, S, B, hasym, hScard, hmark, hunmark, hrows, hzero⟩ :=
    exists_sharpness_array m n F t ell hm hFn ht.1 he
  refine ⟨R, B, S, hScard.trans (graph_size_formula m F t ell he), ?_⟩
  intro u
  by_cases hu : u ∈ S
  · have hmiss := PredictionTable.model_failure_set R (fun {u v} => hasym u v) B emb hinj
      t ell ht he hmark hunmark u (firstRows F n)
      (fun j hj => hrows u hu j (by simpa [firstRows] using hj))
      (fun j hj => hzero u j (Or.inr (by simpa [firstRows] using hj)))
    simp only [Setup.failure, hmiss, firstRows_card hFn, le_refl, hu]
  · have hmiss := PredictionTable.model_failure_set R (fun {u v} => hasym u v) B emb hinj
      t ell ht he hmark hunmark u ∅ (by simp)
      (fun j _ => hzero u j (Or.inl hu))
    constructor
    · intro hf
      unfold Setup.failure at hf
      rw [hmiss] at hf
      simp only [card_empty] at hf
      omega
    · intro hus
      exact False.elim (hu hus)

/-- The exact count is attained by an actual admissible learner and one
complete finite array of zero-response blocks. -/
theorem exists_exact_failure_count_model {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (m n F t ell : ℕ) (hm : 1 ≤ m) (hF : 1 ≤ F) (hFn : F ≤ n)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m)
    (emb : Fin (m+1) × Fin n → X) (hinj : Function.Injective emb) :
    ∃ (A : Setup.Learner X n) (Z : Fin (m+1) → Setup.Block X n),
      (univ.filter fun u => Setup.failure A Z u F t ell ht he).card =
        if F < t then m+1 else min (m+1) (2*min m (F*(ell-1)/(F-t+1))+1) := by
  obtain ⟨R, B, S, hScard, hfail⟩ := exists_exact_failure_model m n F t ell hm hF hFn ht he emb hinj
  refine ⟨PredictionTable.tableLearner (PredictionTable.incidenceTable R B) emb,
    PredictionTable.modelData emb, ?_⟩
  have hset : (univ.filter fun u => Setup.failure
      (PredictionTable.tableLearner (PredictionTable.incidenceTable R B) emb)
        (PredictionTable.modelData emb) u F t ell ht he) = S := by
    ext u
    simpa using hfail u
  rw [hset]
  exact hScard

end
end MEJF.Sharpness
