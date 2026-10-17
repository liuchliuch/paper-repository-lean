import Paper08.ZeroFreeModel

/-! # Coordinate freezing and one-occurrence replacements -/
noncomputable section
open scoped BigOperators
namespace Paper08.ZeroFreeInduction
open Integral

variable {n m r c : ℕ} {q : ℝ}

/-- Occurrences that can depend on coordinate `j`. -/
def Model.incident (M : Model n m r c q) (j : Fin n) : Finset (Fin m) :=
  Finset.univ.filter fun e => j ∈ M.scope e

@[simp] lemma Model.mem_incident (M : Model n m r c q) (j : Fin n) (e : Fin m) :
    e ∈ M.incident j ↔ j ∈ M.scope e := by simp [Model.incident]

lemma Model.card_incident_le (M : Model n m r c q) (j : Fin n) :
    (M.incident j).card ≤ c := M.occurrence j

/-- The coordinate value chosen separately for each labelled occurrence. -/
def assignment (A : Finset (Fin m)) (a b : ℝ) (e : Fin m) : ℝ :=
  if e ∈ A then b else a

lemma assignment_mem (A : Finset (Fin m)) {a b : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) (e : Fin m) :
    assignment A a b e ∈ Set.Icc (0 : ℝ) 1 := by
  unfold assignment
  split_ifs <;> assumption

/-- Freeze the coordinate at `b` for occurrences in `A`, and at `a` for all
 remaining occurrences. -/
def Model.freezeSet (M : Model n m r c q) (j : Fin n) (A : Finset (Fin m))
    {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    Model n m r c q := M.freeze j (assignment A a b) (assignment_mem A ha hb)

@[simp] lemma Model.freezeSet_scope (M : Model n m r c q) (j : Fin n)
    (A : Finset (Fin m)) {a b : ℝ} (ha) (hb) (e : Fin m) :
    (M.freezeSet j A (a := a) (b := b) ha hb).scope e = (M.scope e).erase j := rfl

@[simp] lemma Model.freezeSet_potential (M : Model n m r c q) (j : Fin n)
    (A : Finset (Fin m)) {a b : ℝ} (ha) (hb) (e : Fin m) (x : Fin n → ℝ) :
    (M.freezeSet j A (a := a) (b := b) ha hb).potential e x =
      M.potential e (Function.update x j (assignment A a b e)) := rfl

@[simp] lemma Model.freezeSet_empty_total (M : Model n m r c q) (j : Fin n)
    {a b : ℝ} (ha) (hb) (x : Fin n → ℝ) :
    (M.freezeSet j ∅ (a := a) (b := b) ha hb).total x = M.total (Function.update x j a) := by
  simp [Model.total, assignment]

lemma Model.freezeSet_incident_total (M : Model n m r c q) (j : Fin n)
    {a b : ℝ} (ha) (hb) {x : Fin n → ℝ} (hx : x ∈ cube n) :
    (M.freezeSet j (M.incident j) (a := a) (b := b) ha hb).total x =
      M.total (Function.update x j b) := by
  classical
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : e ∈ M.incident j
  · simp [assignment, he]
  · simp only [Model.freezeSet_potential, assignment, if_neg he]
    apply M.depends e _ _ (update_mem_cube hx j ha) (update_mem_cube hx j hb)
    intro v hv
    have hvj : v ≠ j := by
      intro hvj
      subst v
      exact he ((M.mem_incident j e).mpr hv)
    simp [Function.update_of_ne hvj]

/-- Inserting one occurrence changes no other frozen potential. -/
lemma Model.freezeSet_insert_other (M : Model n m r c q) (j : Fin n)
    (A : Finset (Fin m)) (e i : Fin m) (hi : i ≠ e)
    {a b : ℝ} (ha) (hb) (x : Fin n → ℝ) :
    (M.freezeSet j (insert e A) (a := a) (b := b) ha hb).potential i x =
      (M.freezeSet j A (a := a) (b := b) ha hb).potential i x := by
  simp [assignment, Finset.mem_insert, hi]

lemma Model.freezeSet_insert_self (M : Model n m r c q) (j : Fin n)
    (A : Finset (Fin m)) (e : Fin m) (he : e ∉ A)
    {a b : ℝ} (ha) (hb) (x : Fin n → ℝ) :
    (M.freezeSet j (insert e A) (a := a) (b := b) ha hb).potential e x -
      (M.freezeSet j A (a := a) (b := b) ha hb).potential e x =
      M.potential e (Function.update x j b) - M.potential e (Function.update x j a) := by
  simp [assignment, he]

lemma Model.freezeSet_total_sub (M : Model n m r c q) (j : Fin n)
    (A : Finset (Fin m)) (e : Fin m) (he : e ∉ A)
    {a b : ℝ} (ha) (hb) (x : Fin n → ℝ) :
    (M.freezeSet j (insert e A) (a := a) (b := b) ha hb).total x -
      (M.freezeSet j A (a := a) (b := b) ha hb).total x =
      M.potential e (Function.update x j b) - M.potential e (Function.update x j a) := by
  rw [Model.total_sub_eq_single _ _ e
    (fun i hi y => M.freezeSet_insert_other j A e i hi ha hb y)]
  exact M.freezeSet_insert_self j A e he ha hb x

/-- The changed potential loses the coordinate that has just been frozen. -/
lemma Model.frozen_arity_le_sub_one (M : Model n m r c q) (j : Fin n)
    (e : Fin m) (he : e ∈ M.incident j) : ((M.scope e).erase j).card ≤ r - 1 := by
  rw [Finset.card_erase_of_mem ((M.mem_incident j e).mp he)]
  have h := M.arity e
  omega

/-- The real difference used along the interpolation path. -/
def Model.delta (M : Model n m r c q) (j : Fin n) (a b : ℝ) (e : Fin m)
    (x : Fin n → ℝ) : ℝ :=
  M.potential e (Function.update x j b) - M.potential e (Function.update x j a)

lemma Model.continuous_delta (M : Model n m r c q) (j : Fin n)
    {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) (e : Fin m) :
    ContinuousOn (M.delta j a b e) (cube n) :=
  ((M.continuous e).comp (continuous_update j b).continuousOn
    (fun _ hx => update_mem_cube hx j hb)).sub
  ((M.continuous e).comp (continuous_update j a).continuousOn
    (fun _ hx => update_mem_cube hx j ha))

lemma Model.abs_delta_le (M : Model n m r c q) (j : Fin n)
    {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) (e : Fin m)
    {x : Fin n → ℝ} (hx : x ∈ cube n) : |M.delta j a b e x| ≤ q :=
  potential_sub_abs_le M e (update_mem_cube hx j hb) (update_mem_cube hx j ha)

lemma Model.delta_depends (M : Model n m r c q) (j : Fin n)
    {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) (e : Fin m)
    {x y : Fin n → ℝ} (hx : x ∈ cube n) (hy : y ∈ cube n)
    (hxy : ∀ v ∈ (M.scope e).erase j, x v = y v) :
    M.delta j a b e x = M.delta j a b e y := by
  have heq : ∀ d ∈ Set.Icc (0 : ℝ) 1,
      M.potential e (Function.update x j d) = M.potential e (Function.update y j d) := by
    intro d hd
    apply M.depends e _ _ (update_mem_cube hx j hd) (update_mem_cube hy j hd)
    intro v hv
    by_cases hvj : v = j
    · subst v; simp
    · simpa [Function.update_of_ne hvj] using hxy v (Finset.mem_erase.mpr ⟨hvj, hv⟩)
  exact congrArg₂ (· - ·) (heq b hb) (heq a ha)

end Paper08.ZeroFreeInduction
