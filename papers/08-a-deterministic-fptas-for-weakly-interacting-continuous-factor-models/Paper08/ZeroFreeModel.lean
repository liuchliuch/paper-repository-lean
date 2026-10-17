import Paper08.ZeroFree

/-! # Bounded continuous real-potential models for the cube zero-free induction

This class is closed under coordinate freezing and convex interpolation.
Its fields are precisely range, continuity, scope, arity, and occurrence
hypotheses. Non-vanishing and phase estimates are conclusions to be proved.
-/

noncomputable section
open scoped BigOperators

namespace Paper08.ZeroFreeInduction
open Integral

/-- A labelled bounded continuous scoped real-potential model on the unit cube.
Empty scopes and zero potentials are allowed, so freezing and subcollections
stay in the same induction class. -/
structure Model (n m r c : ℕ) (q : ℝ) where
  scope : Fin m → Finset (Fin n)
  potential : Fin m → (Fin n → ℝ) → ℝ
  arity : ∀ e, (scope e).card ≤ r
  occurrence : ∀ v, (Finset.univ.filter fun e => v ∈ scope e).card ≤ c
  range : ∀ e x, x ∈ cube n → 0 ≤ potential e x ∧ potential e x ≤ q
  continuous : ∀ e, ContinuousOn (potential e) (cube n)
  depends : ∀ e x y, x ∈ cube n → y ∈ cube n →
    (∀ v ∈ scope e, x v = y v) → potential e x = potential e y

variable {n m r c : ℕ} {q : ℝ}

lemma update_mem_cube {x : Fin n → ℝ} (hx : x ∈ cube n)
    (j : Fin n) {a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    Function.update x j a ∈ cube n := by
  apply mem_cube.mpr
  intro v
  by_cases hv : v = j
  · subst v
    simpa using ha
  · simpa [Function.update_of_ne hv] using mem_cube.mp hx v

lemma continuous_update (j : Fin n) (a : ℝ) :
    Continuous (fun x : Fin n → ℝ => Function.update x j a) :=
  continuous_id.update j continuous_const

/-- Each potential can be frozen at its own value of the same coordinate.
This parametrizes the intermediate models in a finite telescoping sequence. -/
def Model.freeze (M : Model n m r c q) (j : Fin n) (a : Fin m → ℝ)
    (ha : ∀ e, a e ∈ Set.Icc (0 : ℝ) 1) : Model n m r c q where
  scope e := (M.scope e).erase j
  potential e x := M.potential e (Function.update x j (a e))
  arity e := (Finset.card_erase_le).trans (M.arity e)
  occurrence v := by
    apply le_trans (Finset.card_le_card ?_) (M.occurrence v)
    intro e he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ e,
      Finset.mem_of_mem_erase (Finset.mem_filter.mp he).2⟩
  range e x hx := M.range e _ (update_mem_cube hx j (ha e))
  continuous e := (M.continuous e).comp (continuous_update j (a e)).continuousOn
    (fun _ hx => update_mem_cube hx j (ha e))
  depends e x y hx hy hxy := by
    apply M.depends e _ _ (update_mem_cube hx j (ha e)) (update_mem_cube hy j (ha e))
    intro v hv
    by_cases hvj : v = j
    · subst v
      simp
    · simpa [Function.update_of_ne hvj] using hxy v (Finset.mem_erase.mpr ⟨hvj, hv⟩)

@[simp] lemma Model.freeze_scope (M : Model n m r c q) (j : Fin n)
    (a : Fin m → ℝ) (ha) (e : Fin m) :
    (M.freeze j a ha).scope e = (M.scope e).erase j := rfl

@[simp] lemma Model.freeze_potential (M : Model n m r c q) (j : Fin n)
    (a : Fin m → ℝ) (ha) (e : Fin m) (x : Fin n → ℝ) :
    (M.freeze j a ha).potential e x = M.potential e (Function.update x j (a e)) := rfl

/-- Convex interpolation between two models with the same declared scopes.
It preserves every induction hypothesis, including occurrence and arity. -/
def Model.mix (M N : Model n m r c q) (hscope : ∀ e, N.scope e = M.scope e)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : Model n m r c q where
  scope := M.scope
  potential e x := (1 - t) * M.potential e x + t * N.potential e x
  arity := M.arity
  occurrence := M.occurrence
  range e x hx := by
    rcases M.range e x hx with ⟨hM₀, hM₁⟩
    rcases N.range e x hx with ⟨hN₀, hN₁⟩
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) hM₀) (mul_nonneg ht.1 hN₀)
    · calc
        (1-t)*M.potential e x + t*N.potential e x ≤ (1-t)*q+t*q :=
          add_le_add (mul_le_mul_of_nonneg_left hM₁ (sub_nonneg.mpr ht.2))
            (mul_le_mul_of_nonneg_left hN₁ ht.1)
        _ = q := by ring
  continuous e := (continuousOn_const.mul (M.continuous e)).add
    (continuousOn_const.mul (N.continuous e))
  depends e x y hx hy hxy := by
    rw [M.depends e x y hx hy hxy, N.depends e x y hx hy]
    simpa [hscope e] using hxy

/-- Real exponent before multiplication by the complex interpolation argument. -/
def Model.total (M : Model n m r c q) (x : Fin n → ℝ) : ℝ :=
  ∑ e, M.potential e x

lemma Model.continuous_total (M : Model n m r c q) : ContinuousOn M.total (cube n) :=
  continuousOn_finset_sum _ fun e _ => M.continuous e

lemma Model.total_range (M : Model n m r c q) {x : Fin n → ℝ} (hx : x ∈ cube n) :
    0 ≤ M.total x ∧ M.total x ≤ m * q := by
  refine ⟨Finset.sum_nonneg (fun e _ => (M.range e x hx).1), ?_⟩
  calc
    M.total x ≤ ∑ _e : Fin m, q := Finset.sum_le_sum fun e _ => (M.range e x hx).2
    _ = m * q := by simp

@[simp] lemma Model.total_mix (M N : Model n m r c q) (hscope) (t : ℝ) (ht)
    (x : Fin n → ℝ) :
    (M.mix N hscope t ht).total x = (1-t)*M.total x + t*N.total x := by
  simp only [Model.total, Model.mix, Finset.sum_add_distrib, ← Finset.mul_sum]

lemma potential_sub_abs_le (M : Model n m r c q) (e : Fin m)
    {x y : Fin n → ℝ} (hx : x ∈ cube n) (hy : y ∈ cube n) :
    |M.potential e x - M.potential e y| ≤ q := by
  rcases M.range e x hx with ⟨hx₀, hx₁⟩
  rcases M.range e y hy with ⟨hy₀, hy₁⟩
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A coordinate changes only the factors whose declared scopes contain it. -/
lemma Model.abs_total_update_sub_le (M : Model n m r c q) (hq : 0 ≤ q)
    {x : Fin n → ℝ} (hx : x ∈ cube n) (j : Fin n)
    {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    |M.total (Function.update x j a) - M.total (Function.update x j b)| ≤ c * q := by
  classical
  let I := Finset.univ.filter fun e => j ∈ M.scope e
  have hsum : M.total (Function.update x j a) - M.total (Function.update x j b) =
      ∑ e ∈ I, (M.potential e (Function.update x j a) -
        M.potential e (Function.update x j b)) := by
    rw [Model.total, Model.total, ← Finset.sum_sub_distrib]
    symm
    apply Finset.sum_subset (Finset.subset_univ I)
    intro e he heI
    have hj : j ∉ M.scope e := by simpa [I] using heI
    apply sub_eq_zero.mpr
    apply M.depends e _ _ (update_mem_cube hx j ha) (update_mem_cube hx j hb)
    intro v hv
    have hvj : v ≠ j := by rintro rfl; exact hj hv
    simp [Function.update_of_ne hvj]
  rw [hsum]
  calc
    |∑ e ∈ I, (M.potential e (Function.update x j a) -
        M.potential e (Function.update x j b))| ≤
        ∑ e ∈ I, |M.potential e (Function.update x j a) -
          M.potential e (Function.update x j b)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ I, q := Finset.sum_le_sum fun e _ =>
      potential_sub_abs_le M e (update_mem_cube hx j ha) (update_mem_cube hx j hb)
    _ = I.card * q := by simp
    _ ≤ c * q := mul_le_mul_of_nonneg_right (by exact_mod_cast M.occurrence j) hq

lemma Model.freeze_update_eq {M : Model n m r c q} (j : Fin n)
    (a : Fin m → ℝ) (ha) (e : Fin m) (b : ℝ) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (i : Fin m) (hi : i ≠ e) (x : Fin n → ℝ) :
    (M.freeze j (Function.update a e b) (by
      intro v
      by_cases hv : v = e
      · subst v; simpa using hb
      · simpa [Function.update_of_ne hv] using ha v)).potential i x =
      (M.freeze j a ha).potential i x := by
  simp [Function.update_of_ne hi]

/-- The difference of a single pair of potentials is the difference of the
 total exponents when every other occurrence is unchanged. -/
lemma Model.total_sub_eq_single (M N : Model n m r c q) (e : Fin m)
    (heq : ∀ i, i ≠ e → ∀ x, N.potential i x = M.potential i x) (x : Fin n → ℝ) :
    N.total x - M.total x = N.potential e x - M.potential e x := by
  rw [Model.total, Model.total, ← Finset.sum_sub_distrib]
  apply Finset.sum_eq_single e
  · intro i hi hie
    rw [heq i hie x, sub_self]
  · simp

/-- The induction class contains every subcollection of the original model.
Out-of-subcollection occurrences are the zero potential, without changing any
arity or occurrence promise. -/
def ofFactors {n r m c : ℕ} (E : FactorFamily n r m) (B : Finset (Fin m))
    {q K : ℝ} (hq : 0 ≤ q) (hE : ∀ e, (E e).RangeOk q)
    (hLip : ∀ e, (E e).LipOk K) (hc : FamilyBoundedOccurrence E c) : Model n m r c q where
  scope e := (E e).scope
  potential e x := if e ∈ B then ZeroFree.ell (E e) x else 0
  arity e := (E e).card_le
  occurrence := hc
  range e x hx := by
    by_cases he : e ∈ B
    · simpa [he] using ZeroFree.ell_range (E e) (hE e) hx
    · simp [he, hq]
  continuous e := by
    by_cases he : e ∈ B
    · simpa [he] using ZeroFree.continuousOn_ell (E e) (hE e) (hLip e)
    · simpa [he] using (continuousOn_const : ContinuousOn (fun _ : Fin n → ℝ => (0 : ℝ)) (cube n))
  depends e x y hx hy hxy := by
    by_cases he : e ∈ B
    · simpa [he] using ZeroFree.ell_dependsOn_scope (E e) hxy
    · simp [he]

lemma ofFactors_total {n r m c : ℕ} (E : FactorFamily n r m) (B : Finset (Fin m))
    {q K : ℝ} (hq : 0 ≤ q) (hE : ∀ e, (E e).RangeOk q)
    (hLip : ∀ e, (E e).LipOk K) (hc : FamilyBoundedOccurrence E c) (x : Fin n → ℝ) :
    (ofFactors E B hq hE hLip hc).total x = ZeroFree.sumEll E B x := by
  classical
  simp [Model.total, ofFactors, ZeroFree.sumEll, Finset.sum_ite_mem]

end Paper08.ZeroFreeInduction
