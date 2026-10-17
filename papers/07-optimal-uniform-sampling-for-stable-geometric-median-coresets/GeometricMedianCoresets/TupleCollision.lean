import GeometricMedianCoresets.SampleFibers

/-! A direct finite counting bound for collisions of independent uniform indices.
The harmless bound `m²/n` lets the lower-bound construction choose a larger population. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace GeometricMedianCoresets.TupleCollision

def collisionEquiv {n m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    {f : Fin m → Fin n // f i = f j} ≃ ({k : Fin m // k ≠ i} → Fin n) where
  toFun f k := f.val k
  invFun g := ⟨fun k => if hk : k = i then g ⟨j, hij.symm⟩ else g ⟨k, hk⟩, by simp [hij.symm]⟩
  left_inv f := by
    apply Subtype.ext
    funext k
    dsimp only
    split_ifs with hk
    · subst k
      exact f.property.symm
    · rfl
  right_inv g := by
    funext k
    simp [k.property]

lemma card_collision {n m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    ((Finset.univ : Finset (Fin m → Fin n)).filter (fun f => f i = f j)).card = n ^ (m - 1) := by
  have h := Fintype.card_congr (collisionEquiv (n := n) i j hij)
  have hrest : Fintype.card {k : Fin m // k ≠ i} = m - 1 := by
    rw [Fintype.card_subtype]
    have heq : (Finset.univ.filter (fun k : Fin m => k ≠ i)) = Finset.univ.erase i := by
      ext k
      simp [ne_comm]
    rw [heq]
    simp
  rw [Fintype.card_subtype, Fintype.card_fun, Fintype.card_fin, hrest] at h
  exact h

/-- The pointwise union bound for a collision witness. -/
lemma collision_indicator_le {n m : ℕ} (f : Fin m → Fin n) :
    (if ¬ Function.Injective f then (1:ℝ) else 0) ≤
      ∑ i, ∑ j, if i ≠ j ∧ f i = f j then (1:ℝ) else 0 := by
  by_cases hf : Function.Injective f
  · simp only [hf, not_true_eq_false, if_false]
    positivity
  · simp only [hf, not_false_eq_true, if_true]
    obtain ⟨i, j, heq, hne⟩ := Function.not_injective_iff.1 hf
    have hterm : (1:ℝ) ≤ ∑ k : Fin m, if i ≠ k ∧ f i = f k then (1:ℝ) else 0 := by
      have h := Finset.single_le_sum (s := Finset.univ)
        (f := fun k => if i ≠ k ∧ f i = f k then (1:ℝ) else 0)
        (fun k _ => by positivity) (Finset.mem_univ j)
      simpa [hne, heq] using h
    exact hterm.trans (Finset.single_le_sum (s := Finset.univ)
      (f := fun i => ∑ j : Fin m, if i ≠ j ∧ f i = f j then (1:ℝ) else 0)
      (fun k _ => by positivity) (Finset.mem_univ i))

/-- At most `m² n^(m-1)` index tuples have any collision. -/
theorem card_bad_le (n m : ℕ) :
    (((Finset.univ : Finset (Fin m → Fin n)).filter
      (fun f => ¬ Function.Injective f)).card : ℝ) ≤ (m:ℝ)^2 * (n:ℝ)^(m-1) := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun (f : Fin m → Fin n) _ => collision_indicator_le f)
  have hleft : (∑ f : Fin m → Fin n, if ¬ Function.Injective f then (1:ℝ) else 0) =
      ((Finset.univ.filter (fun f : Fin m → Fin n => ¬ Function.Injective f)).card : ℝ) := by
    simp [Finset.sum_ite]
  rw [hleft, Finset.sum_comm] at hs
  have hright : (∑ i : Fin m, ∑ f : Fin m → Fin n, ∑ j : Fin m,
      if i ≠ j ∧ f i = f j then (1:ℝ) else 0) ≤ (m:ℝ)^2 * (n:ℝ)^(m-1) := by
    calc _ = ∑ i : Fin m, ∑ j : Fin m, ∑ f : Fin m → Fin n,
        if i ≠ j ∧ f i = f j then (1:ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
      _ ≤ ∑ i : Fin m, ∑ j : Fin m, (n:ℝ)^(m-1) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        by_cases hij : i = j
        · simp [hij]
        · have hc := card_collision (n := n) i j hij
          have hcount : (∑ f : Fin m → Fin n, if f i = f j then (1:ℝ) else 0) =
              ((Finset.univ.filter (fun f : Fin m → Fin n => f i = f j)).card : ℝ) := by
            simp [Finset.sum_ite]
          calc _ ≤ ∑ f : Fin m → Fin n, if f i = f j then (1:ℝ) else 0 := by
                  apply Finset.sum_le_sum
                  intro f _
                  by_cases he : f i = f j <;> simp [he]
                  split_ifs <;> norm_num
            _ = _ := hcount
            _ ≤ _ := by rw [hc]; simp
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]; ring
  exact hs.trans hright

/-- Independent uniform indices have collision probability at most `m²/n`. -/
theorem bad_fraction_le {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    (((Finset.univ : Finset (Fin m → Fin n)).filter
      (fun f => ¬ Function.Injective f)).card : ℝ) / (n:ℝ)^m ≤ (m:ℝ)^2 / n := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hpow : (n:ℝ)^m = (n:ℝ)^(m-1) * n := by
    nth_rw 1 [← Nat.sub_add_cancel hm]
    rw [pow_succ]
  apply (div_le_div_of_nonneg_right (card_bad_le n m) (by positivity)).trans
  rw [hpow]
  have hne : (n:ℝ)^(m-1) ≠ 0 := pow_ne_zero _ hnR.ne'
  field_simp
  norm_num

end GeometricMedianCoresets.TupleCollision
