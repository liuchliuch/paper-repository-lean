import GeometricMedianCoresets.TupleCollision

/-! Comparison of independent tuples with the uniform law on unordered subdatasets. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace GeometricMedianCoresets.TupleSampling

/-- The image of any ordered tuple, including tuples with collisions. -/
def image {n m : ℕ} (f : Fin m → Fin n) : Finset (Fin n) := Finset.univ.image f

def eventEquiv {n m : ℕ} (E : Finset (Fin n) → Prop) :
    {f : Fin m → Fin n // Function.Injective f ∧ E (image f)} ≃
      {e : Fin m ↪ Fin n // E (SampleFibers.image e)} where
  toFun f := ⟨⟨f.val, f.property.1⟩, f.property.2⟩
  invFun e := ⟨e.val, e.val.injective, e.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma card_injective_event {n m : ℕ} (E : Finset (Fin n) → Prop) :
    ((Finset.univ : Finset (Fin m → Fin n)).filter
      (fun f => Function.Injective f ∧ E (image f))).card =
      m.factorial * (((Finset.univ : Finset (Fin n)).powersetCard m).filter E).card := by
  have h := Fintype.card_congr (eventEquiv (n := n) (m := m) E)
  rw [Fintype.card_subtype, Fintype.card_subtype, SampleFibers.card_event] at h
  exact h

lemma card_injective (n m : ℕ) :
    ((Finset.univ : Finset (Fin m → Fin n)).filter Function.Injective).card =
      m.factorial * n.choose m := by
  have h := card_injective_event (n := n) (m := m) (fun _ => True)
  simpa using h

/-- Conditioning on no collision gives a uniform subset; discarding collisions costs at most
exactly their independent-tuple probability. This formulation needs no independence hypothesis. -/
theorem independent_le_withoutReplacement_add_collision {n m : ℕ}
    (hn : 0 < n) (hmn : m ≤ n) (E : Finset (Fin n) → Prop)
    (A : (Fin m → Fin n) → Prop)
    (hAE : ∀ f, Function.Injective f → (A f ↔ E (image f))) :
    (((Finset.univ : Finset (Fin m → Fin n)).filter A).card : ℝ) / (n:ℝ)^m ≤
      ((((Finset.univ : Finset (Fin n)).powersetCard m).filter E).card : ℝ) / (n.choose m : ℝ) +
      (((Finset.univ : Finset (Fin m → Fin n)).filter (fun f => ¬ Function.Injective f)).card : ℝ) /
        (n:ℝ)^m := by
  have hN : (0:ℝ) < (n:ℝ)^m := pow_pos (by exact_mod_cast hn) _
  have hB : (0:ℝ) < n.choose m := by exact_mod_cast Nat.choose_pos hmn
  have hI := Finset.card_filter_le (Finset.univ : Finset (Fin m → Fin n)) Function.Injective
  rw [card_injective, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at hI
  have hIR : (m.factorial:ℝ) * (n.choose m : ℝ) ≤ (n:ℝ)^m := by exact_mod_cast hI
  have hK : ((((Finset.univ : Finset (Fin m → Fin n)).filter
        (fun f => Function.Injective f ∧ E (image f))).card : ℝ) / (n:ℝ)^m) ≤
      ((((Finset.univ : Finset (Fin n)).powersetCard m).filter E).card : ℝ) / (n.choose m : ℝ) := by
    rw [card_injective_event, Nat.cast_mul]
    apply (div_le_div_iff₀ hN hB).2
    have hmul := mul_le_mul_of_nonneg_right hIR
      (Nat.cast_nonneg (α := ℝ) ((((Finset.univ : Finset (Fin n)).powersetCard m).filter E).card))
    nlinarith
  have hsub : (Finset.univ : Finset (Fin m → Fin n)).filter A ⊆
      Finset.univ.filter (fun f => Function.Injective f ∧ E (image f)) ∪
        Finset.univ.filter (fun f => ¬ Function.Injective f) := by
    intro f hf
    have he := (Finset.mem_filter.1 hf).2
    by_cases hi : Function.Injective f
    · have he' := (hAE f hi).1 he
      simp [hi, he']
    · simp [hi]
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hdiv := div_le_div_of_nonneg_right (by exact_mod_cast hc :
      (((Finset.univ : Finset (Fin m → Fin n)).filter A).card : ℝ) ≤
        ((Finset.univ.filter (fun f : Fin m → Fin n => Function.Injective f ∧ E (image f))).card : ℝ) +
        ((Finset.univ.filter (fun f : Fin m → Fin n => ¬ Function.Injective f)).card : ℝ)) hN.le
  rw [add_div] at hdiv
  linarith

/-- A sufficiently large population loses at most `1/20` when replacing independent tuples
by uniform subsets. The main lower bound is free to choose this population size. -/
theorem withoutReplacement_ge_independent_sub {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n) (hlarge : 20 * (m:ℝ)^2 ≤ n)
    (E : Finset (Fin n) → Prop) (A : (Fin m → Fin n) → Prop)
    (hAE : ∀ f, Function.Injective f → (A f ↔ E (image f))) :
    ((((Finset.univ : Finset (Fin n)).powersetCard m).filter E).card : ℝ) / (n.choose m : ℝ) ≥
      (((Finset.univ : Finset (Fin m → Fin n)).filter A).card : ℝ) / (n:ℝ)^m - 1/20 := by
  have hc := TupleCollision.bad_fraction_le hn hm
  have hbound : (m:ℝ)^2 / n ≤ 1/20 := (div_le_iff₀ (by exact_mod_cast hn : (0:ℝ) < n)).2
    (by linarith)
  have he := independent_le_withoutReplacement_add_collision hn hmn E A hAE
  linarith

end GeometricMedianCoresets.TupleSampling
