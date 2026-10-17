import GeometricMedianCoresets.BernoulliMajority
import GeometricMedianCoresets.TupleSampling

/-! Independent uniform index tuples induce exactly the Bernoulli product law on cluster labels. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace GeometricMedianCoresets.LabelLaw
open FiniteLaw

def labels {n m : ℕ} (mark : Fin n → Bool) (f : Fin m → Fin n) : Fin m → Bool :=
  fun j => mark (f j)

def fiberEquiv {n m : ℕ} (mark : Fin n → Bool) (w : Fin m → Bool) :
    {f : Fin m → Fin n // labels mark f = w} ≃ ((j : Fin m) → {i : Fin n // mark i = w j}) where
  toFun f j := ⟨f.val j, congrFun f.property j⟩
  invFun g := ⟨fun j => (g j).val, funext fun j => (g j).property⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma card_fiber {n m : ℕ} (mark : Fin n → Bool) (w : Fin m → Bool) :
    ((Finset.univ : Finset (Fin m → Fin n)).filter (fun f => labels mark f = w)).card =
      ∏ j, ((Finset.univ : Finset (Fin n)).filter (fun i => mark i = w j)).card := by
  have h := Fintype.card_congr (fiberEquiv mark w)
  simpa only [Fintype.card_subtype, Fintype.card_pi] using h

lemma false_card {n : ℕ} (mark : Fin n → Bool) :
    ((Finset.univ : Finset (Fin n)).filter (fun i => mark i = true)).card +
      ((Finset.univ : Finset (Fin n)).filter (fun i => mark i = false)).card = n := by
  have h := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset (Fin n))) (fun i => mark i = true)
  simpa using h

/-- Each word has exactly its Bernoulli product probability, counting multiplicities. -/
theorem fiber_probability {n m : ℕ} (hn : 0 < n) (mark : Fin n → Bool) (w : Fin m → Bool) :
    (((Finset.univ : Finset (Fin m → Fin n)).filter (fun f => labels mark f = w)).card : ℝ) /
      (n:ℝ)^m = bernProduct m
        ((((Finset.univ : Finset (Fin n)).filter (fun i => mark i = true)).card : ℝ) / n) w := by
  rw [card_fiber, Nat.cast_prod]
  unfold bernProduct
  have hden : (n:ℝ)^m = ∏ _j : Fin m, (n:ℝ) := by simp
  rw [hden, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro j _
  cases hw : w j
  · rw [bern]
    simp only [Bool.false_eq_true, if_false]
    have hcard := false_card mark
    have hcardR :
        (((Finset.univ : Finset (Fin n)).filter (fun i => mark i = true)).card : ℝ) +
        (((Finset.univ : Finset (Fin n)).filter (fun i => mark i = false)).card : ℝ) = n := by
      exact_mod_cast hcard
    have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
    linarith
  · simp [bern, hw]

/-- Event probabilities agree with the Bernoulli product law before any conditioning. -/
theorem event_probability {n m : ℕ} (hn : 0 < n) (mark : Fin n → Bool)
    (E : (Fin m → Bool) → Prop) :
    (((Finset.univ : Finset (Fin m → Fin n)).filter (fun f => E (labels mark f))).card : ℝ) /
      (n:ℝ)^m = event (bernProduct m
        ((((Finset.univ : Finset (Fin n)).filter (fun i => mark i = true)).card : ℝ) / n)) E := by
  let s := (Finset.univ : Finset (Fin m → Fin n)).filter (fun f => E (labels mark f))
  let t := (Finset.univ : Finset (Fin m → Bool)).filter E
  have hmap : Set.MapsTo (labels mark) (s : Set (Fin m → Fin n)) (t : Set (Fin m → Bool)) := by
    intro f hf
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hf).2⟩
  have hc := Finset.card_eq_sum_card_fiberwise hmap
  change (s.card : ℝ) / _ = _
  rw [hc, Nat.cast_sum, Finset.sum_div]
  unfold event
  apply Finset.sum_congr rfl
  intro w hw
  have he := (Finset.mem_filter.1 hw).2
  have hfilter : s.filter (fun f => labels mark f = w) =
      (Finset.univ : Finset (Fin m → Fin n)).filter (fun f => labels mark f = w) := by
    ext f
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨h ▸ he, h⟩
  rw [hfilter]
  exact fiber_probability hn mark w

/-- On injective tuples the label count is the cluster count in the image subset. -/
lemma trueCount_image {n m : ℕ} (mark : Fin n → Bool) (f : Fin m → Fin n)
    (hf : Function.Injective f) :
    trueCount (labels mark f) = ((TupleSampling.image f).filter (fun i => mark i = true)).card := by
  unfold trueCount labels TupleSampling.image
  rw [Finset.filter_image]
  rw [Finset.card_image_of_injective _ hf]

end GeometricMedianCoresets.LabelLaw
