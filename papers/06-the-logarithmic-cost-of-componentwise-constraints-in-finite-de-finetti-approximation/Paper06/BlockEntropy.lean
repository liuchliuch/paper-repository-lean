import Paper06.ConditioningCore
import Paper06.Posterior

open Real BigOperators
open scoped Classical

namespace Paper06.ConditioningFull

variable {α : Type*} [Fintype α] {n : ℕ}

/-- The actual first `m` coordinates of the joint law. -/
noncomputable def prefixLaw (P : FinProb (Fin n → α)) (m : ℕ) (hm : m ≤ n) :
    FinProb (Fin m → α) :=
  push P (fun z j => z ⟨j.val, lt_of_lt_of_le j.isLt hm⟩)

/-- Entropy of a prefix, held constant after all `n` coordinates have been
observed.  This convention makes the entropy sequence total on `ℕ`. -/
noncomputable def H (P : FinProb (Fin n → α)) (m : ℕ) : ℝ :=
  if hm : m ≤ n then FinProb.entropy (prefixLaw P m hm) else FinProb.entropy P

theorem H_eq (P : FinProb (Fin n → α)) {m : ℕ} (hm : m ≤ n) :
    H P m = FinProb.entropy (prefixLaw P m hm) := dif_pos hm

/-- Removing coordinates is a deterministic observation of the larger prefix. -/
theorem prefixLaw_truncate (P : FinProb (Fin n → α))
    {m l : ℕ} (hml : m ≤ l) (hl : l ≤ n) :
    push (prefixLaw P l hl) (fun (z : Fin l → α) (j : Fin m) => z (Fin.castLE hml j)) =
      prefixLaw P m (hml.trans hl) := by
  rw [prefixLaw, push_comp]
  rfl

/-- The block entropy sequence is monotone. -/
theorem H_mono (P : FinProb (Fin n → α)) : Monotone (H P) := by
  intro m l hml
  by_cases hl : l ≤ n
  · have hm := hml.trans hl
    rw [H_eq P hm, H_eq P hl]
    rw [← prefixLaw_truncate P hml hl]
    exact entropy_push_le _ _
  · simp only [H, dif_neg hl]
    split_ifs with hm
    · exact entropy_push_le P _
    · exact le_refl _

/-- Every block of `m` finite-alphabet variables has entropy at most
`m log |α|`, including alphabets admitting zero-mass symbols. -/
theorem prefixLaw_entropy_le (P : FinProb (Fin n → α))
    (m : ℕ) (hm : m ≤ n) :
    FinProb.entropy (prefixLaw P m hm) ≤ (m : ℝ) * log (Fintype.card α) := by
  have h := entropy_le_log_card (prefixLaw P m hm)
  simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Real.log_pow] using h

/-- The unclipped joint entropy has the same finite-alphabet ceiling. -/
theorem joint_entropy_le (P : FinProb (Fin n → α)) :
    FinProb.entropy P ≤ (n : ℝ) * log (Fintype.card α) := by
  have h := entropy_le_log_card P
  simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Real.log_pow] using h

/-- The total block entropy sequence satisfies the usual linear ceiling. -/
theorem H_cap (P : FinProb (Fin n → α)) (m : ℕ) :
    H P m ≤ (m : ℝ) * log (Fintype.card α) := by
  by_cases hm : m ≤ n
  · rw [H_eq P hm]
    exact prefixLaw_entropy_le P m hm
  · rw [H, dif_neg hm]
    exact (joint_entropy_le P).trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hm))) (Real.log_natCast_nonneg _))

theorem H_nonneg (P : FinProb (Fin n → α)) (m : ℕ) : 0 ≤ H P m := by
  unfold H
  split_ifs <;> exact entropy_nonneg _

/-- The ordered law on any specified list of sites. -/
noncomputable def selectedLaw {J : Type*} [Fintype J] [DecidableEq J]
    (P : FinProb (Fin n → α)) (f : J → Fin n) : FinProb (J → α) :=
  push P (fun z => z ∘ f)

/-- Exchangeability identifies actual laws on distinct ordered selections. -/
theorem selectedLaw_eq {J : Type*} [Fintype J] [DecidableEq J]
    (P : FinProb (Fin n → α)) (hP : Posterior.Exchangeable P)
    (f g : J → Fin n) (hf : Function.Injective f) (hg : Function.Injective g) :
    selectedLaw P f = selectedLaw P g := by
  apply FinProb.ext
  intro a
  exact Posterior.selected_mass_eq P hP f g hf hg a

/-- Reindexing an observed coordinate tuple by an equivalence preserves
its entropy. -/
theorem entropy_selected_reindex {J K : Type*} [Fintype J] [Fintype K] [DecidableEq J] [DecidableEq K]
    (P : FinProb (Fin n → α)) (f : J → Fin n) (e : K ≃ J) :
    FinProb.entropy (selectedLaw P (f ∘ e)) = FinProb.entropy (selectedLaw P f) := by
  have h := entropy_push_eq (selectedLaw P f)
    (fun z => z ∘ e) (fun z => z ∘ e.symm)
    (by intro z; funext j; simp)
  simpa only [selectedLaw, push_comp, Function.comp_assoc] using h

/-- An arbitrary finite collection of distinct coordinates has entropy
`H_card J`.  This includes all unions of disjoint observed blocks. -/
theorem entropy_selected_card {J : Type*} [Fintype J] [DecidableEq J]
    (P : FinProb (Fin n → α)) (hP : Posterior.Exchangeable P)
    (f : J → Fin n) (hf : Function.Injective f) :
    FinProb.entropy (selectedLaw P f) = H P (Fintype.card J) := by
  let m := Fintype.card J
  have hm : m ≤ n := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf
  let e : Fin m ≃ J := (Fintype.equivFin J).symm
  let g : Fin m → Fin n := fun j => ⟨j.val, lt_of_lt_of_le j.isLt hm⟩
  have hg : Function.Injective g := by
    intro a b h
    exact Fin.ext (congrArg (fun t : Fin n => t.val) h)
  have he : Function.Injective (f ∘ e) := hf.comp e.injective
  calc
    FinProb.entropy (selectedLaw P f) = FinProb.entropy (selectedLaw P (f ∘ e)) :=
      (entropy_selected_reindex P f e).symm
    _ = FinProb.entropy (selectedLaw P g) := congrArg FinProb.entropy (selectedLaw_eq P hP _ _ he hg)
    _ = H P (Fintype.card J) := (H_eq P hm).symm

/-- Convenient natural-number specialization of block entropy invariance. -/
theorem entropy_selected_eq_H {m : ℕ}
    (P : FinProb (Fin n → α)) (hP : Posterior.Exchangeable P)
    (f : Fin m → Fin n) (hf : Function.Injective f) :
    FinProb.entropy (selectedLaw P f) = H P m := by
  simpa only [Fintype.card_fin] using entropy_selected_card P hP f hf

/-- The actual joint law of two blocks of physical coordinates. -/
noncomputable def blockJoint {J K : Type*} [Fintype J] [Fintype K] [DecidableEq J] [DecidableEq K]
    (P : FinProb (Fin n → α)) (f : J → Fin n) (g : K → Fin n) :
    FinProb ((J → α) × (K → α)) :=
  push P (fun z => (z ∘ f, z ∘ g))

/-- Joint entropy of disjoint coordinate blocks is the entropy at the
sum of their cardinalities. -/
theorem entropy_blockJoint {J K : Type*} [Fintype J] [Fintype K] [DecidableEq J] [DecidableEq K]
    (P : FinProb (Fin n → α)) (hP : Posterior.Exchangeable P)
    (f : J → Fin n) (g : K → Fin n)
    (hfg : Function.Injective (Sum.elim f g)) :
    FinProb.entropy (blockJoint P f g) = H P (Fintype.card J + Fintype.card K) := by
  have he := entropy_push_eq (selectedLaw P (Sum.elim f g))
    (fun z : J ⊕ K → α => (fun j => z (Sum.inl j), fun k => z (Sum.inr k)))
    (fun z : (J → α) × (K → α) => Sum.elim z.1 z.2)
    (by intro z; funext j; cases j <;> rfl)
  have hpush : push (selectedLaw P (Sum.elim f g))
      (fun z : J ⊕ K → α => (fun j => z (Sum.inl j), fun k => z (Sum.inr k))) =
      blockJoint P f g := by
    rw [selectedLaw, push_comp]
    rfl
  rw [hpush] at he
  rw [he, entropy_selected_card P hP _ hfg, Fintype.card_sum]

/-- Joint law of one distinguished site and an ordered observed block. -/
noncomputable def siteBlock (P : FinProb (Fin n → α)) (i : Fin n)
    {m : ℕ} (g : Fin m → Fin n) : FinProb (α × (Fin m → α)) :=
  push P (fun z => (z i, z ∘ g))

/-- The entropy of one site together with a disjoint observed block. -/
theorem entropy_siteBlock {m : ℕ}
    (P : FinProb (Fin n → α)) (hP : Posterior.Exchangeable P)
    (i : Fin n) (g : Fin m → Fin n) (hg : Function.Injective g)
    (hi : ∀ j, i ≠ g j) :
    FinProb.entropy (siteBlock P i g) = H P (m + 1) := by
  let f : Option (Fin m) → Fin n := fun o => o.elim i g
  have hf : Function.Injective f := by
    intro a b hab
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some b => exact (hi b hab).elim
    | some a =>
      cases b with
      | none => exact (hi a hab.symm).elim
      | some b => exact congrArg some (hg hab)
  have he := entropy_push_eq (selectedLaw P f)
    (fun z : Option (Fin m) → α => (z none, fun j => z (some j)))
    (fun z : α × (Fin m → α) => fun o => o.elim z.1 z.2)
    (by intro z; funext j; cases j <;> rfl)
  have hpush : push (selectedLaw P f)
      (fun z : Option (Fin m) → α => (z none, fun j => z (some j))) =
      siteBlock P i g := by
    rw [selectedLaw, push_comp]
    rfl
  rw [hpush] at he
  rw [he, entropy_selected_card P hP f hf]
  simp only [Fintype.card_option, Fintype.card_fin]

/-- Swapping two unobserved sites leaves the observed block fixed, hence
gives identical site/block joint laws.  Injectivity of the observed list
is not needed for this identity. -/
theorem siteBlock_eq {m : ℕ}
    (P : FinProb (Fin n → α)) (hP : Posterior.Exchangeable P)
    (i i' : Fin n) (g : Fin m → Fin n)
    (hi : ∀ j, i ≠ g j) (hi' : ∀ j, i' ≠ g j) :
    siteBlock P i g = siteBlock P i' g := by
  apply FinProb.ext
  intro a
  simp only [siteBlock, push_w]
  have hobs : ∀ z : Fin n → α, (z ∘ Equiv.swap i i') ∘ g = z ∘ g := by
    intro z
    funext j
    simp only [Function.comp_apply,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm (hi j)) (Ne.symm (hi' j))]
  letI : DecidableEq (α × (Fin m → α)) := Classical.decEq _
  have h := Posterior.statistic_mass_permutation P hP (Equiv.swap i i')
    (fun z => (z i, z ∘ g)) a
  simpa only [Function.comp_apply, Equiv.swap_apply_left, hobs] using h.symm

/-- Natural-number specialization of the joint disjoint-block entropy. -/
theorem entropy_pair_eq_H {k m : ℕ}
    (P : FinProb (Fin n → α)) (hP : Posterior.Exchangeable P)
    (f : Fin k → Fin n) (g : Fin m → Fin n)
    (hfg : Function.Injective (Sum.elim f g)) :
    FinProb.entropy (push P (fun z => (z ∘ f, z ∘ g))) = H P (k + m) := by
  simpa only [Fintype.card_fin] using entropy_blockJoint P hP f g hfg

/-- Direct `push` formulation for the distinguished-site/block entropy. -/
theorem entropy_single_pair_eq_H {m : ℕ}
    (P : FinProb (Fin n → α)) (hP : Posterior.Exchangeable P)
    (i : Fin n) (g : Fin m → Fin n) (hg : Function.Injective g)
    (hi : ∀ j, i ≠ g j) :
    FinProb.entropy (push P (fun z => (z i, z ∘ g))) = H P (m + 1) :=
  entropy_siteBlock P hP i g hg hi

end Paper06.ConditioningFull
