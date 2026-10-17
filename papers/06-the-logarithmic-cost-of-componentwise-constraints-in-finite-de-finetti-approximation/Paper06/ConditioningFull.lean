import Paper06.ConditioningCore
import Paper06.Posterior
import Paper06.BlockEntropy

open Real BigOperators
open scoped Classical

namespace Paper06
namespace ConditioningFull

variable {κ α J E : Type*} [Fintype κ] [DecidableEq κ] [Fintype α] [Fintype J] [DecidableEq J]
variable [AddCommGroup E] [Module ℝ E]

/-- Every positive component of a finite posterior mixture obeys the actual
original vector-valued lifted affine constraint. -/
theorem conditional_selected_feasible [Nonempty α]
    (Γ : (α → ℝ) →ₗ[ℝ] E) (η : E) (P : FinProb (κ → α))
    (hP : Posterior.Exchangeable P) (c : κ) (hCP : Posterior.LiftedCP Γ η P c)
    (i : κ) (t : J → κ) (hi : ∀ j, t j ≠ i) (b : J → α)
    (hb : 0 < (margR (push P (fun z => (z i, fun j => z (t j))))).w b) :
    Γ (conditional (push P (fun z => (z i, fun j => z (t j)))) b).w = η := by
  let R := push P (fun z => (z i, fun j => z (t j)))
  let Y : (κ → α) → (J → α) := fun z j => z (t j)
  have hm : margR R = push P Y := by
    rw [margR_eq_push, push_comp]
    rfl
  have hex : ∃ z : κ → α, Y z = b := by
    by_contra! h
    have hz : (push P Y).w b = 0 := by
      simp [push_w, h]
    change 0 < (margR R).w b at hb
    rw [hm, hz] at hb
    linarith
  obtain ⟨z, hz⟩ := hex
  let I : Finset κ := Finset.univ.image t
  have hI : i ∉ I := by
    intro h
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
    exact hi j hj
  have hevent : ∀ x : κ → α, (∀ j ∈ I, x j = z j) ↔ Y x = b := by
    intro x
    rw [← hz]
    constructor
    · intro h
      funext j
      exact h (t j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
    · intro h j hj
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hj
      exact congrFun h a
  have hobs : Posterior.observedMass P I z = (margR R).w b := by
    rw [hm]
    simp only [Posterior.observedMass, push_w, hevent]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : Y x = b <;> simp [hx]
  have hjoint : ∀ a, Posterior.jointMass P I z i a = R.w (a, b) := by
    intro a
    simp only [Posterior.jointMass, hevent, R, push_w, Prod.mk.injEq]
    apply Finset.sum_congr rfl
    intro x _
    simp [Y, and_comm]
  have hpos : 0 < Posterior.observedMass P I z := by rw [hobs]; exact hb
  have hpost : conditional R b = Posterior.posterior P I z i hpos := by
    apply FinProb.ext
    intro a
    rw [conditional_w R b hb]
    change R.w (a, b) / (margR R).w b =
      Posterior.jointMass P I z i a / Posterior.observedMass P I z
    rw [hobs, hjoint]
  change Γ (conditional R b).w = η
  rw [hpost]
  exact Posterior.lemma_2_1_posterior_preservation Γ η P hP c hCP i I hI z hpos

/-- Null observations can be filled with one fixed feasible component, so
all factors of the finite mixing law belong to the slice. -/
theorem replace_null_components {β : Type*} [Fintype β]
    (Γ : (α → ℝ) →ₗ[ℝ] E) (η : E) (w : FinProb β) (q : β → FinProb α)
    (hq : ∀ b, 0 < w.w b → Γ (q b).w = η) (k : ℕ) :
    ∃ q' : β → FinProb α, (∀ b, Γ (q' b).w = η) ∧
      mixtureProduct k w.w w.nonneg w.sum_eq_one q' =
        mixtureProduct k w.w w.nonneg w.sum_eq_one q := by
  have hex : ∃ b, 0 < w.w b := by
    by_contra! h
    have hs : (∑ b, w.w b) ≤ 0 := Finset.sum_nonpos (fun b _ => h b)
    rw [w.sum_eq_one] at hs
    linarith
  obtain ⟨b₀, hb₀⟩ := hex
  let q' : β → FinProb α := fun b => if 0 < w.w b then q b else q b₀
  refine ⟨q', ?_, ?_⟩
  · intro b
    dsimp [q']
    split_ifs with hb
    · exact hq b hb
    · exact hq b₀ hb₀
  · apply FinProb.ext
    intro z
    simp only [mixtureProduct_w]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : 0 < w.w b
    · simp [q', hb]
    · have hz : w.w b = 0 := le_antisymm (le_of_not_gt hb) (w.nonneg _)
      simp [hz]

/-- The first block is an actual injection into the `n` sites. -/
def firstSelection {n : ℕ} (k : ℕ) (hk : k ≤ n) : Fin k → Fin n := Fin.castLE hk

/-- The block of `m` conditioning sites immediately after the first `k`. -/
def nextSelection {n : ℕ} (k m : ℕ) (hkm : k + m ≤ n) : Fin m → Fin n :=
  fun j => ⟨k + j.val, by omega⟩

theorem firstSelection_injective {n k : ℕ} (hk : k ≤ n) :
    Function.Injective (firstSelection k hk) := by
  intro a b h
  apply Fin.ext
  simpa [firstSelection] using congrArg (fun i : Fin n => i.val) h

theorem nextSelection_injective {n k m : ℕ} (hkm : k + m ≤ n) :
    Function.Injective (nextSelection k m hkm) := by
  intro a b h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp [nextSelection] at this
  omega

theorem first_next_disjoint {n k m : ℕ} (hk : k ≤ n) (hkm : k + m ≤ n)
    (i : Fin k) (j : Fin m) : firstSelection k hk i ≠ nextSelection k m hkm j := by
  intro h
  have := congrArg Fin.val h
  dsimp [firstSelection, nextSelection] at this
  omega

theorem first_next_injective {n k m : ℕ} (hk : k ≤ n) (hkm : k + m ≤ n) :
    Function.Injective (Sum.elim (firstSelection k hk) (nextSelection k m hkm)) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (firstSelection_injective hk h)
    | inr b => exact (first_next_disjoint hk hkm a b h).elim
  | inr a =>
    cases b with
    | inl b => exact (first_next_disjoint hk hkm b a h.symm).elim
    | inr b => exact congrArg Sum.inr (nextSelection_injective hkm h)


/-- The finite posterior product mixture for two disjoint site lists. -/
noncomputable def blockMixture {n k m : ℕ} [Nonempty α]
    (P : FinProb (Fin n → α)) (f : Fin k → Fin n) (g : Fin m → Fin n)
    (i₀ : Fin k) : FinProb (Fin k → α) :=
  let A := blockJoint P f g
  mixtureProduct k (margR A).w (margR A).nonneg (margR A).sum_eq_one
    (conditional (siteBlock P (f i₀) g))

/-- Exchangeability identifies the posterior law at all unobserved sites. -/
theorem block_coordinate_joint {n k m : ℕ}
    (P : FinProb (Fin n → α)) (hP : Posterior.Exchangeable P)
    (f : Fin k → Fin n) (g : Fin m → Fin n)
    (hdisj : ∀ i j, f i ≠ g j) (i i₀ : Fin k) :
    push (blockJoint P f g) (fun z => (z.1 i, z.2)) = siteBlock P (f i₀) g := by
  have hmap : push (blockJoint P f g) (fun z => (z.1 i, z.2)) = siteBlock P (f i) g := by
    rw [blockJoint, push_comp]
    rfl
  exact hmap.trans (siteBlock_eq P hP (f i) (f i₀) g (hdisj i) (hdisj i₀))

/-- Actual KL convexity and total correlation for the selected block. -/
theorem block_conditional_mixture_bound {n k m : ℕ} [Nonempty α]
    (P : FinProb (Fin n → α)) (hP : Posterior.Exchangeable P)
    (f : Fin k → Fin n) (g : Fin m → Fin n)
    (hdisj : ∀ i j, f i ≠ g j) (i₀ : Fin k) :
    FinProb.Supports (selectedLaw P f) (blockMixture P f g i₀) ∧
      FinProb.klPos (selectedLaw P f) (blockMixture P f g i₀) ≤
        (k : ℝ) * (FinProb.entropy (siteBlock P (f i₀) g) - FinProb.entropy (selectedLaw P g)) -
          (FinProb.entropy (blockJoint P f g) - FinProb.entropy (selectedLaw P g)) := by
  let A := blockJoint P f g
  let R := siteBlock P (f i₀) g
  have hR := block_coordinate_joint P hP f g hdisj
  have hb := conditional_product_mixture_bound (Nat.zero_lt_of_lt i₀.isLt) A R (fun i => hR i i₀)
  have hleft : margL A = selectedLaw P f := by
    rw [margL_eq_push]
    change push (push P (fun z => (z ∘ f, z ∘ g))) Prod.fst = _
    rw [push_comp]
    rfl
  have hright : margR A = selectedLaw P g := by
    rw [margR_eq_push]
    change push (push P (fun z => (z ∘ f, z ∘ g))) Prod.snd = _
    rw [push_comp]
    rfl
  constructor
  · exact hleft ▸ hb.1
  · calc
      _ = FinProb.klPos (margL A) (blockMixture P f g i₀) :=
        congrArg (fun p => FinProb.klPos p (blockMixture P f g i₀)) hleft.symm
      _ ≤ _ := hb.2
      _ = _ := by rw [hright]

/-- Every factor of a finite posterior representation can be chosen
feasible, including the components at null conditioning observations. -/
theorem block_feasible_components {n k m : ℕ} [Nonempty α]
    (Γ : (α → ℝ) →ₗ[ℝ] E) (η : E)
    (P : FinProb (Fin n → α)) (hP : Posterior.Exchangeable P)
    (c : Fin n) (hCP : Posterior.LiftedCP Γ η P c)
    (f : Fin k → Fin n) (g : Fin m → Fin n)
    (hdisj : ∀ i j, f i ≠ g j) (i₀ : Fin k) :
    ∃ q : (Fin m → α) → FinProb α,
      (∀ b, Γ (q b).w = η) ∧
      mixtureProduct k (margR (blockJoint P f g)).w (margR (blockJoint P f g)).nonneg
        (margR (blockJoint P f g)).sum_eq_one q = blockMixture P f g i₀ := by
  let A := blockJoint P f g
  let R := siteBlock P (f i₀) g
  have hm : margR R = margR A := by
    change margR (siteBlock P (f i₀) g) = margR (blockJoint P f g)
    rw [← block_coordinate_joint P hP f g hdisj i₀ i₀]
    simp only [margR_eq_push, push_comp]
    rfl
  have hf : ∀ b, 0 < (margR A).w b → Γ (conditional R b).w = η := by
    intro b hb
    have hbR : 0 < (margR R).w b := by rwa [hm]
    have hraw := conditional_selected_feasible (J := Fin m) Γ η P hP c hCP (f i₀) g
      (fun j => (hdisj i₀ j).symm) b
    have hdef : R = push P (fun z => (z (f i₀), fun j => z (g j))) := rfl
    rw [hdef] at hbR ⊢
    exact hraw hbR
  obtain ⟨q, hq, hmix⟩ := replace_null_components Γ η (margR A) (conditional R) hf k
  refine ⟨q, hq, ?_⟩
  exact hmix

/-- **Proposition 2.2 (conditioning upper bound).**  The finite law `w`
on the feasible component family `q` is an explicit finite mixing measure.
Every factor belongs to the original affine slice, and the separate
support conclusion certifies that the paper's extended relative entropy
is finite. -/
theorem prop_2_2_conditioning_upper_bound
    (Γ : (α → ℝ) →ₗ[ℝ] E) (η : E) {n k : ℕ}
    (P : FinProb (Fin n → α)) (hP : Posterior.Exchangeable P)
    (c : Fin n) (hCP : Posterior.LiftedCP Γ η P c)
    (hk : 1 ≤ k) (hn : k < n) :
    ∃ m ≤ n - k, ∃ w : FinProb (Fin m → α), ∃ q : (Fin m → α) → FinProb α,
      (∀ b, Γ (q b).w = η) ∧
      FinProb.Supports (prefixLaw P k hn.le)
        (mixtureProduct k w.w w.nonneg w.sum_eq_one q) ∧
      FinProb.kl (prefixLaw P k hn.le)
        (mixtureProduct k w.w w.nonneg w.sum_eq_one q) ≤
        ((((k : ℝ) * (k - 1) / (2 * ((n : ℝ) - k + 1))) *
          log (Fintype.card α) : ℝ) : EReal) := by
  letI : Nonempty α := Posterior.alphabet_nonempty P c
  have hkpos : 0 < k := by omega
  have hN : 0 < n - k + 1 := by omega
  obtain ⟨m, hm, haverage⟩ := exists_entropy_average (H P) (n - k + 1) k
    (log (Fintype.card α)) hN (H_nonneg P 0)
    (fun i _ => H_mono P (Nat.le_add_right _ _)) (fun i _ => H_cap P i)
  have hmk : m ≤ n - k := by omega
  have hkm : k + m ≤ n := by omega
  let f := firstSelection k hn.le
  let g := nextSelection k m hkm
  let i₀ : Fin k := ⟨0, hkpos⟩
  have hdisj : ∀ i j, f i ≠ g j := first_next_disjoint hn.le hkm
  let w := margR (blockJoint P f g)
  obtain ⟨q, hq, hmix⟩ := block_feasible_components Γ η P hP c hCP f g hdisj i₀
  have hbound := block_conditional_mixture_bound P hP f g hdisj i₀
  have hHA : FinProb.entropy (blockJoint P f g) = H P (k + m) := by
    simpa only [Fintype.card_fin] using
      entropy_blockJoint P hP f g (first_next_injective hn.le hkm)
  have hHR : FinProb.entropy (siteBlock P (f i₀) g) = H P (m + 1) := by
    exact entropy_siteBlock P hP (f i₀) g (nextSelection_injective hkm) (hdisj i₀)
  have hHY : FinProb.entropy (selectedLaw P g) = H P m :=
    entropy_selected_eq_H P hP g (nextSelection_injective hkm)
  have hp : selectedLaw P f = prefixLaw P k hn.le := rfl
  have hs : FinProb.Supports (prefixLaw P k hn.le)
      (mixtureProduct k w.w w.nonneg w.sum_eq_one q) := by
    rw [hmix, ← hp]
    exact hbound.1
  have hreal : FinProb.klPos (prefixLaw P k hn.le)
      (mixtureProduct k w.w w.nonneg w.sum_eq_one q) ≤
      (k : ℝ) * (H P (m + 1) - H P m) - (H P (k + m) - H P m) := by
    rw [hmix, ← hp]
    calc
      _ ≤ _ := hbound.2
      _ = _ := by rw [hHA, hHR, hHY]
  have hcast : ((n - k + 1 : ℕ) : ℝ) = (n : ℝ) - k + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hn.le, Nat.cast_one]
  have havg : (k : ℝ) * (H P (m + 1) - H P m) -
      (H P (k + m) - H P m) ≤
        (k : ℝ) * (k - 1) / (2 * ((n : ℝ) - k + 1)) * log (Fintype.card α) := by
    simpa only [Nat.add_comm m k, hcast] using haverage
  refine ⟨m, hmk, w, q, hq, hs, ?_⟩
  exact (FinProb.kl_of_support hs).trans_le (EReal.coe_le_coe (hreal.trans havg))

end ConditioningFull
end Paper06
