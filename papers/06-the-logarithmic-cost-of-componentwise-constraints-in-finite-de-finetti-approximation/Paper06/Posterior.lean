/-
The full finite-coordinate posterior preservation lemma.  The constraint is
imposed only at one distinguished coordinate; exchangeability and finite
summation derive its preservation under every partial observation.
-/
import Paper06.Constraints
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Algebra.BigOperators.Group.Finset.Pi

open scoped BigOperators Classical

namespace Paper06.Posterior

variable {κ α E : Type*} [Fintype κ] [DecidableEq κ] [Fintype α]
variable [AddCommGroup E] [Module ℝ E]

/-- Exchangeability under every permutation of the actual coordinate set. -/
def Exchangeable (P : FinProb (κ → α)) : Prop :=
  ∀ (σ : Equiv.Perm κ) (z : κ → α), P.w (z ∘ σ) = P.w z

/-- The tensor identity `(id ⊗ Γ) P = P₋c ⊗ η`, at one coordinate `c`.
The right-hand marginal is computed from the same joint law, with no
conditional-feasibility premise. -/
def LiftedCP (Γ : (α → ℝ) →ₗ[ℝ] E) (η : E)
    (P : FinProb (κ → α)) (c : κ) : Prop :=
  ∀ z : κ → α,
    Γ (fun a => P.w (Function.update z c a)) =
      (∑ a, P.w (Function.update z c a)) • η

/-- Exchangeability moves the single assumed lifted identity to any site. -/
theorem liftedCP_at_every_coordinate
    (Γ : (α → ℝ) →ₗ[ℝ] E) (η : E) (P : FinProb (κ → α))
    (hP : Exchangeable P) (c : κ) (hCP : LiftedCP Γ η P c) (i : κ) :
    LiftedCP Γ η P i := by
  classical
  intro z
  let σ : Equiv.Perm κ := Equiv.swap c i
  have hslice : ∀ a, P.w (Function.update (z ∘ σ) c a) =
      P.w (Function.update z i a) := by
    intro a
    have heq : (Function.update (z ∘ σ) c a) ∘ σ = Function.update z i a := by
      funext j
      by_cases hj : j = i
      · subst j
        change Function.update (z ∘ σ) c a (σ i) = Function.update z i a i
        rw [show σ i = c from Equiv.swap_apply_right c i, Function.update_self, Function.update_self]
      · have hs : σ j ≠ c := by
          intro hh
          have hh' := congrArg σ hh
          exact hj (by simpa [σ, Equiv.swap_apply_left] using hh')
        simp [Function.comp_def, Function.update_of_ne hj, Function.update_of_ne hs, σ]
    calc
      P.w (Function.update (z ∘ σ) c a) =
          P.w ((Function.update (z ∘ σ) c a) ∘ σ) := (hP σ _).symm
      _ = P.w (Function.update z i a) := congrArg P.w heq
  simpa only [hslice] using hCP (z ∘ σ)

/-- Coordinates other than the predicted site. -/
abbrev Other (i : κ) := {j : κ // j ≠ i}

/-- Join a value at `i` to an assignment of all remaining coordinates. -/
def insertCoord (i : κ) (u : Other i → α) (a : α) : κ → α :=
  fun j => if h : j = i then a else u ⟨j, h⟩

@[simp] theorem insertCoord_self (i : κ) (u : Other i → α) (a : α) :
    insertCoord i u a i = a := by simp [insertCoord]

@[simp] theorem insertCoord_other (i : κ) (u : Other i → α) (a : α)
    (j : Other i) : insertCoord i u a j = u j := by simp [insertCoord, j.property]

@[simp] theorem update_insertCoord (i : κ) (u : Other i → α) (a b : α) :
    Function.update (insertCoord i u b) i a = insertCoord i u a := by
  funext j
  by_cases h : j = i
  · subst j; simp
  · simp [Function.update_of_ne h, insertCoord, h]

/-- Splitting a joint outcome into one coordinate and its complement is a
bijection; it is used to prove the marginal formulas from the joint law. -/
def splitEquiv (i : κ) : (α × (Other i → α)) ≃ (κ → α) where
  toFun v := insertCoord i v.2 v.1
  invFun z := (z i, fun j => z j)
  left_inv v := by
    apply Prod.ext
    · simp
    · funext j; simp
  right_inv z := by
    funext j
    by_cases h : j = i
    · subst j; simp
    · simp [insertCoord, h]

/-- The probability of the cylinder event `Z_I = z_I`, evaluated directly
by summing the original joint law. -/
noncomputable def observedMass (P : FinProb (κ → α)) (I : Finset κ)
    (z : κ → α) : ℝ :=
  ∑ x, if ∀ j ∈ I, x j = z j then P.w x else 0

/-- The joint probability of `Z_I = z_I` and `Z_i = a`, evaluated directly
from the original joint law. -/
noncomputable def jointMass (P : FinProb (κ → α)) (I : Finset κ)
    (z : κ → α) (i : κ) (a : α) : ℝ :=
  ∑ x, if (∀ j ∈ I, x j = z j) ∧ x i = a then P.w x else 0

/-- Whether a complementary assignment has the observed coordinates. -/
def compatible (I : Finset κ) (z : κ → α) (i : κ) (u : Other i → α) : Prop :=
  ∀ (j : κ) (hj : j ∈ I) (hne : j ≠ i), u ⟨j, hne⟩ = z j

lemma observation_insertCoord (I : Finset κ) (z : κ → α) (i : κ)
    (hi : i ∉ I) (u : Other i → α) (a : α) :
    (∀ j ∈ I, insertCoord i u a j = z j) ↔ compatible I z i u := by
  constructor
  · intro h j hj hne
    simpa [insertCoord, hne] using h j hj
  · intro h j hj
    have hne : j ≠ i := by intro e; subst j; exact hi hj
    simpa [insertCoord, hne] using h j hj hne

lemma jointMass_nonneg (P : FinProb (κ → α)) (I : Finset κ)
    (z : κ → α) (i : κ) (a : α) : 0 ≤ jointMass P I z i a := by
  classical
  apply Finset.sum_nonneg
  intro x hx
  split_ifs
  · exact P.nonneg x
  · exact le_refl 0

/-- Disintegration of a cylinder event along one unobserved coordinate. -/
theorem jointMass_eq_complement_sum (P : FinProb (κ → α)) (I : Finset κ)
    (z : κ → α) (i : κ) (hi : i ∉ I) (a : α) :
    jointMass P I z i a =
      ∑ u : Other i → α, if compatible I z i u then P.w (insertCoord i u a) else 0 := by
  classical
  unfold jointMass
  rw [← (splitEquiv (α := α) i).sum_comp]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  change (∑ b : α, if (∀ j ∈ I, insertCoord i u b j = z j) ∧ insertCoord i u b i = a
      then P.w (insertCoord i u b) else 0) = _
  simp only [insertCoord_self]
  simp_rw [observation_insertCoord I z i hi]
  by_cases hc : compatible I z i u
  · simp [hc]
  · simp [hc]

/-- The observed marginal sums the joint probabilities over the site value. -/
theorem sum_jointMass (P : FinProb (κ → α)) (I : Finset κ)
    (z : κ → α) (i : κ) :
    ∑ a, jointMass P I z i a = observedMass P I z := by
  classical
  unfold jointMass observedMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hc : ∀ j ∈ I, x j = z j
  · simp only [ite_and, if_pos hc]
    simp
  · simp only [ite_and, if_neg hc, Finset.sum_const_zero]

/-- A genuine joint probability law with a site has a nonempty alphabet. -/
theorem alphabet_nonempty (P : FinProb (κ → α)) (i : κ) : Nonempty α := by
  classical
  by_contra h
  haveI : IsEmpty α := not_nonempty_iff.mp h
  haveI : IsEmpty (κ → α) := ⟨fun z => isEmptyElim (z i)⟩
  have hsum := P.sum_eq_one
  simp at hsum

/-- Summing the lifted identity over all unobserved coordinates gives the
unnormalized posterior identity, the intermediate equation in Lemma 2.1. -/
theorem jointMass_linear_constraint
    (Γ : (α → ℝ) →ₗ[ℝ] E) (η : E) (P : FinProb (κ → α))
    (i : κ) (hCP : LiftedCP Γ η P i)
    (I : Finset κ) (hi : i ∉ I) (z : κ → α) :
    Γ (fun a => jointMass P I z i a) = observedMass P I z • η := by
  classical
  haveI : Nonempty α := alphabet_nonempty P i
  let a₀ : α := Classical.choice (inferInstance : Nonempty α)
  have hCP' : ∀ u : Other i → α,
      Γ (fun a => P.w (insertCoord i u a)) =
        (∑ a, P.w (insertCoord i u a)) • η := by
    intro u
    simpa only [update_insertCoord] using hCP (insertCoord i u a₀)
  have hvec : (fun a => jointMass P I z i a) =
      ∑ u : Other i → α,
        if compatible I z i u then (fun a => P.w (insertCoord i u a)) else 0 := by
    funext a
    rw [jointMass_eq_complement_sum P I z i hi]
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro u hu
    split_ifs <;> rfl
  rw [hvec, map_sum]
  have hmarg : observedMass P I z =
      ∑ u : Other i → α,
        if compatible I z i u then ∑ a, P.w (insertCoord i u a) else 0 := by
    rw [← sum_jointMass P I z i]
    simp_rw [jointMass_eq_complement_sum P I z i hi]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u hu
    split_ifs <;> simp_all
  rw [hmarg, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hc : compatible I z i u
  · simpa only [if_pos hc] using hCP' u
  · simp only [if_neg hc, map_zero, zero_smul]

/-- The normalized, finite-alphabet conditional law of `Z_i` given the
positive-probability cylinder `Z_I = z_I`. -/
noncomputable def posterior (P : FinProb (κ → α)) (I : Finset κ)
    (z : κ → α) (i : κ) (hz : 0 < observedMass P I z) : FinProb α where
  w a := jointMass P I z i a / observedMass P I z
  nonneg a := div_nonneg (jointMass_nonneg P I z i a) hz.le
  sum_eq_one := by
    simp only [div_eq_mul_inv, ← Finset.sum_mul]
    rw [sum_jointMass P I z i, mul_inv_cancel₀ (ne_of_gt hz)]

/-- **Lemma 2.1 (Posterior preservation), in its full generality.**
For any finite coordinate set (hence for every finite `n`), any real linear
vector constraint, any site `i`, and every observed subset disjoint from
`i`, each positive-mass conditional law is feasible.  Only the single
original lifted identity and exchangeability are assumed. -/
theorem lemma_2_1_posterior_preservation
    (Γ : (α → ℝ) →ₗ[ℝ] E) (η : E) (P : FinProb (κ → α))
    (hP : Exchangeable P) (c : κ) (hCP : LiftedCP Γ η P c)
    (i : κ) (I : Finset κ) (hi : i ∉ I) (z : κ → α)
    (hz : 0 < observedMass P I z) :
    Γ (posterior P I z i hz).w = η := by
  have hiCP := liftedCP_at_every_coordinate Γ η P hP c hCP i
  have hlin := jointMass_linear_constraint Γ η P i hiCP I hi z
  have hvec : (posterior P I z i hz).w =
      (observedMass P I z)⁻¹ • (fun a => jointMass P I z i a) := by
    funext a
    simp only [posterior, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [hvec, map_smul, hlin, smul_smul, inv_mul_cancel₀ (ne_of_gt hz), one_smul]

/-- The vector-valued affine slice used by the paper. -/
def AffineSlice (Γ : (α → ℝ) →ₗ[ℝ] E) (η : E) : Set (FinProb α) :=
  {q | Γ q.w = η}

/-- All positive-mass posterior components belong to the original slice. -/
theorem posterior_mem_affineSlice
    (Γ : (α → ℝ) →ₗ[ℝ] E) (η : E) (P : FinProb (κ → α))
    (hP : Exchangeable P) (c : κ) (hCP : LiftedCP Γ η P c)
    (i : κ) (I : Finset κ) (hi : i ∉ I) (z : κ → α)
    (hz : 0 < observedMass P I z) :
    posterior P I z i hz ∈ AffineSlice Γ η :=
  lemma_2_1_posterior_preservation Γ η P hP c hCP i I hi z hz

/-- Probability of any event in the original finite joint sample space. -/
noncomputable def eventMass (P : FinProb (κ → α)) (A : (κ → α) → Prop) : ℝ :=
  ∑ z, if A z then P.w z else 0

/-- A site whose input marginal obeys lifted CP is independent of every
joint event unaffected by that site's full symbol.  This is the event
version of the fixed-input lifted identity used in Proposition 4.1. -/
theorem event_input_independent {X : Type*}
    (P : FinProb (κ → α)) (i : κ) (f : α → X) (π : X → ℝ)
    (hCP : ∀ (z : κ → α) (x : X),
      (∑ a, if f a = x then P.w (Function.update z i a) else 0) =
        π x * ∑ a, P.w (Function.update z i a))
    (A : (κ → α) → Prop)
    (hA : ∀ (z : κ → α) (a : α), A (Function.update z i a) ↔ A z)
    (x : X) :
    (∑ z, if A z ∧ f (z i) = x then P.w z else 0) = π x * eventMass P A := by
  classical
  haveI : Nonempty α := alphabet_nonempty P i
  let a₀ : α := Classical.choice (inferInstance : Nonempty α)
  have hA' : ∀ (u : Other i → α) (a : α),
      A (insertCoord i u a) ↔ A (insertCoord i u a₀) := by
    intro u a
    simpa only [update_insertCoord] using hA (insertCoord i u a₀) a
  have hevent : eventMass P A =
      ∑ u : Other i → α,
        if A (insertCoord i u a₀) then ∑ a, P.w (insertCoord i u a) else 0 := by
    unfold eventMass
    rw [← (splitEquiv (α := α) i).sum_comp, Fintype.sum_prod_type,
      Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u hu
    change (∑ a, if A (insertCoord i u a) then P.w (insertCoord i u a) else 0) = _
    simp_rw [hA']
    split_ifs <;> simp_all
  rw [← (splitEquiv (α := α) i).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm, hevent, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  change (∑ a, if A (insertCoord i u a) ∧ f (insertCoord i u a i) = x
    then P.w (insertCoord i u a) else 0) = _
  simp only [insertCoord_self]
  simp_rw [hA']
  by_cases h : A (insertCoord i u a₀)
  · simp only [ite_and, if_pos h]
    simpa only [update_insertCoord] using hCP (insertCoord i u a₀) x
  · simp only [ite_and, if_neg h, Finset.sum_const_zero, mul_zero]

/-- Exchangeability transports the distribution of every statistic under
a permutation of the physical coordinates. -/
theorem statistic_mass_permutation {β : Type*} [DecidableEq β]
    (P : FinProb (κ → α)) (hP : Exchangeable P)
    (σ : Equiv.Perm κ) (f : (κ → α) → β) (b : β) :
    (∑ z, if f (z ∘ σ) = b then P.w z else 0) =
      ∑ z, if f z = b then P.w z else 0 := by
  classical
  let e : (κ → α) ≃ (κ → α) :=
    { toFun := fun z => z ∘ σ
      invFun := fun z => z ∘ σ.symm
      left_inv := by intro z; funext j; simp
      right_inv := by intro z; funext j; simp }
  calc
    (∑ z, if f (z ∘ σ) = b then P.w z else 0) =
        ∑ z, if f (e z) = b then P.w (e z) else 0 := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [show P.w (e z) = P.w z from hP σ z]
      rfl
    _ = ∑ z, if f z = b then P.w z else 0 := by
      simpa using e.sum_comp (fun z => if f z = b then P.w z else 0)

/-- Any two injective selections of coordinates in a finite ambient set
are related by a permutation of that ambient set. -/
theorem exists_permutation_of_injections {J : Type*}
    (f g : J → κ) (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ σ : Equiv.Perm κ, ∀ j, σ (f j) = g j := by
  classical
  let ef := Equiv.ofInjective f hf
  let eg := Equiv.ofInjective g hg
  let e : Set.range f ≃ Set.range g := ef.symm.trans eg
  refine ⟨e.extendSubtype, ?_⟩
  intro j
  rw [e.extendSubtype_apply_of_mem (f j) (Set.mem_range_self j)]
  change (e ⟨f j, Set.mem_range_self j⟩).val = g j
  have hfj : ef j = ⟨f j, Set.mem_range_self j⟩ := rfl
  rw [← hfj]
  change (eg (ef.symm (ef j))).val = g j
  rw [ef.symm_apply_apply]
  rfl

/-- Ordered marginals on any two injective lists of distinct sites are
identical.  The observation order is preserved, not merely its support. -/
theorem selected_mass_eq {J : Type*}
    (P : FinProb (κ → α)) (hP : Exchangeable P)
    (f g : J → κ) (hf : Function.Injective f) (hg : Function.Injective g)
    (a : J → α) :
    (∑ z, if (fun j => z (f j)) = a then P.w z else 0) =
      ∑ z, if (fun j => z (g j)) = a then P.w z else 0 := by
  classical
  obtain ⟨σ, hσ⟩ := exists_permutation_of_injections f g hf hg
  have h := statistic_mass_permutation P hP σ (fun z j => z (f j)) a
  simpa only [Function.comp_apply, hσ] using h.symm

end Paper06.Posterior
