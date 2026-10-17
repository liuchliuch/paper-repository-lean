/-
Zero-mass input reduction, complete-row layouts, and support transport
for the fixed-input-support response-table construction.
-/
import Paper06.Posterior
import Paper06.Divergence
import Mathlib.Data.Fintype.EquivFin

open Real BigOperators
open scoped Classical

namespace Paper06.SupportReduction

/-- Place complete response rows in physical coordinates whenever they fit. -/
noncomputable def rowsEmbedding {X : Type*} [Fintype X] (n M : ℕ)
    (h : M * Fintype.card X ≤ n) : Fin M × X ↪ Fin n :=
  Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa using h))

/-- Assign each input to its designated physical site; unused sites receive a default. -/
noncomputable def prescribedInputs {X : Type*} [Nonempty X] {n M : ℕ}
    (ι : Fin M × X ↪ Fin n) : Fin n → X :=
  Function.extend ι Prod.snd (fun _ => Classical.arbitrary X)

@[simp] theorem prescribedInputs_at {X : Type*} [Nonempty X] {n M : ℕ}
    (ι : Fin M × X ↪ Fin n) (j : Fin M) (x : X) :
    prescribedInputs ι (ι (j,x)) = x :=
  ι.injective.extend_apply Prod.snd _ (j,x)

/-- The first `k` physical coordinates, as an injection. -/
def referenceSites {n k : ℕ} (hk : k ≤ n) : Fin k ↪ Fin n := Fin.castLEEmb hk

/-- Extend any displayed input string to the physical coordinate set. -/
noncomputable def referenceInputs {X : Type*} [Nonempty X] {n k : ℕ}
    (g : Fin k ↪ Fin n) (x : Fin k → X) : Fin n → X :=
  Function.extend g x (fun _ => Classical.arbitrary X)

@[simp] theorem referenceInputs_at {X : Type*} [Nonempty X] {n k : ℕ}
    (g : Fin k ↪ Fin n) (x : Fin k → X) (i : Fin k) :
    referenceInputs g x (g i) = x i := g.injective.extend_apply x _ i

/-- The floor row count always fits the physical coordinate budget. -/
theorem floor_rows_fit (n s : ℕ) : n / s * s ≤ n := Nat.div_mul_le_self n s

/-- At least one complete row exists under the proposition's `n ≥ s` hypothesis. -/
theorem floor_rows_pos (n s : ℕ) (hs : 0 < s) (hsn : s ≤ n) : 0 < n / s :=
  Nat.div_pos hsn hs

/-- The physical layout used in the proposition, with the original floor row count. -/
noncomputable def floorRowsEmbedding (X : Type*) [Fintype X] (n : ℕ) :
    Fin (n / Fintype.card X) × X ↪ Fin n :=
  rowsEmbedding n (n / Fintype.card X) (floor_rows_fit n (Fintype.card X))

/-- Every admissible sample size has canonical reference sites in the physical system. -/
def floorReferenceSites {X : Type*} [Fintype X] {n k : ℕ}
    (hk : k ≤ n / Fintype.card X) : Fin k ↪ Fin n :=
  referenceSites (hk.trans (Nat.div_le_self n (Fintype.card X)))

/-- The strictly positive input support. -/
abbrev InputSupport {X : Type*} [Fintype X] (π : FinProb X) := {x : X // 0 < π.w x}

/-- A finite probability law has at least one strictly positive mass. -/
theorem inputSupport_nonempty {X : Type*} [Fintype X] (π : FinProb X) :
    Nonempty (InputSupport π) := by
  by_contra h
  have hz : ∀ x, π.w x = 0 := by
    intro x
    apply le_antisymm _ (π.nonneg x)
    apply le_of_not_gt
    intro hx
    exact h ⟨⟨x,hx⟩⟩
  have hs := π.sum_eq_one
  simp only [hz, Finset.sum_const_zero] at hs
  norm_num at hs

/-- Restriction of a finite law to a set carrying all its mass. -/
noncomputable def restrictLaw {α : Type*} [Fintype α]
    (p : FinProb α) (S : α → Prop) (h : ∀ x, ¬ S x → p.w x = 0) :
    FinProb {x // S x} where
  w x := p.w x.1
  nonneg x := p.nonneg x.1
  sum_eq_one := by
    have hs := Fintype.sum_subtype_add_sum_subtype S p.w
    have hz : (∑ x : {x // ¬ S x}, p.w x.1) = 0 :=
      Finset.sum_eq_zero (fun x _ => h x.1 x.2)
    rw [hz, add_zero, p.sum_eq_one] at hs
    exact hs

@[simp] theorem restrictLaw_w {α : Type*} [Fintype α]
    (p : FinProb α) (S : α → Prop) (h : ∀ x, ¬ S x → p.w x = 0) (x : {x // S x}) :
    (restrictLaw p S h).w x = p.w x.1 := rfl

/-- The restricted law recovers the original law under subtype inclusion. -/
theorem map_restrictLaw {α : Type*} [Fintype α]
    (p : FinProb α) (S : α → Prop) (h : ∀ x, ¬ S x → p.w x = 0) :
    FinProb.map (restrictLaw p S h) Subtype.val = p := by
  apply FinProb.ext
  intro x
  by_cases hx : S x
  · have he : ∀ y : {x // S x}, (y : α) = x ↔ y = ⟨x,hx⟩ := by
      intro y
      exact ⟨fun hy => Subtype.ext hy, fun hy => congrArg Subtype.val hy⟩
    simp only [FinProb.map_w, restrictLaw_w, he]
    simp
  · have he : ∀ y : {x // S x}, (y : α) ≠ x := by
      intro y he
      exact hx (he ▸ y.2)
    simp [FinProb.map_w, he, h x hx]

/-- The input law on its positive support, with unchanged positive weights. -/
noncomputable def supportLaw {X : Type*} [Fintype X] (π : FinProb X) :
    FinProb (InputSupport π) :=
  restrictLaw π (fun x => 0 < π.w x)
    (fun x hx => le_antisymm (le_of_not_gt hx) (π.nonneg x))

@[simp] theorem supportLaw_w {X : Type*} [Fintype X] (π : FinProb X)
    (x : InputSupport π) : (supportLaw π).w x = π.w x := rfl

theorem supportLaw_positive {X : Type*} [Fintype X] (π : FinProb X)
    (x : InputSupport π) : 0 < (supportLaw π).w x := x.2

@[simp] theorem map_supportLaw {X : Type*} [Fintype X] (π : FinProb X) :
    FinProb.map (supportLaw π) Subtype.val = π := map_restrictLaw _ _ _

/-- The all-coordinate fixed-input lifted identity, stated directly in finite weights.
This is definitionally the same identity as `Response.FixedInputCP`. -/
def InputCP {κ X A : Type*} [Fintype κ] [DecidableEq κ] [Fintype X] [Fintype A]
    (π : FinProb X) (P : FinProb (κ → X × A)) : Prop :=
  ∀ i z x, (∑ a : X × A, if a.1 = x then P.w (Function.update z i a) else 0) =
    π.w x * ∑ a, P.w (Function.update z i a)

/-- A configuration with an impossible input has zero mass, as a consequence of (CP). -/
theorem zero_of_unsupported_input {κ X A : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype X] [Fintype A] (π : FinProb X) (P : FinProb (κ → X × A))
    (hCP : InputCP π P) (z : κ → X × A) (i : κ)
    (hz : ¬ 0 < π.w (z i).1) : P.w z = 0 := by
  have hz0 : π.w (z i).1 = 0 := le_antisymm (le_of_not_gt hz) (π.nonneg _)
  have hs := Posterior.event_input_independent P i Prod.fst π.w
    (hCP i) (fun _ => True) (by simp) (z i).1
  simp only [true_and, hz0, zero_mul] at hs
  have he : (if (z i).1 = (z i).1 then P.w z else 0) ≤
      ∑ u, if (u i).1 = (z i).1 then P.w u else 0 :=
    Finset.single_le_sum
      (f := fun u : κ → X × A => if (u i).1 = (z i).1 then P.w u else 0)
      (fun u _ => by dsimp only; split_ifs; exact P.nonneg u; exact le_rfl) (Finset.mem_univ z)
  simp only [if_true] at he
  rw [hs] at he
  exact le_antisymm he (P.nonneg z)

/-- Inclusion of support-restricted site alphabets, applied to a full configuration. -/
def includeInputs {κ X A : Type*} [Fintype X] (π : FinProb X)
    (z : κ → InputSupport π × A) : κ → X × A := fun i => ((z i).1.1, (z i).2)

theorem includeInputs_injective {κ X A : Type*} [Fintype X] (π : FinProb X) :
    Function.Injective (includeInputs (κ := κ) (A := A) π) := by
  intro z u h
  funext i
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun v => (v i).1) h
  · exact congrArg (fun v => (v i).2) h

/-- Removing zero-probability input symbols from a full joint law. -/
noncomputable def reducedLaw {κ X A : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype X] [Fintype A] (π : FinProb X) (P : FinProb (κ → X × A))
    (hCP : InputCP π P) : FinProb (κ → InputSupport π × A) where
  w z := P.w (includeInputs π z)
  nonneg z := P.nonneg _
  sum_eq_one := by
    calc
      (∑ z, P.w (includeInputs π z)) = ∑ u, P.w u := by
        apply Fintype.sum_of_injective (includeInputs π) (includeInputs_injective π)
        · intro u hu
          by_cases hpos : ∀ i, 0 < π.w (u i).1
          · exfalso
            apply hu
            exact ⟨fun i => (⟨(u i).1, hpos i⟩, (u i).2), rfl⟩
          · obtain ⟨i, hi⟩ := not_forall.mp hpos
            exact zero_of_unsupported_input π P hCP u i hi
        · intro z
          rfl
      _ = 1 := P.sum_eq_one

@[simp] theorem reducedLaw_w {κ X A : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype X] [Fintype A] (π : FinProb X) (P : FinProb (κ → X × A))
    (hCP : InputCP π P) (z : κ → InputSupport π × A) :
    (reducedLaw π P hCP).w z = P.w (includeInputs π z) := rfl

/-- Support restriction commutes with every coordinate permutation. -/
theorem reducedLaw_exchangeable {κ X A : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype X] [Fintype A] (π : FinProb X) (P : FinProb (κ → X × A))
    (hCP : InputCP π P) (hP : Posterior.Exchangeable P) :
    Posterior.Exchangeable (reducedLaw π P hCP) := by
  intro σ z
  exact hP σ (includeInputs π z)

/-- Summing only supported input symbols leaves every support-concentrated statistic unchanged. -/
theorem sum_support_prod {X A : Type*} [Fintype X] [Fintype A]
    (π : FinProb X) (f : X × A → ℝ)
    (hf : ∀ x, ¬ 0 < π.w x → ∀ a, f (x,a) = 0) :
    (∑ z : InputSupport π × A, f (z.1.1,z.2)) = ∑ z : X × A, f z := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  have hs := Fintype.sum_subtype_add_sum_subtype (fun x => 0 < π.w x)
    (fun x => ∑ a : A, f (x,a))
  have hz : (∑ x : {x // ¬ 0 < π.w x}, ∑ a : A, f (x.1,a)) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    exact Finset.sum_eq_zero (fun a _ => hf x.1 x.2 a)
  rw [hz, add_zero] at hs
  exact hs

@[simp] theorem includeInputs_update {κ X A : Type*} [DecidableEq κ] [Fintype X]
    (π : FinProb X) (z : κ → InputSupport π × A) (i : κ) (a : InputSupport π × A) :
    includeInputs π (Function.update z i a) =
      Function.update (includeInputs π z) i (a.1.1,a.2) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [includeInputs]
  · simp [includeInputs, Function.update_of_ne hj]

/-- The reduced joint law satisfies the same lifted constraint, now with positive input law. -/
theorem reducedLaw_inputCP {κ X A : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype X] [Fintype A] (π : FinProb X) (P : FinProb (κ → X × A))
    (hCP : InputCP π P) : InputCP (supportLaw π) (reducedLaw π P hCP) := by
  intro i z x
  simp only [reducedLaw_w, supportLaw_w, includeInputs_update]
  have hz (v : X) (hv : ¬ 0 < π.w v) (a : A) :
      P.w (Function.update (includeInputs π z) i (v,a)) = 0 := by
    exact zero_of_unsupported_input π P hCP _ i (by simpa only [Function.update_self] using hv)
  have htotal := sum_support_prod π
    (fun a : X × A => P.w (Function.update (includeInputs π z) i a)) hz
  have hleft := sum_support_prod π
    (fun a : X × A => if a.1 = (x : X) then
      P.w (Function.update (includeInputs π z) i a) else 0)
    (fun v hv a => by dsimp only; split_ifs; exact hz v hv a; rfl)
  have hl : (∑ a : InputSupport π × A, if a.1 = x then
        P.w (Function.update (includeInputs π z) i (a.1.1,a.2)) else 0) =
      ∑ a : X × A, if a.1 = (x : X) then
        P.w (Function.update (includeInputs π z) i a) else 0 := by
    simpa only [Subtype.ext_iff] using hleft
  rw [hl, htotal]
  exact hCP i (includeInputs π z) x.1

/-- Every original configuration outside the included support has zero probability. -/
theorem zero_of_not_range_includeInputs {κ X A : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype X] [Fintype A] (π : FinProb X) (P : FinProb (κ → X × A))
    (hCP : InputCP π P) (u : κ → X × A)
    (hu : u ∉ Set.range (includeInputs (κ := κ) (A := A) π)) : P.w u = 0 := by
  by_cases hpos : ∀ i, 0 < π.w (u i).1
  · exact False.elim (hu ⟨fun i => (⟨(u i).1,hpos i⟩,(u i).2),rfl⟩)
  · obtain ⟨i,hi⟩ := not_forall.mp hpos
    exact zero_of_unsupported_input π P hCP u i hi

/-- Including support-restricted configurations exactly recovers the original joint law. -/
theorem map_reducedLaw {κ X A : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype X] [Fintype A] (π : FinProb X) (P : FinProb (κ → X × A))
    (hCP : InputCP π P) :
    FinProb.map (reducedLaw π P hCP) (includeInputs π) = P := by
  apply FinProb.ext
  intro u
  by_cases hu : u ∈ Set.range (includeInputs (κ := κ) (A := A) π)
  · obtain ⟨z,rfl⟩ := hu
    have he : ∀ v : κ → InputSupport π × A,
        includeInputs π v = includeInputs π z ↔ v = z := by
      intro v
      exact (includeInputs_injective π).eq_iff
    simp only [FinProb.map_w, he]
    simp
  · have he : ∀ z : κ → InputSupport π × A, includeInputs π z ≠ u := by
      intro z hz
      exact hu ⟨z,hz⟩
    simp only [FinProb.map_w, he, if_false, Finset.sum_const_zero]
    exact (zero_of_not_range_includeInputs π P hCP u hu).symm

/-- Applying a one-site map independently commutes with forming an iid law. -/
theorem map_productFinProb {α β : Type*} [Fintype α] [Fintype β]
    (p : FinProb α) (f : α → β) (k : ℕ) :
    FinProb.map (productFinProb k p) (fun z i => f (z i)) =
      productFinProb k (FinProb.map p f) := by
  apply FinProb.ext
  intro z
  simp only [FinProb.map_w, productFinProb_w]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : ∀ i : Fin k, f (x i) = z i
  · have he : (fun i => f (x i)) = z := funext hx
    simp only [he, if_true]
    apply Finset.prod_congr rfl
    intro i _
    rw [if_pos (hx i)]
  · have he : (fun i => f (x i)) ≠ z := fun h => hx (congrFun h)
    rw [if_neg he]
    obtain ⟨i,hi⟩ := not_forall.mp hx
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp only [if_neg hi])

/-- Applying any observation map commutes with finite probability mixtures. -/
theorem map_mixture {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]
    (w : ι → ℝ) (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1)
    (q : ι → FinProb α) (f : α → β) :
    FinProb.map (mixture w hw hw1 q) f =
      mixture w hw hw1 (fun j => FinProb.map (q j) f) := by
  apply FinProb.ext
  intro y
  simp only [FinProb.map_w, mixture_w]
  have he (x : α) : (if f x = y then ∑ j, w j * (q j).w x else 0) =
      ∑ j, w j * (if f x = y then (q j).w x else 0) := by
    by_cases hx : f x = y <;> simp [hx]
  simp_rw [he]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

/-- A one-site map carries a product mixture to the mixture of mapped one-site laws. -/
theorem map_mixtureProduct {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]
    (k : ℕ) (w : ι → ℝ) (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1)
    (q : ι → FinProb α) (f : α → β) :
    FinProb.map (mixtureProduct k w hw hw1 q) (fun z i => f (z i)) =
      mixtureProduct k w hw hw1 (fun j => FinProb.map (q j) f) := by
  unfold mixtureProduct
  rw [map_mixture]
  simp_rw [map_productFinProb]

/-- Inclusion of a support-restricted one-site alphabet. -/
def includeSite {X A : Type*} [Fintype X] (π : FinProb X)
    (z : InputSupport π × A) : X × A := (z.1.1,z.2)

/-- Lift a one-site law on the positive input support to the original alphabet. -/
noncomputable def liftLaw {X A : Type*} [Fintype X] [Fintype A]
    (π : FinProb X) (q : FinProb (InputSupport π × A)) : FinProb (X × A) :=
  FinProb.map q (includeSite π)

@[simp] theorem liftLaw_w_supported {X A : Type*} [Fintype X] [Fintype A]
    (π : FinProb X) (q : FinProb (InputSupport π × A)) (x : InputSupport π) (a : A) :
    (liftLaw π q).w (x.1,a) = q.w (x,a) := by
  have he : ∀ z : InputSupport π × A, includeSite π z = (x.1,a) ↔ z = (x,a) := by
    intro z
    constructor
    · intro h
      apply Prod.ext
      · exact Subtype.ext (congrArg Prod.fst h)
      · exact congrArg (fun b : X × A => b.2) h
    · rintro rfl
      rfl
  simp only [liftLaw, FinProb.map_w, he]
  simp

@[simp] theorem liftLaw_w_unsupported {X A : Type*} [Fintype X] [Fintype A]
    (π : FinProb X) (q : FinProb (InputSupport π × A)) (x : X)
    (hx : ¬ 0 < π.w x) (a : A) : (liftLaw π q).w (x,a) = 0 := by
  have he : ∀ z : InputSupport π × A, includeSite π z ≠ (x,a) := by
    intro z h
    have hzx : z.1.1 = x := congrArg (fun b : X × A => b.1) h
    exact hx (hzx ▸ z.1.2)
  simp only [liftLaw, FinProb.map_w, he, if_false, Finset.sum_const_zero]

/-- Feasible components on the support lift to feasible components for the original input law. -/
theorem liftLaw_feasible {X A : Type*} [Fintype X] [Fintype A]
    (π : FinProb X) (q : FinProb (InputSupport π × A))
    (hq : ∀ x, ∑ a : A, q.w (x,a) = (supportLaw π).w x) :
    ∀ x : X, ∑ a : A, (liftLaw π q).w (x,a) = π.w x := by
  intro x
  by_cases hx : 0 < π.w x
  · calc
      (∑ a, (liftLaw π q).w (x,a)) = ∑ a, q.w (⟨x,hx⟩,a) := by
        apply Finset.sum_congr rfl
        intro a _
        exact liftLaw_w_supported π q ⟨x,hx⟩ a
      _ = π.w x := hq ⟨x,hx⟩
  · simp only [liftLaw_w_unsupported π q x hx, Finset.sum_const_zero]
    exact le_antisymm (π.nonneg x) (le_of_not_gt hx)

/-- Support inclusion commutes with taking any ordered marginal. -/
theorem map_reduced_marginal {κ ι X A : Type*}
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    [Fintype X] [Fintype A] (π : FinProb X) (P : FinProb (κ → X × A))
    (hCP : InputCP π P) (g : ι → κ) :
    FinProb.map (FinProb.map (reducedLaw π P hCP) (fun z i => z (g i)))
        (includeInputs π) = FinProb.map P (fun z i => z (g i)) := by
  calc
    _ = FinProb.map (FinProb.map (reducedLaw π P hCP) (includeInputs π))
        (fun z i => z (g i)) := by
      rw [FinProb.map_comp, FinProb.map_comp]
      rfl
    _ = FinProb.map P (fun z i => z (g i)) :=
      congrArg (fun R : FinProb (κ → X × A) => FinProb.map R (fun z i => z (g i)))
        (map_reducedLaw π P hCP)

/-- Lifting all one-site components recovers the original-alphabet product mixture. -/
theorem map_lifted_mixtureProduct {X A ι : Type*}
    [Fintype X] [Fintype A] [Fintype ι]
    (π : FinProb X) (k : ℕ) (w : FinProb ι) (q : ι → FinProb (InputSupport π × A)) :
    FinProb.map (mixtureProduct k w.w w.nonneg w.sum_eq_one q) (includeInputs π) =
      mixtureProduct k w.w w.nonneg w.sum_eq_one (fun j => liftLaw π (q j)) :=
  map_mixtureProduct k w.w w.nonneg w.sum_eq_one q (includeSite π)

/-- An injective finite observation preserves the mass of every image atom. -/
theorem map_injective_w {α β : Type*} [Fintype α] [Fintype β]
    (p : FinProb α) (f : α → β) (hf : Function.Injective f) (x : α) :
    (FinProb.map p f).w (f x) = p.w x := by
  simp only [FinProb.map_w, hf.eq_iff]
  simp

/-- The lifted constraint for any input-label map on a finite site alphabet.
Taking the alphabet to be `Σ x, A x` and the label map to be `Sigma.fst`
is precisely the dependent-output fixed-input constraint. -/
def InputFiberCP {κ X Z : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype X] [Fintype Z] (π : FinProb X) (label : Z → X)
    (P : FinProb (κ → Z)) : Prop :=
  ∀ i z x, (∑ a : Z, if label a = x then P.w (Function.update z i a) else 0) =
    π.w x * ∑ a : Z, P.w (Function.update z i a)

/-- Encode a dependent site alphabet in a product alphabet by recording its input label. -/
def encodeInputs {κ X Z : Type*} (label : Z → X) (z : κ → Z) : κ → X × Z :=
  fun i => (label (z i),z i)

theorem encodeInputs_injective {κ X Z : Type*} (label : Z → X) :
    Function.Injective (encodeInputs (κ := κ) label) := by
  intro z u h
  funext i
  exact congrArg (fun v => (v i).2) h

/-- The actual pushforward law on the common product alphabet. -/
noncomputable def encodedLaw {κ X Z : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype X] [Fintype Z] (label : Z → X) (P : FinProb (κ → Z)) :
    FinProb (κ → X × Z) := FinProb.map P (encodeInputs label)

/-- Encoded mass is the original mass exactly on valid label-output pairs, and zero otherwise. -/
theorem encodedLaw_w {κ X Z : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype X] [Fintype Z] (label : Z → X) (P : FinProb (κ → Z))
    (z : κ → X × Z) :
    (encodedLaw label P).w z =
      if ∀ i, label (z i).2 = (z i).1 then P.w (fun i => (z i).2) else 0 := by
  by_cases hz : ∀ i, label (z i).2 = (z i).1
  · have he : encodeInputs label (fun i => (z i).2) = z := by
      funext i
      exact Prod.ext (hz i) rfl
    rw [if_pos hz, ← he]
    exact map_injective_w P (encodeInputs label) (encodeInputs_injective label) _
  · rw [if_neg hz]
    have he : ∀ u : κ → Z, encodeInputs label u ≠ z := by
      intro u hu
      apply hz
      intro i
      have hi := congrFun hu i
      rw [← hi]
      rfl
    simp only [encodedLaw, FinProb.map_w, he, if_false, Finset.sum_const_zero]

/-- Invalid input-output labels have exactly zero probability under the encoded law. -/
theorem encodedLaw_zero_invalid {κ X Z : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype X] [Fintype Z] (label : Z → X) (P : FinProb (κ → Z))
    (z : κ → X × Z) (i : κ) (hi : label (z i).2 ≠ (z i).1) :
    (encodedLaw label P).w z = 0 := by
  rw [encodedLaw_w, if_neg (fun h => hi (h i))]

/-- Projecting away the redundant label exactly recovers the original dependent-output law. -/
theorem map_encodedLaw_snd {κ X Z : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype X] [Fintype Z] (label : Z → X) (P : FinProb (κ → Z)) :
    FinProb.map (encodedLaw label P) (fun z i => (z i).2) = P := by
  rw [encodedLaw, FinProb.map_comp]
  exact FinProb.map_id P

/-- Encoding input labels preserves exchangeability of the original dependent-output law. -/
theorem encodedLaw_exchangeable {κ X Z : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype X] [Fintype Z] (label : Z → X) (P : FinProb (κ → Z))
    (hP : Posterior.Exchangeable P) : Posterior.Exchangeable (encodedLaw label P) := by
  intro σ z
  by_cases hz : ∀ i, label (z i).2 = (z i).1
  · have hs : ∀ i, label ((z ∘ σ) i).2 = ((z ∘ σ) i).1 := fun i => hz (σ i)
    rw [encodedLaw_w, if_pos hs, encodedLaw_w, if_pos hz]
    exact hP σ (fun i => (z i).2)
  · have hs : ¬ ∀ i, label ((z ∘ σ) i).2 = ((z ∘ σ) i).1 := by
      intro h
      apply hz
      intro i
      simpa only [Function.comp_apply, σ.apply_symm_apply] using h (σ.symm i)
    simp only [encodedLaw_w, if_neg hs, if_neg hz]

/-- Updating the predicted coordinate only changes its own label-validity condition. -/
theorem encodedLaw_update_w {κ X Z : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype X] [Fintype Z] (label : Z → X) (P : FinProb (κ → Z))
    (z : κ → X × Z) (i : κ)
    (hz : ∀ j, j ≠ i → label (z j).2 = (z j).1) (x : X) (a : Z) :
    (encodedLaw label P).w (Function.update z i (x,a)) =
      if label a = x then P.w (Function.update (fun j => (z j).2) i a) else 0 := by
  rw [encodedLaw_w]
  have hv : (∀ j, label ((Function.update z i (x,a)) j).2 =
      ((Function.update z i (x,a)) j).1) ↔ label a = x := by
    constructor
    · intro h
      simpa only [Function.update_self] using h i
    · intro h j
      by_cases hj : j = i
      · subst j
        simpa only [Function.update_self] using h
      · simpa only [Function.update_of_ne hj] using hz j hj
  have he : (fun j => ((Function.update z i (x,a)) j).2) =
      Function.update (fun j => (z j).2) i a := by
    funext j
    by_cases hj : j = i
    · subst j
      simp
    · simp only [Function.update_of_ne hj]
  simp only [hv, he]

/-- The encoded product-alphabet law inherits (CP) from the original labelled alphabet. -/
theorem encodedLaw_inputCP {κ X Z : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype X] [Fintype Z] (π : FinProb X) (label : Z → X)
    (P : FinProb (κ → Z)) (hCP : InputFiberCP π label P) :
    InputCP π (encodedLaw label P) := by
  intro i z x
  by_cases hz : ∀ j, j ≠ i → label (z j).2 = (z j).1
  · have ht : (∑ a : X × Z, (encodedLaw label P).w (Function.update z i a)) =
        ∑ a : Z, P.w (Function.update (fun j => (z j).2) i a) := by
      rw [Fintype.sum_prod_type]
      simp_rw [encodedLaw_update_w label P z i hz]
      rw [Finset.sum_comm]
      simp
    have hl : (∑ a : X × Z, if a.1 = x then
        (encodedLaw label P).w (Function.update z i a) else 0) =
        ∑ a : Z, if label a = x then
          P.w (Function.update (fun j => (z j).2) i a) else 0 := by
      rw [Fintype.sum_prod_type]
      have he (y : X) : (∑ a : Z, if y = x then
          (encodedLaw label P).w (Function.update z i (y,a)) else 0) =
          if y = x then ∑ a : Z, if label a = x then
            P.w (Function.update (fun j => (z j).2) i a) else 0 else 0 := by
        by_cases hy : y = x
        · subst y
          simp only [if_true, encodedLaw_update_w label P z i hz]
        · simp only [if_neg hy, Finset.sum_const_zero]
      simp only [he]
      simp
    rw [hl, ht]
    exact hCP i (fun j => (z j).2) x
  · obtain ⟨j,hj⟩ := not_forall.mp hz
    have hji : j ≠ i := by
      by_contra h
      subst j
      exact hj (by simp)
    have hjz : label (z j).2 ≠ (z j).1 := by
      intro h
      exact hj (fun _ => h)
    have he : ∀ a : X × Z,
        (encodedLaw label P).w (Function.update z i a) = 0 := by
      intro a
      exact encodedLaw_zero_invalid label P _ j
        (by simpa only [Function.update_of_ne hji] using hjz)
    simp only [he, ite_self, Finset.sum_const_zero, mul_zero]

/-- Two observation maps agreeing at all positive-mass atoms have the same pushforward. -/
theorem map_eq_of_ae_eq {α β : Type*} [Fintype α] [Fintype β]
    (p : FinProb α) (f g : α → β) (h : ∀ z, p.w z ≠ 0 → f z = g z) :
    FinProb.map p f = FinProb.map p g := by
  apply FinProb.ext
  intro y
  simp only [FinProb.map_w]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : p.w z = 0
  · simp [hz]
  · rw [h z hz]

/-- Support inclusion preserves every relation between inputs and outputs. -/
theorem liftLaw_relation {X A : Type*} [Fintype X] [Fintype A]
    (π : FinProb X) (q : FinProb (InputSupport π × A)) (R : X → A → Prop)
    (hq : ∀ z, ¬ R z.1.1 z.2 → q.w z = 0) :
    ∀ z, ¬ R z.1 z.2 → (liftLaw π q).w z = 0 := by
  rintro ⟨x,a⟩ hx
  by_cases hp : 0 < π.w x
  · rw [liftLaw_w_supported π q ⟨x,hp⟩ a]
    exact hq (⟨x,hp⟩,a) hx
  · exact liftLaw_w_unsupported π q x hp a

/-- The same relation-preservation statement in positive-mass form. -/
theorem liftLaw_relation_of_nonzero {X A : Type*} [Fintype X] [Fintype A]
    (π : FinProb X) (q : FinProb (InputSupport π × A)) (R : X → A → Prop)
    (hq : ∀ z, q.w z ≠ 0 → R z.1.1 z.2) :
    ∀ z, (liftLaw π q).w z ≠ 0 → R z.1 z.2 := by
  intro z hz
  by_contra hR
  apply hz
  exact liftLaw_relation π q R
    (fun u hu => by by_contra h; exact hu (hq u h)) z hR

/-- Projection of an encoded marginal recovers the original dependent-output marginal. -/
theorem map_encoded_marginal {κ ι X Z : Type*}
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    [Fintype X] [Fintype Z] (label : Z → X) (P : FinProb (κ → Z)) (g : ι → κ) :
    FinProb.map (FinProb.map (encodedLaw label P) (fun z i => z (g i)))
        (fun z i => (z i).2) = FinProb.map P (fun z i => z (g i)) := by
  calc
    _ = FinProb.map (FinProb.map (encodedLaw label P) (fun z i => (z i).2))
        (fun z i => z (g i)) := by
      rw [FinProb.map_comp, FinProb.map_comp]
      rfl
    _ = FinProb.map P (fun z i => z (g i)) :=
      congrArg (fun Q : FinProb (κ → Z) => FinProb.map Q (fun z i => z (g i)))
        (map_encodedLaw_snd label P)

/-- Valid label-output pairs turn an ordinary input marginal into the original labelled marginal. -/
theorem map_snd_feasible {X Z : Type*} [Fintype X] [Fintype Z]
    (π : FinProb X) (label : Z → X) (q : FinProb (X × Z))
    (hq : ∀ x, ∑ a : Z, q.w (x,a) = π.w x)
    (hvalid : ∀ z, label z.2 ≠ z.1 → q.w z = 0) :
    ∀ x, (∑ a : Z, if label a = x then (FinProb.map q Prod.snd).w a else 0) = π.w x := by
  intro x
  have hi : (∑ a : Z, if label a = x then (FinProb.map q Prod.snd).w a else 0) =
      ∑ a : Z, (FinProb.map q Prod.snd).w a * (if label a = x then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  rw [hi, FinProb.sum_map_mul]
  have he (z : X × Z) :
      q.w z * (if label z.2 = x then 1 else 0) = if z.1 = x then q.w z else 0 := by
    by_cases hz : q.w z = 0
    · simp [hz]
    · have hl : label z.2 = z.1 := by
        by_contra h
        exact hz (hvalid z h)
      simp only [hl]
      split_ifs <;> simp
  simp_rw [he]
  rw [Fintype.sum_prod_type]
  have hs (y : X) : (∑ a : Z, if y = x then q.w (y,a) else 0) =
      if y = x then ∑ a : Z, q.w (x,a) else 0 := by
    by_cases hy : y = x <;> simp [hy]
  simp only [hs]
  simpa using hq x

end Paper06.SupportReduction
