import Paper08.ZeroFreeFreeze
import Paper08.ComplexSector

/-! # Finite phase telescoping and the unintegrated base case -/
noncomputable section
open scoped BigOperators
namespace Paper08.ZeroFreeInduction
open Integral ComplexSector

/-- Finite telescoping only accumulates one bound for each selected labelled
 occurrence. This theorem does not presuppose any partition-function fact. -/
lemma phase_finset_telescope {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (F : Finset ι → ℂ) (d : ℝ)
    (hstep : ∀ A ⊆ I, ∀ e ∈ I, e ∉ A → Phase (F A) (F (insert e A)) d) :
    Phase (F ∅) (F I) ((I.card : ℝ) * d) := by
  have h : ∀ A : Finset ι, A ⊆ I → Phase (F ∅) (F A) ((A.card : ℝ) * d) := by
    intro A
    induction A using Finset.induction_on with
    | empty =>
        intro _
        simpa using phase_refl (F ∅)
    | @insert e A he ih =>
        intro hAI
        have hsub : A ⊆ I := fun i hi => hAI (Finset.mem_insert_of_mem hi)
        have heI : e ∈ I := hAI (Finset.mem_insert_self e A)
        have ht := (ih hsub).trans (hstep A hsub e heI he)
        simpa only [Finset.card_insert_of_notMem he, Nat.cast_add, Nat.cast_one, add_mul,
          one_mul] using ht
  exact h I (Finset.Subset.refl I)

variable {n m r c : ℕ} {q : ℝ}

/-- The actual complex exponential associated to a scoped model. -/
def Model.exponential (M : Model n m r c q) (z : ℂ) (x : Fin n → ℝ) : ℂ :=
  Complex.exp (z * (M.total x : ℂ))

lemma Model.continuous_exponential (M : Model n m r c q) (z : ℂ) :
    ContinuousOn (M.exponential z) (cube n) :=
  Complex.continuous_exp.comp_continuousOn
    (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn M.continuous_total))

lemma Model.exponential_ne_zero (M : Model n m r c q) (z : ℂ) (x : Fin n → ℝ) :
    M.exponential z x ≠ 0 := Complex.exp_ne_zero _

/-- Changing one coordinate before integration changes the phase by at most
 the total occurrence budget. This is the base of the cardinality induction. -/
lemma Model.phase_exponential_update (M : Model n m r c q) (hq : 0 ≤ q) (z : ℂ)
    {x : Fin n → ℝ} (hx : x ∈ cube n) (j : Fin n)
    {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    Phase (M.exponential z (Function.update x j a))
      (M.exponential z (Function.update x j b)) (‖z‖ * (c * q)) := by
  apply (exp_phase _ _).mono
  have hdiff := M.abs_total_update_sub_le hq hx j hb ha
  apply (Complex.abs_im_le_norm _).trans
  have heq : z * (M.total (Function.update x j b) : ℂ) -
      z * (M.total (Function.update x j a) : ℂ) =
      z * ((M.total (Function.update x j b) - M.total (Function.update x j a) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left hdiff (norm_nonneg z)

/-- Every replacement path has a genuine real-potential mixture model on the
 full parameter interval; its changed scope has lost the frozen coordinate. -/
def Model.replacement (M : Model n m r c q) (j : Fin n)
    (A : Finset (Fin m)) (e : Fin m) {a b : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : Model n m r c q :=
  (M.freezeSet j A ha hb).mix (M.freezeSet j (insert e A) ha hb)
    (fun _ => rfl) t ht

lemma Model.replacement_total (M : Model n m r c q) (j : Fin n)
    (A : Finset (Fin m)) (e : Fin m) (he : e ∉ A) {a b : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (x : Fin n → ℝ) :
    (M.replacement j A e ha hb t ht).total x =
      (M.freezeSet j A ha hb).total x + t * M.delta j a b e x := by
  unfold Model.replacement
  rw [Model.total_mix]
  have hd := M.freezeSet_total_sub j A e he ha hb x
  change _ = (M.freezeSet j A ha hb).total x +
    t * (M.potential e (Function.update x j b) - M.potential e (Function.update x j a))
  rw [← hd]
  ring

@[simp] lemma Model.replacement_scope (M : Model n m r c q) (j : Fin n)
    (A : Finset (Fin m)) (e i : Fin m) {a b : ℝ} (ha) (hb) (t : ℝ) (ht) :
    (M.replacement j A e (a := a) (b := b) ha hb t ht).scope i = (M.scope i).erase j := rfl

end Paper08.ZeroFreeInduction
