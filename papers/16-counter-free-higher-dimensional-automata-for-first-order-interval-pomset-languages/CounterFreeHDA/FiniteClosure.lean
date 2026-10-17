import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace CounterFreeHDA.Effective
universe u
variable {E : Type u} [Fintype E] [DecidableEq E]
    (R : E → E → Prop) [DecidableRel R] (seed : Finset E)

def expand (S : Finset E) : Finset E := S ∪ Finset.univ.filter (fun y => ∃ x ∈ S, R x y)
def iterate : ℕ → Finset E
  | 0 => seed
  | n+1 => expand R (iterate n)

theorem iterate_subset (n : ℕ) : iterate R seed n ⊆ iterate R seed (n+1) := Finset.subset_union_left

theorem equality_propagates {n : ℕ} (h : iterate R seed n = iterate R seed (n+1)) :
    iterate R seed (n+1) = iterate R seed (n+2) := congrArg (expand R) h

theorem strict_card {n : ℕ} (h : iterate R seed n ≠ iterate R seed (n+1)) :
    (iterate R seed n).card < (iterate R seed (n+1)).card := by
  apply Finset.card_lt_card
  exact (iterate_subset R seed n).ssubset_of_ne h

theorem card_growth (n : ℕ) (h : iterate R seed n ≠ iterate R seed (n+1)) :
    n < (iterate R seed (n+1)).card := by
  induction n with
  | zero => have hc := strict_card R seed h; omega
  | succ n ih =>
    have hp : iterate R seed n ≠ iterate R seed (n+1) := fun he => h (equality_propagates R seed he)
    have hc := strict_card R seed h
    have hi := ih hp
    omega

/-- After at most the number of states, finite forward closure is saturated. -/
theorem iterate_fixed : iterate R seed (Fintype.card E) = iterate R seed (Fintype.card E+1) := by
  by_contra h
  have hg := card_growth R seed _ h
  have hb := Finset.card_le_card (Finset.subset_univ (iterate R seed (Fintype.card E+1)))
  simp only [Finset.card_univ] at hb
  omega

def closure : Finset E := iterate R seed (Fintype.card E)

theorem seed_subset : seed ⊆ closure R seed := by
  have hi : ∀ n, seed ⊆ iterate R seed n := by
    intro n
    induction n with
    | zero => exact fun _ h => h
    | succ n ih => exact ih.trans (iterate_subset R seed n)
  exact hi _

theorem closure_step {x y : E} (hx : x ∈ closure R seed) (hxy : R x y) : y ∈ closure R seed := by
  rw [closure,iterate_fixed R seed]
  exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,x,hx,hxy⟩)

theorem closure_least (S : Set E) (hs : ∀ x ∈ seed, x ∈ S)
    (hstep : ∀ x ∈ S, ∀ y, R x y → y ∈ S) : ∀ x ∈ closure R seed, x ∈ S := by
  have hi : ∀ n, ∀ x ∈ iterate R seed n, x ∈ S := by
    intro n
    induction n with
    | zero => exact hs
    | succ n ih =>
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact ih x hx
      · obtain ⟨_,y,hy,hyx⟩ := Finset.mem_filter.mp hx
        exact hstep y (ih y hy) x hyx
  exact hi _

end CounterFreeHDA.Effective
