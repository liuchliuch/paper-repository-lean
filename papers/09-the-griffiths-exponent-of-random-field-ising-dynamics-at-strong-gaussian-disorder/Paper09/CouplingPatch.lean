import Paper09.DisagreementMarks
import Paper09.LocalSimulation
import Paper09.BlockKernels

open Finset BigOperators Classical
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

namespace Paper09

namespace FinProb
variable {α : Type*} [Fintype α]

@[simp] theorem map_id (p : FinProb α) : p.map id = p := by
  apply ext_weights
  intro a
  simp [map]

end FinProb

private theorem patch_sum_four_swap {ι κ χ μ : Type*}
    [Fintype ι] [Fintype κ] [Fintype χ] [Fintype μ] (f : ι → κ → χ → μ → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, f i j k l) = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := by
  simpa only [Fintype.sum_prod_type] using
    (sum_comm (s := (univ : Finset (ι × κ))) (t := (univ : Finset (χ × μ)))
      (f := fun ij kl => f ij.1 ij.2 kl.1 kl.2))

namespace Coupling
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
variable {p : FinProb α} {q : FinProb β}

/-- Push both coordinates of an actual finite coupling through deterministic maps. -/
def map (c : Coupling p q) (f : α → γ) (g : β → δ) : Coupling (p.map f) (q.map g) where
  mass z w := ∑ a, ∑ b, if f a = z ∧ g b = w then c.mass a b else 0
  nonneg z w := sum_nonneg fun a _ => sum_nonneg fun b _ => by
    split_ifs <;> simp_all [c.nonneg]
  row z := by
    rw [sum_comm]
    change (∑ a, ∑ w, ∑ b, if f a = z ∧ g b = w then c.mass a b else 0) =
      ∑ a, if f a = z then p.w a else 0
    apply sum_congr rfl
    intro a _
    rw [sum_comm]
    by_cases ha : f a = z
    · simp [ha, c.row]
    · simp [ha]
  col w := by
    simp_rw [sum_comm (f := fun a b => if f a = _ ∧ g b = w then c.mass a b else 0)]
    rw [sum_comm]
    change (∑ b, ∑ z, ∑ a, if f a = z ∧ g b = w then c.mass a b else 0) =
      ∑ b, if g b = w then q.w b else 0
    apply sum_congr rfl
    intro b _
    rw [sum_comm]
    by_cases hb : g b = w
    · simp [hb, c.col]
    · simp [hb]

/-- Deterministic pushforward preserves the exact expected transformed cost. -/
theorem cost_map (c : Coupling p q) (f : α → γ) (g : β → δ) (d : γ → δ → ℝ) :
    (c.map f g).cost d = c.cost (fun a b => d (f a) (g b)) := by
  unfold cost map
  simp only [sum_mul]
  rw [patch_sum_four_swap]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  simp [ite_mul, ite_and]

/-- A nonzero pushed-forward coupling entry comes from a nonzero original entry. -/
theorem map_support (c : Coupling p q) (f : α → γ) (g : β → δ) (z : γ) (w : δ)
    (hm : (c.map f g).mass z w ≠ 0) :
    ∃ a b, f a = z ∧ g b = w ∧ c.mass a b ≠ 0 := by
  by_contra hn
  push_neg at hn
  apply hm
  apply sum_eq_zero
  intro a _
  apply sum_eq_zero
  intro b _
  by_cases h : f a = z ∧ g b = w
  · simp [h, hn a b h.1 h.2]
  · simp [h]

/-- The graph of a deterministic map is an actual coupling with its pushforward. -/
def graph (p : FinProb α) (f : α → β) : Coupling p (p.map f) where
  mass a b := if f a = b then p.w a else 0
  nonneg a b := by split_ifs <;> simp_all [p.nonneg]
  row a := by simp
  col b := rfl

theorem cost_graph (p : FinProb α) (f : α → β) (d : α → β → ℝ) :
    (graph p f).cost d = p.expect (fun a => d a (f a)) := by
  simp [cost, graph, FinProb.expect, ite_mul]

/-- Transport the specified marginals along equalities without changing any mass. -/
def retype {p' : FinProb α} {q' : FinProb β} (c : Coupling p q)
    (hp : p = p') (hq : q = q') : Coupling p' q' where
  mass := c.mass
  nonneg := c.nonneg
  row a := by rw [← hp]; exact c.row a
  col b := by rw [← hq]; exact c.col b

@[simp] theorem cost_retype {p' : FinProb α} {q' : FinProb β} (c : Coupling p q)
    (hp : p = p') (hq : q = q') (d : α → β → ℝ) :
    (c.retype hp hq).cost d = c.cost d := rfl

end Coupling

namespace CouplingPatch
variable {V : Type*} [Fintype V]

/-- Sample the first output once and patch its updated block into the second
frozen exterior. The supplied equality is the kernel's ordinary locality law. -/
def synchronousRow (K : Config V → FinProb (Config V)) (C : Finset V)
    (η ξ : Config V) (hlocal : (K η).map (BlockKernels.patch C ξ) = K ξ) :
    Coupling (K η) (K ξ) :=
  (Coupling.graph (K η) (BlockKernels.patch C ξ)).retype rfl hlocal

/-- Patching a common updated block preserves the original Hamming cost whenever
the starting configurations agree in the block and the sampled exterior is frozen. -/
theorem hamming_patch (C : Finset V) (η ξ ζ : Config V)
    (hC : ∀ x ∈ C, η x = ξ x) (hout : ∀ x, x ∉ C → ζ x = η x) :
    hammingR ζ (BlockKernels.patch C ξ ζ) = hammingR η ξ := by
  simp only [hammingR_eq_sum]
  apply sum_congr rfl
  intro x _
  by_cases hx : x ∈ C
  · simp [BlockKernels.patch, hx, hC x hx]
  · simp [BlockKernels.patch, hx, hout x hx]

/-- The explicitly constructed row coupling has exactly the input Hamming cost. -/
theorem cost_synchronousRow (K : Config V → FinProb (Config V)) (C : Finset V)
    (η ξ : Config V) (hlocal : (K η).map (BlockKernels.patch C ξ) = K ξ)
    (hfrozen : LocalSimulation.FrozenOutside C η (K η))
    (hC : ∀ x ∈ C, η x = ξ x) :
    (synchronousRow K C η ξ hlocal).cost hammingR = hammingR η ξ := by
  rw [synchronousRow, Coupling.cost_retype, Coupling.cost_graph]
  calc
    (K η).expect (fun ζ => hammingR ζ (BlockKernels.patch C ξ ζ)) =
        (K η).expect (fun _ => hammingR η ξ) := by
      unfold FinProb.expect
      apply sum_congr rfl
      intro ζ _
      dsimp only
      by_cases hz : (K η).w ζ = 0
      · simp [hz]
      · rw [hamming_patch C η ξ ζ hC (hfrozen ζ hz)]
    _ = _ := FinProb.expect_const _ _

/-- A local row cannot increase Hamming Wasserstein distance when both starts
agree on the kernel's dependence region. -/
theorem row_wasserstein_le (K : Config V → FinProb (Config V)) (C S : Finset V)
    (hCS : C ⊆ S) (η ξ : Config V)
    (hfrozen : LocalSimulation.FrozenOutside C η (K η))
    (hlocal : (K η).map (BlockKernels.patch C ξ) = K ξ)
    (hS : ∀ x ∈ S, η x = ξ x) :
    hammingWasserstein (K η) (K ξ) ≤ hammingR η ξ := by
  calc hammingWasserstein (K η) (K ξ) ≤ (synchronousRow K C η ξ hlocal).cost hammingR :=
      Wasserstein.le_cost hammingR_nonneg _
    _ = hammingR η ξ := cost_synchronousRow K C η ξ hlocal hfrozen (fun x hx => hS x (hCS hx))

/-- Mix the genuine synchronous row couplings on the support of a given input
coupling. Unsupported input pairs may use any actual coupling. -/
def synchronousBind (K : Config V → FinProb (Config V)) (C S : Finset V)
    (hlocal : ∀ η ξ, (∀ x ∈ S, η x = ξ x) → (K η).map (BlockKernels.patch C ξ) = K ξ)
    {p q : FinProb (Config V)} (c : Coupling p q) : Coupling (p.bind K) (q.bind K) :=
  c.bind K K (fun η ξ => if hS : ∀ x ∈ S, η x = ξ x then
    synchronousRow K C η ξ (hlocal η ξ hS) else Coupling.independent (K η) (K ξ))

/-- Exact preservation of the coupling cost under synchronous remote evolution. -/
theorem cost_synchronousBind (K : Config V → FinProb (Config V)) (C S : Finset V)
    (hCS : C ⊆ S) (hfrozen : ∀ η, LocalSimulation.FrozenOutside C η (K η))
    (hlocal : ∀ η ξ, (∀ x ∈ S, η x = ξ x) → (K η).map (BlockKernels.patch C ξ) = K ξ)
    {p q : FinProb (Config V)} (c : Coupling p q)
    (hsupport : ∀ η ξ, c.mass η ξ ≠ 0 → ∀ x ∈ S, η x = ξ x) :
    (synchronousBind K C S hlocal c).cost hammingR = c.cost hammingR := by
  unfold synchronousBind
  rw [Coupling.cost_bind]
  unfold Coupling.cost
  apply sum_congr rfl
  intro η _
  apply sum_congr rfl
  intro ξ _
  by_cases hc : c.mass η ξ = 0
  · simp [hc]
  · have hS := hsupport η ξ hc
    simp only [dif_pos hS]
    change c.mass η ξ * (synchronousRow K C η ξ (hlocal η ξ hS)).cost hammingR =
      c.mass η ξ * hammingR η ξ
    rw [cost_synchronousRow K C η ξ (hlocal η ξ hS) (hfrozen η) (fun x hx => hS x (hCS hx))]

/-- The resulting output laws have Wasserstein cost bounded by the chosen
actual input coupling, without assuming an optimal coupling exists. -/
theorem bind_wasserstein_le_cost (K : Config V → FinProb (Config V)) (C S : Finset V)
    (hCS : C ⊆ S) (hfrozen : ∀ η, LocalSimulation.FrozenOutside C η (K η))
    (hlocal : ∀ η ξ, (∀ x ∈ S, η x = ξ x) → (K η).map (BlockKernels.patch C ξ) = K ξ)
    {p q : FinProb (Config V)} (c : Coupling p q)
    (hsupport : ∀ η ξ, c.mass η ξ ≠ 0 → ∀ x ∈ S, η x = ξ x) :
    hammingWasserstein (p.bind K) (q.bind K) ≤ c.cost hammingR := by
  calc hammingWasserstein (p.bind K) (q.bind K) ≤ (synchronousBind K C S hlocal c).cost hammingR :=
      Wasserstein.le_cost hammingR_nonneg _
    _ = c.cost hammingR := cost_synchronousBind K C S hCS hfrozen hlocal c hsupport

/-- When every supported pair agrees on the local dependence region, passing
both input laws through the remote local kernel is Wasserstein nonexpansive. -/
theorem bind_wasserstein_le (K : Config V → FinProb (Config V)) (C S : Finset V)
    (hCS : C ⊆ S) (hfrozen : ∀ η, LocalSimulation.FrozenOutside C η (K η))
    (hlocal : ∀ η ξ, (∀ x ∈ S, η x = ξ x) → (K η).map (BlockKernels.patch C ξ) = K ξ)
    {p q : FinProb (Config V)}
    (hsupport : ∀ η ξ, p.w η ≠ 0 → q.w ξ ≠ 0 → ∀ x ∈ S, η x = ξ x) :
    hammingWasserstein (p.bind K) (q.bind K) ≤ hammingWasserstein p q := by
  apply Wasserstein.lower_bound
  intro c
  apply bind_wasserstein_le_cost K C S hCS hfrozen hlocal c
  intro η ξ hc
  exact hsupport η ξ (fun hp => hc (c.mass_eq_zero_of_row hp ξ))
    (fun hq => hc (c.mass_eq_zero_of_col hq η))

end CouplingPatch
end Paper09
