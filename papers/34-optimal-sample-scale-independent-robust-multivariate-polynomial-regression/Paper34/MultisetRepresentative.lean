import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith

/-!
# The multiset representative step of Corollary 3.4

All sums and cardinalities in this file are genuine `Multiset` sums and
cardinalities.  Repeated locations retain their multiplicities.  The witness
proof is unconditional.  The final norming bridge is explicitly conditional on
an L1 approximation estimate; it does not assert or assume a proof of Lemma 3.3.
-/

open Set MeasureTheory

namespace Paper34

/-- The arithmetic average of a function over a multiset, counting multiplicity. -/
noncomputable def multisetAverage {E : Type*} (A : Multiset E) (f : E → ℝ) : ℝ :=
  (A.map f).sum / (A.card : ℝ)

/-- A lower and an upper pointwise bound give the same bounds on a nonempty
multiset average; mapping and summing do not discard repeated observations. -/
theorem multisetAverage_mem_Icc {E : Type*} {A : Multiset E} (hA : A ≠ 0)
    {f : E → ℝ} {a b : ℝ} (hlo : ∀ x ∈ A, a ≤ f x)
    (hhi : ∀ x ∈ A, f x ≤ b) : multisetAverage A f ∈ Icc a b := by
  have hc : (0 : ℝ) < (A.card : ℝ) := Nat.cast_pos.mpr (Multiset.card_pos.mpr hA)
  have hl : (A.card : ℝ) * a ≤ (A.map f).sum := by
    have h := Multiset.card_nsmul_le_sum (s := A.map f) (a := a) (by
      intro v hv
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hv
      exact hlo x hx)
    simpa only [Multiset.card_map, nsmul_eq_mul] using h
  have hu : (A.map f).sum ≤ (A.card : ℝ) * b := by
    have h := Multiset.sum_le_card_nsmul (A.map f) b (by
      intro v hv
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hv
      exact hhi x hx)
    simpa only [Multiset.card_map, nsmul_eq_mul] using h
  constructor
  · exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hl)
  · exact (div_le_iff₀ hc).mpr (by simpa only [mul_comm] using hu)

/-- Every continuous real function on a compact preconnected cell takes its
average over every nonempty multiset of points in that cell. -/
theorem multiset_average_witness_of_compact_preconnected
    {E : Type*} [TopologicalSpace E] {C : Set E} {A : Multiset E} {f : E → ℝ}
    (hA : A ≠ 0) (hAC : ∀ x ∈ A, x ∈ C)
    (hcompact : IsCompact C) (hconnected : IsPreconnected C)
    (hf : ContinuousOn f C) :
    ∃ ξ ∈ C, f ξ = multisetAverage A f := by
  obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hA
  have hC : C.Nonempty := ⟨x, hAC x hx⟩
  obtain ⟨xmin, hxmin, hmin⟩ := hcompact.exists_isMinOn hC hf
  obtain ⟨xmax, hxmax, hmax⟩ := hcompact.exists_isMaxOn hC hf
  have havg : multisetAverage A f ∈ Icc (f xmin) (f xmax) :=
    multisetAverage_mem_Icc hA (fun x hx => hmin (hAC x hx))
      (fun x hx => hmax (hAC x hx))
  exact hconnected.intermediate_value hxmin hxmax hf havg

/-- The multiset-average witness on a compact convex real cell. -/
theorem multiset_average_witness_of_compact_convex
    {E : Type*} [AddCommGroup E] [TopologicalSpace E]
    [Module ℝ E] [ContinuousAdd E] [ContinuousSMul ℝ E]
    {C : Set E} {A : Multiset E} {f : E → ℝ}
    (hA : A ≠ 0) (hAC : ∀ x ∈ A, x ∈ C)
    (hcompact : IsCompact C) (hconvex : Convex ℝ C)
    (hf : ContinuousOn f C) :
    ∃ ξ ∈ C, f ξ = multisetAverage A f :=
  multiset_average_witness_of_compact_preconnected hA hAC hcompact
    hconvex.isPreconnected hf

/-- Representatives can be selected for an arbitrary family of nonempty
multisets.  This is one simultaneous existence statement; it imposes no
independence or coordinatewise-selection condition on the representatives. -/
theorem multiset_average_representatives_of_compact_preconnected
    {κ E : Type*} [TopologicalSpace E] (C : κ → Set E) (A : κ → Multiset E)
    (f : E → ℝ) (hA : ∀ j, A j ≠ 0) (hAC : ∀ j x, x ∈ A j → x ∈ C j)
    (hcompact : ∀ j, IsCompact (C j)) (hconnected : ∀ j, IsPreconnected (C j))
    (hf : ∀ j, ContinuousOn f (C j)) :
    ∃ ξ : κ → E, ∀ j, ξ j ∈ C j ∧ f (ξ j) = multisetAverage (A j) f := by
  have hw : ∀ j, ∃ x ∈ C j, f x = multisetAverage (A j) f := fun j =>
    multiset_average_witness_of_compact_preconnected (hA j) (hAC j)
      (hcompact j) (hconnected j) (hf j)
  exact ⟨fun j => Classical.choose (hw j), fun j => Classical.choose_spec (hw j)⟩

/-- The absolute value of a genuine multivariate polynomial takes its multiset
average at a point of every compact convex cell. -/
theorem mvPolynomial_abs_multiset_average_witness
    {ν : Type*} {C : Set (ν → ℝ)} {A : Multiset (ν → ℝ)}
    (q : MvPolynomial ν ℝ) (hA : A ≠ 0) (hAC : ∀ x ∈ A, x ∈ C)
    (hcompact : IsCompact C) (hconvex : Convex ℝ C) :
    ∃ ξ ∈ C, |MvPolynomial.eval ξ q| =
      multisetAverage A (fun x => |MvPolynomial.eval x q|) :=
  multiset_average_witness_of_compact_convex hA hAC hcompact hconvex
    q.continuous_eval.abs.continuousOn

/-- The polynomial multiset-average step of **Corollary 3.4**, simultaneously
for a family of cells and multisets, with all multiplicities retained. -/
theorem mvPolynomial_abs_multiset_representatives
    {κ ν : Type*} (C : κ → Set (ν → ℝ)) (A : κ → Multiset (ν → ℝ))
    (q : MvPolynomial ν ℝ) (hA : ∀ j, A j ≠ 0)
    (hAC : ∀ j x, x ∈ A j → x ∈ C j)
    (hcompact : ∀ j, IsCompact (C j)) (hconvex : ∀ j, Convex ℝ (C j)) :
    ∃ ξ : κ → (ν → ℝ), ∀ j, ξ j ∈ C j ∧
      |MvPolynomial.eval (ξ j) q| =
        multisetAverage (A j) (fun x => |MvPolynomial.eval x q|) :=
  multiset_average_representatives_of_compact_preconnected C A
    (fun x => |MvPolynomial.eval x q|) hA hAC hcompact
    (fun j => (hconvex j).isPreconnected)
    (fun _ => q.continuous_eval.abs.continuousOn)

/-- The reverse triangle inequality for the real L1 integrals of two actual
integrable functions.  This is the analytic bridge used after a step-function
representative has been identified. -/
theorem abs_l1_integral_difference_le
    {E : Type*} [MeasurableSpace E] {μ : Measure E} {f g : E → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    |(∫ x, |g x| ∂μ) - (∫ x, |f x| ∂μ)| ≤ ∫ x, |g x - f x| ∂μ := by
  calc
    |(∫ x, |g x| ∂μ) - (∫ x, |f x| ∂μ)| =
        |∫ x, |g x| - |f x| ∂μ| := by rw [integral_sub hg.abs hf.abs]
    _ ≤ ∫ x, |(|g x| - |f x|)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, |g x - f x| ∂μ :=
      integral_mono (hg.abs.sub hf.abs).abs (hg.sub hf).abs
        (fun x => abs_abs_sub_abs_le_abs_sub (g x) (f x))

/-- A scalar absolute-error estimate gives the two relative norming bounds. -/
theorem relative_norming_of_abs_error {Φ N ε : ℝ} (h : |Φ - N| ≤ ε * N) :
    (1 - ε) * N ≤ Φ ∧ Φ ≤ (1 + ε) * N := by
  rcases abs_le.mp h with ⟨hlo, hhi⟩
  constructor <;> nlinarith

/-- A **conditional bridge**, not a proof of Lemma 3.3: if an actual function
`g` approximates `f` in L1 to relative error `ε`, then its L1 integral satisfies
the relative norming bounds.  A proof of Lemma 3.3 must supply `happrox` for the
paper's representative step function. -/
theorem representative_relative_norming_conditional
    {E : Type*} [MeasurableSpace E] {μ : Measure E} {f g : E → ℝ} {ε : ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (happrox : (∫ x, |g x - f x| ∂μ) ≤ ε * (∫ x, |f x| ∂μ)) :
    (1 - ε) * (∫ x, |f x| ∂μ) ≤ (∫ x, |g x| ∂μ) ∧
      (∫ x, |g x| ∂μ) ≤ (1 + ε) * (∫ x, |f x| ∂μ) :=
  relative_norming_of_abs_error ((abs_l1_integral_difference_le hf hg).trans happrox)

end Paper34
