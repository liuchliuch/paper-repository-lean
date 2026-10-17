import Paper36.BorelAlgorithm
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! Appendix A.2: actual feasible graphs and exact Borel planning selectors.

The sole external input is a general compact-section measurable maximum
theorem, unrelated to kernels, risk or planning. It is the usual consequence
of Arsenin--Kunugui Borel uniformization (Kechris, Classical Descriptive Set
Theory, Springer GTM 156, 1995, chapter "Uniformization Theorems", pp. 120--128,
DOI 10.1007/978-1-4612-4190-4_18) and the measurable maximum theorem
(Aliprantis--Border, Infinite Dimensional Analysis, third edition, 2006,
chapter "Measurable correspondences", pp. 591--620,
DOI 10.1007/3-540-29587-9_18). These book/chapter identities were checked
against the publisher's primary pages; unverified theorem numbers are omitted.
The source invokes this ingredient at Appendix A.2,
[A1.SS2.p1]/[A1.Ex1], without a numbered bibliography citation there.

For a Borel graph with nonempty compact sections, Arsenin--Kunugui gives
measurability of open-hit sets (open subsets of compact metrizable sections
are sigma compact). The measurable maximum theorem then gives the selector
contract below. No P36 oracle, risk minimization or feasibility assertion is
part of that external contract. -/
namespace Paper36.Selection
open Set MeasureTheory Paper36.Regularity Paper36.Nested
noncomputable section
universe u

/-- A general published measurable-maximum ingredient. All spaces, graphs,
sections and objectives are universally quantified; no planning data occur. -/
structure CompactSectionMaximum : Prop where
  maximize : ∀ {X Y : Type u} [MeasurableSpace X] [StandardBorelSpace X]
      [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
      (Γ : X → Set Y) (f : X × Y → ℝ),
    MeasurableSet {p : X × Y | p.2 ∈ Γ p.1} →
    (∀ x, IsCompact (Γ x)) → (∀ x, (Γ x).Nonempty) →
    Measurable f → (∀ x, Continuous (fun y => f (x,y))) →
    ∃ σ : X → Y, Measurable σ ∧ ∀ x,
      σ x ∈ Γ x ∧ ∀ y ∈ Γ x, f (x,y) ≤ f (x,σ x)

variable {S A : Type u} [Fintype S] [Fintype A]

local instance law_polish {I : Type u} [Fintype I] : PolishSpace (Law I) :=
  (isClosed_stdSimplex I).polishSpace

local instance policy_nonempty [Nonempty A] : Nonempty (Policy S A) :=
  ⟨fun _ _ => Nested.pure (Classical.arbitrary A)⟩

local instance kernelPolicy_opens : OpensMeasurableSpace (Kernel S A × Policy S A) :=
  @Prod.opensMeasurableSpace _ _ _ _ _ _ inferInstance inferInstance inferInstance

/-- The original feasible-policy correspondence, with arbitrary policies
outside Q so that a globally defined Borel selector can be returned. -/
def feasible (α τ : ℝ) (c : ℕ → S → A → ℝ) (H : ℕ) (s₁ : S)
    (Q : Set (Kernel S A)) (q : Kernel S A) : Set (Policy S A) :=
  {π | q ∈ Q → risk α c π q H 0 s₁ ≤ τ}

lemma feasible_on_support (α τ : ℝ) (c : ℕ → S → A → ℝ) (H : ℕ) (s₁ : S)
    (Q : Set (Kernel S A)) {q : Kernel S A} (hq : q ∈ Q) :
    feasible α τ c H s₁ Q q = {π | risk α c π q H 0 s₁ ≤ τ} := by
  ext π
  simp [feasible, hq]

/-- The actual risk feasibility graph on the source's closed model support. -/
theorem feasible_graph_closed (α τ : ℝ) (c : ℕ → S → A → ℝ)
    (H : ℕ) (s₁ : S) :
    IsClosed {p : Kernel S A × Policy S A | risk α c p.2 p.1 H 0 s₁ ≤ τ} := by
  exact isClosed_le ((continuous_risk α c H 0 s₁).comp
    (continuous_snd.prodMk continuous_fst)) continuous_const

/-- Extending the source correspondence off its support preserves a Borel graph. -/
theorem feasible_graph_measurable (α τ : ℝ) (c : ℕ → S → A → ℝ)
    (H : ℕ) (s₁ : S) (Q : Set (Kernel S A)) (hQ : IsClosed Q) :
    MeasurableSet {p : Kernel S A × Policy S A | p.2 ∈ feasible α τ c H s₁ Q p.1} := by
  have houtside : MeasurableSet {p : Kernel S A × Policy S A | p.1 ∉ Q} :=
    (hQ.measurableSet.preimage measurable_fst).compl
  have hinside := (feasible_graph_closed α τ c H s₁).measurableSet
  convert houtside.union hinside using 1
  ext p
  simp [feasible, or_iff_not_imp_left]

/-- Every actual feasible section is compact, including the harmless off-support extension. -/
theorem feasible_section_compact (α τ : ℝ) (c : ℕ → S → A → ℝ)
    (H : ℕ) (s₁ : S) (Q : Set (Kernel S A)) (q : Kernel S A) :
    IsCompact (feasible α τ c H s₁ Q q) := by
  by_cases hq : q ∈ Q
  · rw [feasible_on_support α τ c H s₁ Q hq]
    exact (isClosed_le ((continuous_risk α c H 0 s₁).comp
      (continuous_id.prodMk continuous_const)) continuous_const).isCompact
  · have heq : feasible α τ c H s₁ Q q = Set.univ := by ext π; simp [feasible, hq]
    rw [heq]
    exact isCompact_univ

variable [Nonempty A]

/-- Strict feasibility provides nonempty sections from an actual minimum-risk policy. -/
theorem feasible_section_nonempty (α τ : ℝ) (c : ℕ → S → A → ℝ)
    (H : ℕ) (s₁ : S) (Q : Set (Kernel S A))
    (hstrict : ∀ q ∈ Q, minimumRisk α c H 0 s₁ q < τ) (q : Kernel S A) :
    (feasible α τ c H s₁ Q q).Nonempty := by
  obtain ⟨π,hπ⟩ := exists_minimumRisk α c H 0 s₁ q
  refine ⟨π, ?_⟩
  intro hq
  exact hπ.symm.le.trans (hstrict q hq).le

/-- The general theorem selects an actual exact minimum-risk source policy. -/
theorem exists_borel_calibration (external : CompactSectionMaximum.{u})
    (α : ℝ) (c : ℕ → S → A → ℝ) (H : ℕ) (s₁ : S) :
    ∃ σ : Kernel S A → Policy S A, Measurable σ ∧
      ∀ q, risk α c (σ q) q H 0 s₁ = minimumRisk α c H 0 s₁ q := by
  have hf : Continuous (fun p : Kernel S A × Policy S A => -risk α c p.2 p.1 H 0 s₁) :=
    ((continuous_risk α c H 0 s₁).comp (continuous_snd.prodMk continuous_fst)).neg
  obtain ⟨σ,hσ,hs⟩ := external.maximize (fun _ : Kernel S A => (Set.univ : Set (Policy S A)))
    (fun p => -risk α c p.2 p.1 H 0 s₁) MeasurableSet.univ
    (fun _ => isCompact_univ) (fun _ => Set.univ_nonempty) hf.measurable
    (fun q => hf.comp (continuous_const.prodMk continuous_id))
  refine ⟨σ,hσ,fun q => ?_⟩
  obtain ⟨π,hπ⟩ := exists_minimumRisk α c H 0 s₁ q
  have hle : risk α c (σ q) q H 0 s₁ ≤ risk α c π q H 0 s₁ := by
    have h := (hs q).2 π (Set.mem_univ π)
    linarith
  have hmin : minimumRisk α c H 0 s₁ q ≤ risk α c (σ q) q H 0 s₁ := by
    unfold minimumRisk
    apply csInf_le
    · exact (isCompact_univ.image ((continuous_risk α c H 0 s₁).comp
        (continuous_id.prodMk continuous_const))).bddBelow
    · exact Set.mem_image_of_mem _ (Set.mem_univ _)
  linarith

/-- The actual constrained risk graph and ordinary reward, rather than a
planning-oracle assertion, instantiate the general measurable maximum theorem. -/
theorem exists_borel_exploitation (external : CompactSectionMaximum.{u})
    (α τ : ℝ) (c r : ℕ → S → A → ℝ) (H : ℕ) (s₁ : S)
    (Q : Set (Kernel S A)) (hQ : IsClosed Q)
    (hstrict : ∀ q ∈ Q, minimumRisk α c H 0 s₁ q < τ) :
    ∃ σ : Kernel S A → Policy S A, Measurable σ ∧
      ∀ q ∈ Q, risk α c (σ q) q H 0 s₁ ≤ τ ∧
        ∀ π, risk α c π q H 0 s₁ ≤ τ →
          reward r π q H 0 s₁ ≤ reward r (σ q) q H 0 s₁ := by
  have hf : Continuous (fun p : Kernel S A × Policy S A => reward r p.2 p.1 H 0 s₁) :=
    (continuous_reward r H 0 s₁).comp (continuous_snd.prodMk continuous_fst)
  obtain ⟨σ,hσ,hs⟩ := external.maximize (feasible α τ c H s₁ Q)
    (fun p => reward r p.2 p.1 H 0 s₁) (feasible_graph_measurable α τ c H s₁ Q hQ)
    (feasible_section_compact α τ c H s₁ Q)
    (feasible_section_nonempty α τ c H s₁ Q hstrict) hf.measurable
    (fun q => hf.comp (continuous_const.prodMk continuous_id))
  refine ⟨σ,hσ,fun q hq => ⟨(hs q).1 hq,fun π hπ => ?_⟩⟩
  exact (hs q).2 π (fun _ => hπ)

/-- Appendix A.2: existence of the exact Borel oracle protocol from a general
published selection theorem and the actual source continuity/feasibility facts. -/
theorem exists_borel_oracles (external : CompactSectionMaximum.{u})
    (α τ : ℝ) (c r : ℕ → S → A → ℝ) (H : ℕ) (s₁ : S)
    (Q : Set (Kernel S A)) (hQ : IsClosed Q)
    (hstrict : ∀ q ∈ Q, minimumRisk α c H 0 s₁ q < τ) :
    Nonempty (BorelAlgorithm.BorelOracles α c r H s₁ τ Q) := by
  obtain ⟨cal,hcal,hcalExact⟩ := exists_borel_calibration external α c H s₁
  obtain ⟨exp,hexp,hexpExact⟩ := exists_borel_exploitation external α τ c r H s₁ Q hQ hstrict
  exact ⟨{ calibration := cal
           exploitation := exp
           cal_exact := fun q _ => hcalExact q
           exp_feasible := fun q hq => (hexpExact q hq).1
           exp_optimal := fun q hq => (hexpExact q hq).2
           measurable_calibration := hcal
           measurable_exploitation := hexp }⟩

end
end Paper36.Selection
