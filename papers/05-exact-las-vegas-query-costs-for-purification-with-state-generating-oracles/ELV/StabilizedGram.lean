import ELV.HilbertSum
import Mathlib.SetTheory.Cardinal.Arithmetic

noncomputable section
namespace ELV.Gram
open ELV.Stabilize

abbrev StabilizingIndex (I : Type*) := ℕ ⊕ I
abbrev StabilizingSpace (I : Type*) := lp (fun _ : StabilizingIndex I => ℂ) 2

/-- The added index has exactly the paper's cardinal `max(aleph0, dimHilbert V)`
when `I` indexes a Hilbert basis of `V`. No Hamel dimension is used. -/
theorem stabilizing_cardinal (I : Type*) :
    Cardinal.mk (StabilizingIndex I) = max Cardinal.aleph0 (Cardinal.mk I) := by
  simp only [StabilizingIndex, Cardinal.mk_sum, Cardinal.mk_nat, Cardinal.lift_aleph0, Cardinal.lift_id']
  exact Cardinal.add_eq_max le_rfl

/-- Standard Hilbert basis of the added square summable space. -/
def stabilizingBasis (I : Type*) : HilbertBasis (StabilizingIndex I) ℂ (StabilizingSpace I) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

/-- Embed the coordinate space of `V` into the `I` part of `ℕ ⊕ I`. -/
def coordinateEmbedding (I : Type*) : lp (fun _ : I => ℂ) 2 →ₗᵢ[ℂ] StabilizingSpace I :=
  (((stabilizingBasis I).orthonormal.comp Sum.inr Sum.inr_injective).orthogonalFamily).linearIsometry

variable {V I X : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Actual isometric embedding supplied by a Hilbert basis. -/
def ambientEmbedding (b : HilbertBasis I ℂ V) : V →ₗᵢ[ℂ] StabilizingSpace I :=
  (coordinateEmbedding I).comp b.repr.toLinearIsometry

instance embeddingRange_complete (b : HilbertBasis I ℂ V) :
    CompleteSpace (LinearMap.range (ambientEmbedding b).toLinearMap) := by
  exact IsClosed.completeSpace_coe
    (hs := (ambientEmbedding b).isometry.isClosedEmbedding.isClosed_range)

/-- Lemma 2.1: a single unitary on `V ⊕₂ ℓ²(max(aleph0,dimHilbert V))`.
The construction depends on the entire family; the resulting operator is fixed
for all instances and maps all specified generators simultaneously. -/
def stabilizedUnitary (bV : HilbertBasis I ℂ V) {a b : X → V} (h : EqualGram a b) :
    HilbertPair V (StabilizingSpace I) ≃ₗᵢ[ℂ] HilbertPair V (StabilizingSpace I) :=
  extendDouble (LinearMap.range (ambientEmbedding bV).toLinearMap)
    (ambientEmbedding bV).equivRange (doubleUnitary h)

theorem stabilizedUnitary_apply (bV : HilbertBasis I ℂ V)
    {a b : X → V} (h : EqualGram a b) (x : X) :
    stabilizedUnitary bV h (WithLp.toLp 2 (a x, (0 : StabilizingSpace I))) =
      WithLp.toLp 2 (b x, (0 : StabilizingSpace I)) := by
  exact extendDouble_apply _ _ _ _ _ (doubleUnitary_apply h x)

/-- Basis-free existential version, retaining the exact stabilization cardinal. -/
theorem stabilized_realization {a b : X → V} (h : EqualGram a b) :
    ∃ (I : Set V) (_bV : HilbertBasis I ℂ V)
      (U : HilbertPair V (StabilizingSpace I) ≃ₗᵢ[ℂ] HilbertPair V (StabilizingSpace I)),
      Cardinal.mk (StabilizingIndex I) = max Cardinal.aleph0 (Cardinal.mk I) ∧
      ∀ x, U (WithLp.toLp 2 (a x, (0 : StabilizingSpace I))) =
        WithLp.toLp 2 (b x, (0 : StabilizingSpace I)) := by
  obtain ⟨I, bV, _⟩ := exists_hilbertBasis ℂ V
  exact ⟨I, bV, stabilizedUnitary bV h, stabilizing_cardinal I, stabilizedUnitary_apply bV h⟩

/-- Every orthonormal family in a separable Hilbert space is countable. -/
theorem hilbertBasis_countable [TopologicalSpace.SeparableSpace V] (bV : HilbertBasis I ℂ V) :
    Countable I := by
  have hd : Pairwise (fun i j => Disjoint (Metric.ball (bV i) (1 / 2 : ℝ)) (Metric.ball (bV j) (1 / 2 : ℝ))) := by
    intro i j hij
    apply Metric.ball_disjoint_ball
    have hn : ‖bV i - bV j‖ ^ 2 = 2 := by
      rw [@norm_sub_sq ℂ, bV.orthonormal.norm_eq_one i, bV.orthonormal.norm_eq_one j,
        bV.orthonormal.inner_eq_zero hij]
      norm_num
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (bV i - bV j)]
  exact hd.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
    (fun i => ⟨bV i, Metric.mem_ball_self (by norm_num)⟩)

/-- Square summable coordinate space on a countable index is separable,
proved from the countable dense linear span of its standard Hilbert basis. -/
theorem stabilizingSpace_separable (I : Type*) [Countable I] :
    TopologicalSpace.SeparableSpace (StabilizingSpace I) := by
  apply TopologicalSpace.isSeparable_univ_iff.mp
  have hs := (Set.countable_range (stabilizingBasis I)).isSeparable.span (R := ℂ)
  have hc := hs.closure
  have heq : closure (Submodule.span ℂ (Set.range (stabilizingBasis I)) : Set (StabilizingSpace I))
      = Set.univ := by
    change (↑((Submodule.span ℂ (Set.range (stabilizingBasis I))).topologicalClosure) :
      Set (StabilizingSpace I)) = Set.univ
    rw [(stabilizingBasis I).dense_span]
    rfl
  rwa [heq] at hc

/-- The stabilization is separable whenever the original ambient space is
separable, independently of the cardinality of the family index `X`. -/
theorem separable_realization [TopologicalSpace.SeparableSpace V]
    {a b : X → V} (h : EqualGram a b) :
    ∃ (I : Set V) (_bV : HilbertBasis I ℂ V)
      (U : HilbertPair V (StabilizingSpace I) ≃ₗᵢ[ℂ] HilbertPair V (StabilizingSpace I)),
      TopologicalSpace.SeparableSpace (StabilizingSpace I) ∧
      ∀ x, U (WithLp.toLp 2 (a x, (0 : StabilizingSpace I))) =
        WithLp.toLp 2 (b x, (0 : StabilizingSpace I)) := by
  obtain ⟨I, bV, _⟩ := exists_hilbertBasis ℂ V
  letI : Countable I := hilbertBasis_countable bV
  exact ⟨I, bV, stabilizedUnitary bV h, stabilizingSpace_separable I,
    stabilizedUnitary_apply bV h⟩

/-- Full realization, including the separability clause for this same choice of basis. -/
theorem stabilized_realization_full {a b : X → V} (h : EqualGram a b) :
    ∃ (I : Set V) (_bV : HilbertBasis I ℂ V)
      (U : HilbertPair V (StabilizingSpace I) ≃ₗᵢ[ℂ] HilbertPair V (StabilizingSpace I)),
      Cardinal.mk (StabilizingIndex I) = max Cardinal.aleph0 (Cardinal.mk I) ∧
      (TopologicalSpace.SeparableSpace V → TopologicalSpace.SeparableSpace (StabilizingSpace I)) ∧
      ∀ x, U (WithLp.toLp 2 (a x, (0 : StabilizingSpace I))) =
        WithLp.toLp 2 (b x, (0 : StabilizingSpace I)) := by
  obtain ⟨I, bV, _⟩ := exists_hilbertBasis ℂ V
  refine ⟨I, bV, stabilizedUnitary bV h, stabilizing_cardinal I, ?_, stabilizedUnitary_apply bV h⟩
  intro hsep
  letI := hsep
  letI : Countable I := hilbertBasis_countable bV
  exact stabilizingSpace_separable I

end ELV.Gram
