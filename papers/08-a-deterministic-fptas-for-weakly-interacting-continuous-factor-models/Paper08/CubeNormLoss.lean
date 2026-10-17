import Paper08.CubeMarginal

/-! # Iterating genuine one-coordinate marginal norm bounds

The step premise is an internal inequality for actual marginal integrals.
The finite-cube nonvanishing induction obtains every such step from its
smaller-cardinality phase conclusion; no norm-loss certificate is a model input.
-/
noncomputable section
open scoped BigOperators
namespace Paper08.CubeNormLoss
open Integral CubeMarginal

/-- The one-coordinate consequence of a sector estimate. -/
def StepLower {n : ℕ} (S : Finset (Fin n)) (f : (Fin n → ℝ) → ℂ) (a : ℝ) : Prop :=
  ∀ U ⊆ S, ∀ j ∈ S, j ∉ U → ∀ x ∈ cube n,
    a*realAvg {j} (fun y => ‖avg U f y‖) x ≤ ‖avg (insert j U) f x‖

/-- Add a disjoint set of coordinates, preserving all intervening norm bounds. -/
theorem iterated {n : ℕ} {S : Finset (Fin n)} {f : (Fin n → ℝ) → ℂ}
    (hf : ContinuousOn f (cube n)) {a : ℝ} (ha : 0 ≤ a) (hstep : StepLower S f a)
    (U : Finset (Fin n)) (hU : U ⊆ S) (T : Finset (Fin n)) :
    T ⊆ S → Disjoint U T → ∀ x ∈ cube n,
      a^T.card*realAvg T (fun y => ‖avg U f y‖) x ≤ ‖avg (U∪T) f x‖ := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro hT hdis x hx
    simp only [Finset.card_empty,pow_zero,realAvg_empty,one_mul,Finset.union_empty,le_refl]
  | @insert j T hj ih =>
    intro hT hdis x hx
    have hTS : T ⊆ S := (Finset.subset_insert j T).trans hT
    have hUT : Disjoint U T := hdis.mono_right (Finset.subset_insert j T)
    have hjU : j ∉ U := fun hjU => Finset.disjoint_left.mp hdis hjU (Finset.mem_insert_self j T)
    have hjUT : j ∉ U∪T := by simpa only [Finset.mem_union,not_or] using And.intro hjU hj
    have hUS : U∪T ⊆ S := Finset.union_subset hU hTS
    have hleft : ContinuousOn (fun y => a^T.card*realAvg T (fun z => ‖avg U f z‖) y) (cube n) :=
      continuousOn_const.mul (continuousOn_realAvg T (continuousOn_avg U hf).norm)
    have hright : ContinuousOn (fun y => ‖avg (U∪T) f y‖) (cube n) :=
      (continuousOn_avg (U∪T) hf).norm
    have hmono := realAvg_mono {j} hleft hright (ih hTS hUT) hx
    have hmul := mul_le_mul_of_nonneg_left hmono ha
    have hjS : j ∈ S := hT (Finset.mem_insert_self j T)
    calc
      a^(insert j T).card*realAvg (insert j T) (fun y => ‖avg U f y‖) x =
          a*(a^T.card*realAvg {j} (realAvg T (fun y => ‖avg U f y‖)) x) := by
        rw [Finset.card_insert_of_notMem hj,realAvg_insert T j hj (continuousOn_avg U hf).norm hx]
        ring
      _ = a*realAvg {j} (fun y => a^T.card*realAvg T (fun z => ‖avg U f z‖) y) x := by
        rw [realAvg_const_mul]
      _ ≤ a*realAvg {j} (fun y => ‖avg (U∪T) f y‖) x := hmul
      _ ≤ ‖avg (insert j (U∪T)) f x‖ := hstep (U∪T) hUS j hjS hjUT x hx
      _ = ‖avg (U∪insert j T) f x‖ := by rw [Finset.union_insert]

/-- Integrate the coordinates in T last. Every norm loss is a proved
one-coordinate sector estimate, and the remaining expression is an actual
real expectation of the norm of the complementary marginal. -/
theorem subset {n : ℕ} {S T : Finset (Fin n)} {f : (Fin n → ℝ) → ℂ}
    (hf : ContinuousOn f (cube n)) {a : ℝ} (ha : 0 ≤ a) (hstep : StepLower S f a)
    (hT : T ⊆ S) {x : Fin n → ℝ} (hx : x ∈ cube n) :
    a^T.card*realAvg T (fun y => ‖avg (S\T) f y‖) x ≤ ‖avg S f x‖ := by
  have hd : Disjoint (S\T) T := Finset.disjoint_left.mpr fun _ ha hb => (Finset.mem_sdiff.mp ha).2 hb
  have hu : (S\T)∪T = S := by
    ext i
    by_cases hi : i ∈ T
    · simp [hi, hT hi]
    · simp [hi]
  simpa only [hu] using iterated hf ha hstep (S\T) Finset.sdiff_subset T hT hd x hx

end Paper08.CubeNormLoss
