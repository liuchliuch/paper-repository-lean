import Paper26.CollectiveStageRoutine
import Paper26.CollectiveSubmatrixRoutine
import Paper26.CollectivePadding

/-!
# Uniform high-confidence collective stage families

The original normalized OW existence input supplies each actual physical
submatrix experiment through the proved Proposition5.5. All experiments are
chosen before unknown inputρ. Their different copy counts are natively padded
to one common macro budget, then passed to the measurable moving-basis stage.
No source success conclusion is an external field or protocol premise.
-/
noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal
namespace Paper26.CollectiveStageFamily
open MeasureTheory QuantumModel ContinuousPOVM CollectiveFiltering ShellAccounting
open CollectiveStageRoutine ContinuousSubmatrixLearning

local instance matrixMeasurableSpace (m n : Type*) : MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
local instance : MeasurableSpace (Finset ι) := ⊤

/-- This proposition records a property of actual branch data; it is proved
below from the original OW theorem and contains no external assumption. -/
def BranchSuccess {n : ℕ} {S : Finset ι} (B : Branch ι n S) (W η b : ℝ) : Prop :=
  ∀ σ : Density (Active S ⊕ Inactive S), headMass σ ≤ W →
    MeasurableSet {y | frobeniusSq (B.output y-headBlock σ.matrix) ≤ η} ∧
      ENNReal.ofReal (1-b) ≤ B.measurement.outcomeMeasure (TensorCopies.density σ n)
        {y | frobeniusSq (B.output y-headBlock σ.matrix) ≤ η}

def BranchCost {n : ℕ} {S : Finset ι} (_B : Branch ι n S) (W η b : ℝ) : Prop :=
  if W^2 ≤ η then n=0 else (n : ℝ) ≤
    CollectiveSubmatrixRoutine.universalConstant*((Fintype.card (Active S) : ℝ)*W/η)*Real.log (1/b)

/-- Every actual finite active block has a physical high-confidence routine.
An empty active block uses the zero-copy identity experiment. -/
theorem exists_branch (O : ∀ S : Finset ι, S.Nonempty → FrobeniusLearning.OWFrobeniusInput (Active S))
    (S : Finset ι) {W η b : ℝ} (hW : 0 ≤ W) (hW1 : W ≤ 1) (hη : 0 < η)
    (hb : 0 < b) (hbhalf : b < 1/2) :
    ∃ d : Σ n : ℕ, Branch ι n S, BranchSuccess d.2 W η b ∧ BranchCost d.2 W η b := by
  classical
  by_cases hS : S.Nonempty
  · letI : Nonempty (Active S) := ⟨⟨hS.choose,hS.choose_spec⟩⟩
    obtain ⟨n,Ω,mΩ,M,T,hT,hP,hstat,hcost⟩ :=
      CollectiveSubmatrixRoutine.proposition_5_5 (β := Inactive S) (O S hS) hW hW1 hη hb hbhalf
    letI := mΩ
    let B : Branch ι n S := {
      Outcome := Ω
      outcomeMeasurable := mΩ
      measurement := M
      output := T
      measurable_output := hT
      output_psd := hP }
    exact ⟨⟨n,B⟩,hstat,hcost⟩
  · let B : Branch ι 0 S := {
      Outcome := Unit
      outcomeMeasurable := inferInstance
      measurement := unitMeasurement (Fin 0 → (Active S ⊕ Inactive S))
      output := fun _ => 0
      measurable_output := measurable_const
      output_psd := fun _ => Matrix.PosSemidef.zero }
    refine ⟨⟨0,B⟩,?_,?_⟩
    · intro σ _
      have hR : headBlock σ.matrix = 0 := by
        ext i j
        exact False.elim (hS ⟨i.val,i.property⟩)
      have he : {y : B.Outcome | frobeniusSq (B.output y-headBlock σ.matrix) ≤ η} = Set.univ := by
        ext y
        simp [B,hR,frobeniusSq,hη.le]
      rw [he]
      refine ⟨MeasurableSet.univ,?_⟩
      rw [measure_univ]
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (show 1-b ≤ 1 by linarith)
    · unfold BranchCost
      split_ifs
      · rfl
      · simp only [Nat.cast_zero]
        have hc : 0 ≤ CollectiveSubmatrixRoutine.universalConstant :=
          CollectiveSubmatrixRoutine.universalConstant_pos.le
        have hl : 0 ≤ Real.log (1/b) := by
          apply Real.log_nonneg
          apply (le_div_iff₀ hb).mpr
          linarith
        positivity

/-- A chosen entire physical branch. The choice has no unknown input-state
argument, and its properties are supplied by exists_branch. -/
def chosen (O : ∀ S : Finset ι, S.Nonempty → FrobeniusLearning.OWFrobeniusInput (Active S))
    (S : Finset ι) {W η b : ℝ} (hW : 0 ≤ W) (hW1 : W ≤ 1) (hη : 0 < η)
    (hb : 0 < b) (hbhalf : b < 1/2) : Σ n : ℕ, Branch ι n S :=
  Classical.choose (exists_branch O S hW hW1 hη hb hbhalf)

theorem chosen_success (O : ∀ S : Finset ι, S.Nonempty → FrobeniusLearning.OWFrobeniusInput (Active S))
    (S : Finset ι) {W η b : ℝ} (hW : 0 ≤ W) (hW1 : W ≤ 1) (hη : 0 < η)
    (hb : 0 < b) (hbhalf : b < 1/2) :
    BranchSuccess (chosen O S hW hW1 hη hb hbhalf).2 W η b :=
  (Classical.choose_spec (exists_branch O S hW hW1 hη hb hbhalf)).1

theorem chosen_cost (O : ∀ S : Finset ι, S.Nonempty → FrobeniusLearning.OWFrobeniusInput (Active S))
    (S : Finset ι) {W η b : ℝ} (hW : 0 ≤ W) (hW1 : W ≤ 1) (hη : 0 < η)
    (hb : 0 < b) (hbhalf : b < 1/2) :
    BranchCost (chosen O S hW hW1 hη hb hbhalf).2 W η b :=
  (Classical.choose_spec (exists_branch O S hW hW1 hη hb hbhalf)).2

/-- Padding is a physical tensor identity extension; its exact Born law is
proved in CollectivePadding rather than assumed by this stage family. -/
def padBranch {n N : ℕ} {S : Finset ι} (h : n ≤ N) (B : Branch ι n S) : Branch ι N S where
  Outcome := B.Outcome
  outcomeMeasurable := B.outcomeMeasurable
  measurement := CollectivePadding.padTo h B.measurement
  output := B.output
  measurable_output := B.measurable_output
  output_psd := B.output_psd

theorem padBranch_success {n N : ℕ} {S : Finset ι} (h : n ≤ N) (B : Branch ι n S)
    {W η b : ℝ} (hB : BranchSuccess B W η b) : BranchSuccess (padBranch h B) W η b := by
  intro σ hσ
  obtain ⟨hE,hp⟩ := hB σ hσ
  refine ⟨hE,?_⟩
  change ENNReal.ofReal (1-b) ≤
    (CollectivePadding.padTo h B.measurement).outcomeMeasure (TensorCopies.density σ N) _
  rw [CollectivePadding.padTo_outcomeMeasure]
  exact hp

section UniformBudget
variable (O : ∀ S : Finset ι, S.Nonempty → FrobeniusLearning.OWFrobeniusInput (Active S))
    {W η b : ℝ} (hW : 0 ≤ W) (hW1 : W ≤ 1) (hη : 0 < η)
    (hb : 0 < b) (hbhalf : b < 1/2)

def copyBound : ℝ := CollectiveSubmatrixRoutine.universalConstant *
  ((Fintype.card ι : ℝ)*W/η)*Real.log (1/b)

def macroCopies : ℕ := ⌈copyBound (ι := ι) (W := W) (η := η) (b := b)⌉₊

include hb hbhalf in
lemma log_nonneg : 0 ≤ Real.log (1/b) := by
  apply Real.log_nonneg
  apply (le_div_iff₀ hb).mpr
  linarith

include hW hη hb hbhalf in
lemma copyBound_nonneg : 0 ≤ copyBound (ι := ι) (W := W) (η := η) (b := b) := by
  have hC := CollectiveSubmatrixRoutine.universalConstant_pos.le
  have hl := log_nonneg hb hbhalf
  unfold copyBound
  positivity

/-- Every chosen original routine fits the common ambient-dimensional bound,
with no multiplicative number-of-subsets factor. -/
lemma chosen_count_le_bound (S : Finset ι) :
    ((chosen O S hW hW1 hη hb hbhalf).1 : ℝ) ≤
      copyBound (ι := ι) (W := W) (η := η) (b := b) := by
  have hc := chosen_cost O S hW hW1 hη hb hbhalf
  unfold BranchCost at hc
  by_cases hz : W^2 ≤ η
  · rw [if_pos hz] at hc
    rw [hc, Nat.cast_zero]
    exact copyBound_nonneg hW hη hb hbhalf
  · rw [if_neg hz] at hc
    apply hc.trans
    have hcard : (Fintype.card (Active S) : ℝ) ≤ Fintype.card ι := by
      exact_mod_cast (show Fintype.card (Active S) ≤ Fintype.card ι by
        simpa only [Active, Fintype.card_coe] using Finset.card_le_univ S)
    unfold copyBound
    apply mul_le_mul_of_nonneg_right _ (log_nonneg hb hbhalf)
    apply mul_le_mul_of_nonneg_left _ CollectiveSubmatrixRoutine.universalConstant_pos.le
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcard hW) hη.le

lemma chosen_count_le_macro (S : Finset ι) :
    (chosen O S hW hW1 hη hb hbhalf).1 ≤ macroCopies (ι := ι) (W := W) (η := η) (b := b) := by
  have hc := (chosen_count_le_bound O hW hW1 hη hb hbhalf S).trans
    (Nat.le_ceil (copyBound (ι := ι) (W := W) (η := η) (b := b)))
  exact_mod_cast hc

/-- The complete physical branch family padded to ANY sufficiently large
common macro budgetN. It is chosen independently ofρ,U and activeS. -/
def family (N : ℕ)
    (hN : macroCopies (ι := ι) (W := W) (η := η) (b := b) ≤ N)
    (S : Finset ι) : Branch ι N S :=
  padBranch ((chosen_count_le_macro O hW hW1 hη hb hbhalf S).trans hN)
    (chosen O S hW hW1 hη hb hbhalf).2

theorem family_success (N : ℕ)
    (hN : macroCopies (ι := ι) (W := W) (η := η) (b := b) ≤ N) (S : Finset ι) :
    BranchSuccess (family O hW hW1 hη hb hbhalf N hN S) W η b :=
  padBranch_success _ _ (chosen_success O S hW hW1 hη hb hbhalf)

/-- Source Prop5.5's genuine high-confidence guarantee as a native moving-
active-set/unitary Bornkernel bound, for the one common padded macro budget. -/
theorem conditional_success (N : ℕ)
    (hN : macroCopies (ι := ι) (W := W) (η := η) (b := b) ≤ N)
    (h : Control (ι := ι)) (ρ : Density ι)
    (hmass : headMass (splitState h.1 h.2 ρ) ≤ W) :
    let B := family O hW hW1 hη hb hbhalf N hN
    ENNReal.ofReal (1-b) ≤ (step B).bornKernel (TensorCopies.density ρ N) h
      {y | frobeniusSq ((estimateFamily B y h.1).val - compressedBlock h.1 h.2 ρ) ≤ η} := by
  let B := family O hW hW1 hη hb hbhalf N hN
  let σ := splitState h.1 h.2 ρ
  let E : Set ((B h.1).Outcome) :=
    {u | frobeniusSq ((B h.1).output u - compressedBlock h.1 h.2 ρ) ≤ η}
  have hE : MeasurableSet E := measurableSet_le
    (MatrixAmplification.measurable_error _ (B h.1).measurable_output _) measurable_const
  have hp := (family_success O hW hW1 hη hb hbhalf N hN h.1 σ hmass).2
  change ENNReal.ofReal (1-b) ≤ (step B).bornKernel (TensorCopies.density ρ N) h
    (Function.eval h.1 ⁻¹' E)
  rw [branch_event B h ρ E hE]
  simpa only [σ, splitState_headBlock] using hp

end UniformBudget

end Paper26.CollectiveStageFamily
