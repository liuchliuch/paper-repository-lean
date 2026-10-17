import ELV.OraclePhase
import ELV.ReflectionWitness
import ELV.BitFlip
import ELV.FockWitness

/-! Real full-oracle witnesses obtained from the executed fixed line circuit.
The two state-generating calls per reflection and phase-to-bit factor cancel.
No cost is defined to be a numerical target. -/
noncomputable section
namespace ELV.Unrestricted
open ELV.Model ELV.Query ELV.Costs ELV.Stabilize
variable {n : ℕ} [NeZero n]

abbrev Times (n : ℕ) [NeZero n] := Fin (Model.phaseCircuit n).length
abbrev Controls (n : ℕ) [NeZero n] := Times n × ℕ

def phaseQueries (O : Nonbalanced n) : Times n → Line.Channel (Mspace n) :=
  Query.trace (lpCongr O.val.pulledReflection) (Model.phaseCircuit n)
    (WithLp.toLp 2 ((1 : ℂ),phaseCatalyst O))

def rawWitness (O : Nonbalanced n) : OracleQuerySpace n (Controls n) :=
  timeStack (fun i => reflectionWitness O.val (phaseQueries O i))

def witness (O : Nonbalanced n) : OracleQuerySpace n (Controls n) :=
  (Rescale.halfCoefficient : ℂ) • rawWitness O

lemma half_norm_sq : ‖(Rescale.halfCoefficient : ℂ)‖ ^ 2 = (1/2 : ℝ) := by
  simpa [Complex.norm_real,Real.norm_eq_abs,sq_abs] using Rescale.halfCoefficient_sq

lemma half_inner {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (v w : K) :
    inner ℂ ((Rescale.halfCoefficient : ℂ) • v) ((Rescale.halfCoefficient : ℂ) • w) =
      (1/2 : ℂ)*inner ℂ v w := by
  simp only [inner_smul_left,inner_smul_right,Complex.conj_ofReal]
  have hs : (Rescale.halfCoefficient : ℂ)*(Rescale.halfCoefficient : ℂ) = 1/2 := by
    rw [← pow_two,← Complex.ofReal_pow,Rescale.halfCoefficient_sq]
    norm_num
  rw [← mul_assoc,hs]

lemma raw_filter (Ox Oy : Nonbalanced n) :
    inner ℂ (rawWitness Ox) (rawWitness Oy) -
      inner ℂ (bidirectional (Controls n) Ox.val (rawWitness Ox))
        (bidirectional (Controls n) Oy.val (rawWitness Oy)) =
      ∑ i : Times n, (inner ℂ (phaseQueries Ox i) (phaseQueries Oy i) -
        inner ℂ (lpCongr Ox.val.pulledReflection (phaseQueries Ox i))
          (lpCongr Oy.val.pulledReflection (phaseQueries Oy i))) := by
  rw [rawWitness,rawWitness,bidirectional_timeStack,bidirectional_timeStack,timeStack_inner,timeStack_inner,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact reflectionWitness_filter Ox.val Oy.val _ _

lemma raw_norm_sq (O : Nonbalanced n) : ‖rawWitness O‖ ^ 2 =
    2*Query.cost (lpCongr O.val.pulledReflection) (Model.phaseCircuit n)
      (WithLp.toLp 2 ((1 : ℂ),phaseCatalyst O)) := by
  rw [rawWitness,timeStack_norm_sq]
  simp_rw [reflectionWitness_norm_sq]
  rw [← Finset.mul_sum]
  rfl

lemma phaseSign_bitSign (O : Nonbalanced n) : Line.phaseSign O.val.p = bitSign O.val.r := by
  change (if O.val.p < (1/2 : ℝ) then (1 : ℂ) else -1) =
    (-1 : ℂ)^((if O.val.p ≤ (1/2 : ℝ) then (0 : Fin 2) else 1).val)
  by_cases hl : O.val.p < 1/2
  · rw [if_pos hl,if_pos hl.le]
    norm_num
  · have hp : ¬ O.val.p ≤ 1/2 := by
      intro hh
      exact O.property (le_antisymm hh (le_of_not_gt hl))
    rw [if_neg hl,if_neg hp]
    norm_num

lemma phase_bit_gram (b c : Fin 2) :
    (if b=c then (0 : ℂ) else 1) =
      (1/2 : ℂ)*(inner ℂ (1 : ℂ) 1 - inner ℂ (bitSign b) (bitSign c)) := by
  fin_cases b <;> fin_cases c <;> norm_num [bitSign,RCLike.inner_apply]

/-- The witnesses satisfy the actual bidirectional full-oracle filter on
all nonbalanced completions at once, without restricting query rays. -/
theorem feasible : Query.Witness
    (fun O : Nonbalanced n => bidirectional (Controls n) O.val)
    (fun _ => publicBasis 0) (fun O => publicBasis O.val.r) witness := by
  intro Ox Oy
  rw [public_gram_difference,phase_bit_gram]
  change _ = inner ℂ ((Rescale.halfCoefficient : ℂ) • rawWitness Ox)
    ((Rescale.halfCoefficient : ℂ) • rawWitness Oy) -
      inner ℂ (bidirectional (Controls n) Ox.val ((Rescale.halfCoefficient : ℂ) • rawWitness Ox))
        (bidirectional (Controls n) Oy.val ((Rescale.halfCoefficient : ℂ) • rawWitness Oy))
  rw [map_smul,map_smul,half_inner,half_inner,← mul_sub,raw_filter]
  have ht := Query.adversary_identity (Model.phaseCircuit n)
    (fun O : Nonbalanced n => lpCongr O.val.pulledReflection) (fun _ => (1 : ℂ))
    (fun O => Line.phaseSign O.val.p) phaseCatalyst phase_exact Ox Oy
  change inner ℂ (1 : ℂ) 1 - inner ℂ (Line.phaseSign Ox.val.p) (Line.phaseSign Oy.val.p) =
    ∑ i : Times n, (inner ℂ (phaseQueries Ox i) (phaseQueries Oy i) -
      inner ℂ (lpCongr Ox.val.pulledReflection (phaseQueries Ox i))
        (lpCongr Oy.val.pulledReflection (phaseQueries Oy i))) at ht
  rw [phaseSign_bitSign Ox,phaseSign_bitSign Oy] at ht
  exact congrArg (fun z : ℂ => (1/2 : ℂ)*z) ht

/-- The actual witness norm is the actual line-circuit cost, with cancellation
of the two oracle directions against the 1/2 phase-to-bit factor. -/
theorem witness_norm_sq (O : Nonbalanced n) : ‖witness O‖ ^ 2 = 1/|1-2*O.val.p| := by
  rw [witness,norm_smul,mul_pow,half_norm_sq,raw_norm_sq,(phaseCatalyst_spec O).2.1]
  ring

end ELV.Unrestricted
