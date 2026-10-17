import ELV.PhaseToBit
import ELV.QueryRequery
import ELV.PublicCoordinates
import ELV.UnrestrictedUpper

/-! The original four-query purifier: known public Hadamards, the fixed
line walk, and two actual O/O-inverse calls for each pulled reflection. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
namespace ELV.FourQuery
open ELV.Model ELV.Query ELV.Costs ELV.Stabilize ELV.Hilbert
variable {n : ℕ} [NeZero n]

abbrev Channel (n : ℕ) := Line.Channel (Mspace n)
abbrev PrivateSpace (n : ℕ) [NeZero n] := HilbertPair (PhasePrivate n) (Channel n)
abbrev BitSpace (n : ℕ) [NeZero n] := HilbertPair ℂ (HilbertPair ℂ (PhasePrivate n))

def regroup (n : ℕ) [NeZero n] : HilbertPair (BitSpace n) (Channel n) ≃ₗᵢ[ℂ]
    HilbertPair Public (PrivateSpace n) :=
  (pairCongr (pairAssoc (𝕜:=ℂ) (E:=ℂ) (F:=ℂ) (G:=PhasePrivate n)).symm
    (LinearIsometryEquiv.refl ℂ (Channel n))).trans
    ((pairAssoc (𝕜:=ℂ) (E:=HilbertPair ℂ ℂ) (F:=PhasePrivate n) (G:=Channel n)).trans
      (pairCongr publicCoordinates.symm (LinearIsometryEquiv.refl ℂ (PrivateSpace n))))

@[simp] lemma regroup_apply (a b : ℂ) (w : PhasePrivate n) (q : Channel n) :
    regroup n (WithLp.toLp 2 (WithLp.toLp 2 (a,WithLp.toLp 2 (b,w)),q)) =
      WithLp.toLp 2 (publicCoordinates.symm (WithLp.toLp 2 (a,b)),WithLp.toLp 2 (w,q)) := rfl

abbrev PhaseNonquery (n : ℕ) [NeZero n] := Line.Channel (Mspace n)

def preCircuit (n : ℕ) [NeZero n] :
    Circuit (HilbertPair (BitSpace n) (Channel n)) (HilbertPair ℂ (Channel n))
      (HilbertPair (Channel n) (Channel n)) :=
  compileReflection (lpCongr (I:=ℕ) (answerReflection n)) (phaseToBit (Model.phaseCircuit n))

def circuit (n : ℕ) [NeZero n] :
    Circuit (HilbertPair Public (PrivateSpace n)) (HilbertPair ℂ (Channel n))
      (OracleQuerySpace n ℕ) := transport (regroup n)
  (requery (lpPair (I:=ℕ) (E:=Mspace n) (F:=Mspace n)).symm (preCircuit n))

def catalyst (O : Nonbalanced n) : PrivateSpace n :=
  WithLp.toLp 2 ((halfAmplitude : ℂ) • phaseCatalyst O,0)

lemma amplified_reflection (O : Oracle n) :
    (lpCongr (I:=ℕ) O.unitary).trans ((lpCongr (I:=ℕ) (answerReflection n)).trans (lpCongr (I:=ℕ) O.unitary).symm) =
      lpCongr (I:=ℕ) O.pulledReflection := by
  ext v i
  rfl

lemma amplified_bidirectional (O : Oracle n) (q : HilbertPair (Channel n) (Channel n)) :
    bidirectional ℕ O ((lpPair (I:=ℕ) (E:=Mspace n) (F:=Mspace n)).symm q) =
      (lpPair (I:=ℕ) (E:=Mspace n) (F:=Mspace n)).symm
        (pairCongr (lpCongr (I:=ℕ) O.unitary) (lpCongr (I:=ℕ) O.unitary).symm q) := rfl

lemma public_phase_bits (b : Fin 2) :
    publicCoordinates (publicBasis b) =
      WithLp.toLp 2 ((halfAmplitude : ℂ)^2*(1+bitSign b),(halfAmplitude : ℂ)^2*(1-bitSign b)) := by
  have ha : (halfAmplitude : ℂ)^2=(1/2 : ℂ) := by
    rw [← Complex.ofReal_pow,halfAmplitude_sq]
    norm_num
  fin_cases b <;> norm_num [bitSign,ha,publicCoordinates_basis0,publicCoordinates_basis1]

lemma input_regroup (O : Nonbalanced n) :
    WithLp.toLp 2 (publicBasis 0,catalyst O) = regroup n
      (WithLp.toLp 2 (WithLp.toLp 2 ((1 : ℂ),WithLp.toLp 2 ((0 : ℂ),
        (halfAmplitude : ℂ) • phaseCatalyst O)),(0 : Channel n))) := by
  rw [regroup_apply]
  apply (WithLp.equiv 2 (_ × _)).injective
  apply Prod.ext
  · exact (publicCoordinates.symm_apply_eq.mpr publicCoordinates_basis0.symm).symm
  · rfl

/-- Exact public bit, returned actual catalyst, with a circuit independent of p and delta. -/
theorem exact_run (O : Nonbalanced n) :
    Query.run (bidirectional ℕ O.val) (circuit n) (WithLp.toLp 2 (publicBasis 0,catalyst O)) =
      WithLp.toLp 2 (publicBasis O.val.r,catalyst O) := by
  rw [input_regroup,circuit,run_transport,requery_run _ _ _ (amplified_bidirectional O.val)]
  rw [preCircuit,compileReflection_run,amplified_reflection]
  rw [phaseToBit_run _ _ _ _ (phaseCatalyst_spec O).1,Unrestricted.phaseSign_bitSign]
  rw [regroup_apply]
  apply (WithLp.equiv 2 (_ × _)).injective
  apply Prod.ext
  · exact publicCoordinates.symm_apply_eq.mpr (public_phase_bits O.val.r).symm
  · rfl

/-- The executed full-oracle cost is exactly the phase cost: the factor two
from reflection compilation cancels the factor one-half from public Hadamards. -/
theorem pointwise_cost (O : Nonbalanced n) :
    Query.cost (bidirectional ℕ O.val) (circuit n) (WithLp.toLp 2 (publicBasis 0,catalyst O)) =
      1/|1-2*O.val.p| := by
  rw [input_regroup,circuit,cost_transport,requery_cost _ _ _ (amplified_bidirectional O.val)]
  rw [preCircuit,compileReflection_cost,amplified_reflection,phaseToBit_cost,
    (phaseCatalyst_spec O).2.1]
  ring

/-- The actual smaller catalyst norm, equation (3.11), follows through the
public-only conversion and the initially empty added directional branch. -/
theorem catalyst_norm (O : Nonbalanced n) :
    ‖catalyst O‖^2 = min O.val.p (1-O.val.p)/(2*|1-2*O.val.p|) := by
  rw [catalyst,WithLp.prod_norm_sq_eq_of_L2]
  simp only [WithLp.toLp_fst,WithLp.toLp_snd,norm_zero,zero_pow (by decide : (2 : ℕ)≠0),add_zero]
  rw [phaseToBit_catalyst_norm,(phaseCatalyst_spec O).2.2]
  ring

def realization (gap : Gap) (n : ℕ) [NeZero n] : Realization gap n where
  Control := ℕ
  Private := PrivateSpace n
  Nonquery := HilbertPair ℂ (Channel n)
  circuit := circuit n
  catalyst := fun O => catalyst (Unrestricted.promisedInstance gap O)
  exact := fun O => exact_run (Unrestricted.promisedInstance gap O)

lemma uniform_cost_le (gap : Gap) :
    (realization gap n).uniformCost ≤ ENNReal.ofReal (1/(2*gap.δ)) := by
  apply iSup_le
  intro O
  change ENNReal.ofReal (Query.cost (bidirectional ℕ O.val) (circuit n)
    (WithLp.toLp 2 (publicBasis 0,catalyst (Unrestricted.promisedInstance gap O)))) ≤ _
  calc
    _ = ENNReal.ofReal (1/|1-2*O.val.p|) :=
      congrArg ENNReal.ofReal (pointwise_cost (Unrestricted.promisedInstance gap O))
    _ ≤ _ := ENNReal.ofReal_le_ofReal (Unrestricted.cost_le_gap gap O)

/-- The promised transduction-complexity bound (3.11), for the actual catalyst. -/
theorem catalyst_bound (gap : Gap) (O : promisedFamily n gap.δ) :
    ‖catalyst (Unrestricted.promisedInstance gap O)‖^2 ≤ (1-2*gap.δ)/(8*gap.δ) := by
  rw [catalyst_norm]
  change min O.val.p (1-O.val.p)/(2*|1-2*O.val.p|) ≤ _
  have hab : 2*gap.δ ≤ |1-2*O.val.p| := by
    rcases O.property with hl | hh
    · rw [abs_of_nonneg (by linarith [gap.δ_pos] : 0≤1-2*O.val.p)]
      linarith
    · rw [abs_of_nonpos (by linarith [gap.δ_pos] : 1-2*O.val.p≤0)]
      linarith
  have hm : min O.val.p (1-O.val.p) = (1-|1-2*O.val.p|)/2 := by
    by_cases hl : O.val.p≤1/2
    · rw [min_eq_left (by linarith),abs_of_nonneg (by linarith)]
      ring
    · rw [min_eq_right (by linarith),abs_of_nonpos (by linarith)]
      ring
  rw [hm]
  apply (div_le_div_iff₀ (by nlinarith [gap.δ_pos]) (by linarith [gap.δ_pos])).2
  nlinarith

/-- Exactly four actual oracle gates occur in this fixed finite circuit. -/
theorem query_count : queryCount (circuit n)=4 := by
  rw [circuit,transport_queryCount,requery_queryCount,preCircuit,compileReflection_queryCount]
  simp [phaseToBit,queryCount_append,queryCount,parallel_queryCount,Model.phaseCircuit,
    Line.publicCircuit,transport_queryCount,Line.phaseCircuit]

lemma private_separable : TopologicalSpace.SeparableSpace (PrivateSpace n) := by
  letI : TopologicalSpace.SeparableSpace (PhasePrivate n) := Line.private_separable (knownInput n)
  letI : TopologicalSpace.SeparableSpace (Channel n) := Query.lp_separable
  infer_instance

end ELV.FourQuery
