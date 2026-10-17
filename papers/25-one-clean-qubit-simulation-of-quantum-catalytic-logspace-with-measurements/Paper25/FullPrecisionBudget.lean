import Paper25.PrecisionBudget
import Paper25.SourceCircuitSimulation
import Paper25.SelectorArithmetic

/-! A single explicit precision is enough for every numerical call of the
native simulator. Its inverse accuracy is polynomial in the original input;
no catalyst Hilbert-space dimension occurs in the precision budget. -/
noncomputable section
namespace Paper25.FullPrecisionBudget
open OperationalModel SourceCoordinates SelectedFilter

/-- Integer denominator of the regularization parameter lambda/3. -/
def deltaDen (J K : ℕ) : ℕ := 300*J^2*K^3

def deltaRep (J K : ℕ) (hJ : 0 < J) (hK : 0 < K) : RationalRep :=
  ⟨1,deltaDen J K,by dsimp [deltaDen]; positivity⟩

@[simp] lemma deltaRep_value (J K : ℕ) (hJ : 0 < J) (hK : 0 < K) :
    ((deltaRep J K hJ hK).value : ℝ) = biasDelta J K := by
  dsimp [deltaRep,RationalRep.value,deltaDen,biasDelta,biasLam]
  push_cast
  ring

/-- An integer reciprocal below half of the ideal Born separation. -/
def gapDen (J K k : ℕ) : ℕ := 1600*J^2*K^4*2^k

lemma gapDen_pos {J K : ℕ} (hJ : 0 < J) (hK : 0 < K) (k : ℕ) :
    0 < gapDen J K k := by dsimp [gapDen]; positivity

lemma reciprocal_gapDen_le (J K k : ℕ) (hJ : 0 < J) (hK : 0 < K) :
    1/(gapDen J K k:ℝ) ≤
      biasLam J K/((2:ℝ)^(k+4)*Real.sqrt (K:ℝ)) := by
  have hj : (0:ℝ) < J := by exact_mod_cast hJ
  have hk : (0:ℝ) < K := by exact_mod_cast hK
  have hk1 : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hsqrt : Real.sqrt (K:ℝ) ≤ (K:ℝ) := by
    nlinarith [Real.sq_sqrt hk.le,Real.sqrt_nonneg (K:ℝ),
      sq_nonneg (Real.sqrt (K:ℝ)-1)]
  calc
    _ = biasLam J K/((2:ℝ)^(k+4)*(K:ℝ)) := by
      dsimp [gapDen,biasLam]
      push_cast
      rw [pow_add]
      norm_num
      field_simp
      <;> ring
    _ ≤ _ := div_le_div_of_nonneg_left (biasLam_pos hj hk).le
      (mul_pos (by positivity) (Real.sqrt_pos.mpr hk))
      (mul_le_mul_of_nonneg_left hsqrt (by positivity))

/-- The 4000 term reserves numerical precision for both label-angle budgets. -/
def accuracyDen (M m d D : ℕ) : ℕ :=
  100*(24*M+16*(m*(m+2))+4000)*d*D

def precision (M m d D : ℕ) : ℕ := ceilLog2 (accuracyDen M m d D)

def labelError (D : ℕ) : ℝ := 1/(100*(D:ℝ))

lemma accuracyDen_pos (M m d D : ℕ) (hd : 0 < d) (hD : 0 < D) :
    0 < accuracyDen M m d D := by dsimp [accuracyDen]; positivity

lemma all_budgets (M m d D : ℕ) (hd : 0 < d) (hD : 0 < D) :
    bitError (precision M m d D) ≤ labelError D/4 ∧
    bitError (precision M m d D) ≤ (1/(d:ℝ))*labelError D/40 ∧
    4*(24*(M:ℝ)*bitError (precision M m d D) +
       16*(m*(m+2):ℕ)*bitError (precision M m d D)+labelError D) ≤ 1/(D:ℝ) := by
  have hdr : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hDr : (0:ℝ) < D := by exact_mod_cast hD
  let A : ℝ := 24*(M:ℝ)+16*(m*(m+2):ℕ)+4000
  have hA : 4000 ≤ A := by
    dsimp [A]
    have hm : (0:ℝ) ≤ (m*(m+2):ℕ) := by positivity
    have hM : (0:ℝ) ≤ M := by positivity
    linarith
  have hp := precision_error (accuracyDen_pos M m d D hd hD)
  change bitError (precision M m d D) ≤ 1/(accuracyDen M m d D:ℝ) at hp
  have hn : (accuracyDen M m d D:ℝ) = 100*A*(d:ℝ)*(D:ℝ) := by
    dsimp [accuracyDen,A]
    push_cast
    ring
  rw [hn] at hp
  have he := bitError_pos (precision M m d D)
  have hmul : bitError (precision M m d D)*(100*A*(d:ℝ)*(D:ℝ)) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp hp
  have hb : (A*(d:ℝ))*bitError (precision M m d D) ≤ 1/(100*(D:ℝ)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [hmul]
  have hc : (24*(M:ℝ)+16*(m*(m+2):ℕ))*bitError (precision M m d D) ≤ labelError D := by
    have hcoeff : 24*(M:ℝ)+16*(m*(m+2):ℕ) ≤ A*(d:ℝ) := by
      have hAn : 0 ≤ A := by linarith
      nlinarith
    exact (mul_le_mul_of_nonneg_right hcoeff he.le).trans hb
  constructor
  · apply (le_div_iff₀ (by norm_num : (0:ℝ)<4)).mpr
    dsimp [labelError]
    have hsmall : (4:ℝ) ≤ A*(d:ℝ) := by nlinarith
    simpa only [mul_comm] using (mul_le_mul_of_nonneg_right hsmall he.le).trans hb
  constructor
  · have hsmall : (4000:ℝ) ≤ 100*A := by linarith
    have hmul' : bitError (precision M m d D)*(4000*(d:ℝ)*(D:ℝ)) ≤ 1 := by
      apply (mul_le_mul_of_nonneg_left ?_ he.le).trans hmul
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsmall (by positivity)) hDr.le
    dsimp [labelError]
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<40)).mpr
    rw [one_div_mul_one_div]
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [hmul']
  · have hDinv : 0 < 1/(D:ℝ) := by positivity
    have hs : labelError D = (1/(D:ℝ))/100 := by dsimp [labelError]; ring
    rw [hs] at hc ⊢
    nlinarith [hc]

variable {G : EffectiveGateSet}
def sourceD (C : EffectiveSourceComputation G) : ℕ :=
  gapDen (clockSize (duration C)) (2^C.workQubits)
    (simulatorSmallQubits C.workQubits (duration C))

def sourceDeltaDen (C : EffectiveSourceComputation G) : ℕ :=
  deltaDen (clockSize (duration C)) (2^C.workQubits)

def sourcePhase (C : EffectiveSourceComputation G) : ℕ :=
  sourcePhaseBits (SourceCircuitSimulation.clockBits C) (restQubits C)

def sourcePrecision (C : EffectiveSourceComputation G) : ℕ :=
  precision (2^sourcePhase C) (sourcePhase C) (sourceDeltaDen C) (sourceD C)

lemma sourceD_pos (C : EffectiveSourceComputation G) : 0 < sourceD C :=
  gapDen_pos (powerTwoCeil_pos _) (Nat.two_pow_pos _) _

lemma sourceDeltaDen_pos (C : EffectiveSourceComputation G) : 0 < sourceDeltaDen C := by
  have hJ : 0 < clockSize (duration C) := powerTwoCeil_pos _
  have hK : 0 < 2^C.workQubits := Nat.two_pow_pos _
  dsimp [sourceDeltaDen,deltaDen]
  positivity

lemma sourceD_gap (C : EffectiveSourceComputation G) :
    1/(sourceD C:ℝ) ≤ SourceCircuitSimulation.gap C/2 := by
  rw [SourceCircuitSimulation.half_gap_formula]
  exact reciprocal_gapDen_le _ _ _ (powerTwoCeil_pos _) (Nat.two_pow_pos _)

lemma sourceD_polynomial (F : EffectiveSourceFamily G) :
    PolynomialBound (fun x => sourceD (F.circuit x)) :=
  (((PolynomialBound.const 1600).mul
    ((clock_size_polynomial (SourceCircuitSimulation.duration_polynomial F)).pow 2)).mul
      ((logarithmic_work_dimension F.work_logarithmic).pow 4)).mul
      (SourceCircuitSimulation.mixed_resources F).2

lemma sourceDeltaDen_polynomial (F : EffectiveSourceFamily G) :
    PolynomialBound (fun x => sourceDeltaDen (F.circuit x)) :=
  ((PolynomialBound.const 300).mul
    ((clock_size_polynomial (SourceCircuitSimulation.duration_polynomial F)).pow 2)).mul
      ((logarithmic_work_dimension F.work_logarithmic).pow 3)

lemma sourcePhase_dimension_polynomial (F : EffectiveSourceFamily G) :
    PolynomialBound (fun x => 2^sourcePhase (F.circuit x)) := by
  have h := phase_labels_polynomial
    (clock_size_polynomial (SourceCircuitSimulation.duration_polynomial F))
    (logarithmic_work_dimension F.work_logarithmic)
    (fun _ => powerTwoCeil_pos _) (fun _ => Nat.two_pow_pos _)
  convert h using 1
  funext x
  unfold sourcePhase sourcePhaseBits SourceCircuitSimulation.clockBits
  rw [SimulationParameters.clock_card,SimulationParameters.work_card,restQubits_add_one]
  rfl

lemma sourcePrecision_logarithmic (F : EffectiveSourceFamily G) :
    LogarithmicBound (fun x => sourcePrecision (F.circuit x)) := by
  have hM := sourcePhase_dimension_polynomial F
  have hm : PolynomialBound (fun x => sourcePhase (F.circuit x)) :=
    hM.mono (fun x => Nat.le_of_lt (Nat.lt_two_pow_self (n := sourcePhase (F.circuit x))))
  apply precision_logarithmic
  · exact ((((PolynomialBound.const 100).mul
      ((((PolynomialBound.const 24).mul hM).add
        ((PolynomialBound.const 16).mul (hm.mul (hm.add (PolynomialBound.const 2))))).add
          (PolynomialBound.const 4000))).mul (sourceDeltaDen_polynomial F)).mul
            (sourceD_polynomial F))
  · intro x
    exact accuracyDen_pos _ _ _ _ (sourceDeltaDen_pos _) (sourceD_pos _)

end Paper25.FullPrecisionBudget
