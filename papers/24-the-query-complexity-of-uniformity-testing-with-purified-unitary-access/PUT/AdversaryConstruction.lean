import PUT.TestingLowerBound
import PUT.FullQueryBound
import PUT.VectorPrior
import PUT.PhysicalOracles
import PUT.PhysicalRegisters
import PUT.SourceTargets
import PUT.TesterPromises

/-!
# Concrete adversary data for actual purified-access tester circuits

The prior fields and the Fourier--Dirichlet adversary are actual operators.
The constant/free-computation/measurement conditions are proved from the
finite physical tensor construction, rather than supplied as structural
hypotheses by the user. The query-difference estimate is transported from
the proved `FullQueryBound.query_norm_le_printed`.
-/
noncomputable section
namespace PUT.AdversaryConstruction
open MeasureTheory QueryModel FourierModel
open scoped ENNReal InnerProductSpace

section TensorConditions
variable {X Y ι : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [Fintype ι] [DecidableEq ι]
  {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Generic internal constructor: physical free computation and final
measurement intertwining follow from the actual tensor, and its constant
condition follows from the scalar latent constant one. Only the displayed
actual query estimate remains to be supplied by the concrete oracle proof. -/
theorem tensor_conditions (C : Circuit (VectorPrior.Physical ι))
    (U₀ : PointwiseUnitary μ (VectorPrior.Physical ι))
    (U₁ : PointwiseUnitary ν (VectorPrior.Physical ι))
    (Γ : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ) (A B : ℝ)
    (hnorm : ‖Γ‖ ≤ A)
    (hconst : Γ (Lp.const 2 ν (1 : ℂ)) = (A : ℂ) • Lp.const 2 μ (1 : ℂ))
    (hquery : ∀ t,
      ‖(VectorPrior.tensor (ι := ι) Γ).comp
        ((C.priorEvolution U₁).query t : Lp (VectorPrior.Physical ι) 2 ν →L[ℂ] Lp (VectorPrior.Physical ι) 2 ν) -
      ((C.priorEvolution U₀).query t : Lp (VectorPrior.Physical ι) 2 μ →L[ℂ] Lp (VectorPrior.Physical ι) 2 μ).comp
        (VectorPrior.tensor (ι := ι) Γ)‖ ≤ B) :
    TestingLowerBound.AdversaryConditions C U₀ U₁ (VectorPrior.tensor Γ) A B where
  norm_le := (VectorPrior.tensor_norm_le Γ).trans hnorm
  on_constant := VectorPrior.tensor_constant_of_one Γ (A : ℂ) hconst
  free_commutation t y := by
    have h := VectorPrior.tensor_intertwines_unitary Γ (C.free (t+1))
    exact congrArg (fun L => L y) h
  measurement_commutation y := by
    have h := VectorPrior.tensor_intertwines Γ C.measurement.reject
    exact (congrArg (fun L => L y) h).symm
  query_difference := hquery

end TensorConditions

/-- Hermitian oracle fields have identical forward and inverse lifted
operations, including arbitrary states outside the promise. -/
theorem query_lift_eq_of_symm {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] {μ : Measure X}
    (U : PointwiseUnitary μ H) (hsymm : ∀ x, (U.unitary x).symm = U.unitary x)
    (q : Direction) : queryUnitary U.lift q = U.lift := by
  cases q with
  | forward => rfl
  | inverse =>
    apply LinearIsometryEquiv.ext
    intro f
    apply Lp.ext
    filter_upwards [U.query_lift_ae Direction.inverse f, U.lift_apply_ae f] with x hi hf
    change (U.lift.symm f) x = (U.lift f) x
    change (U.lift.symm f) x = (U.unitary x).symm (f x) at hi
    rw [hi, hf]
    exact congrArg (fun V : H ≃ₗᵢ[ℂ] H => V (f x)) (hsymm x)

section BasePhysical
variable {d M : ℕ} {a : ℝ}

/-- The actual physical tensor of the latent Γ acts blockwise after the
proved bottom/output L² isometry. -/
theorem physicalSplit_tensor (Γ : AltL2 d M a →L[ℂ] NullL2 d M)
    (f : Lp (PurificationSpace d M) 2 (alternativeMeasure d M a)) :
    PhysicalOracles.physicalSplit (ι := FourierModel.Coord d M) (phaseMeasure d M) (VectorPrior.tensor Γ f) =
      OperatorBridge.liftedAdversary Γ (workspaceOperator (ι := Coord d M) Γ)
        (PhysicalOracles.physicalSplit (ι := FourierModel.Coord d M) (alternativeMeasure d M a) f) := by
  apply WithLp.ofLp_injective
  apply Prod.ext
  · change VectorPrior.coordinate (phaseMeasure d M) (Sum.inl ()) (VectorPrior.tensor Γ f) =
      Γ (VectorPrior.coordinate (alternativeMeasure d M a) (Sum.inl ()) f) + 0
    simpa using VectorPrior.tensor_coordinate Γ f (Sum.inl ())
  · apply PiLp.ext
    intro q
    change VectorPrior.coordinate (phaseMeasure d M) (Sum.inr q) (VectorPrior.tensor Γ f) =
      (0 + workspaceOperator (ι := Coord d M) Γ
        (PhysicalOracles.physicalSplit (ι := FourierModel.Coord d M) (alternativeMeasure d M a) f).snd) q
    simp only [zero_add, workspaceOperator_apply, PhysicalOracles.physicalSplit_snd]
    exact VectorPrior.tensor_coordinate Γ f (Sum.inr q)

/-- Exact intertwining of the full physical query difference with the
actual reflection-block difference proved in `FullQueryBound`. -/
theorem physicalSplit_query_difference (hd : 0 < d) (ha : 0 < a) (hM : 0 < M)
    (Γ : AltL2 d M a →L[ℂ] NullL2 d M)
    (f : Lp (PurificationSpace d M) 2 (alternativeMeasure d M a)) :
    PhysicalOracles.physicalSplit (ι := FourierModel.Coord d M) (phaseMeasure d M)
      ((VectorPrior.tensor Γ ∘L (PhysicalOracles.U1 hd ha hM).lift.toLinearIsometry.toContinuousLinearMap -
        (PhysicalOracles.U0 hd hM).lift.toLinearIsometry.toContinuousLinearMap ∘L VectorPrior.tensor Γ) f) =
      ((OperatorBridge.liftedAdversary Γ (workspaceOperator (ι := Coord d M) Γ) ∘L
          OperatorBridge.reflectionBlock (FourierPreparation.V1 hd ha hM).toContinuousLinearMap -
        OperatorBridge.reflectionBlock (FourierPreparation.V0 hd hM).toContinuousLinearMap ∘L
          OperatorBridge.liftedAdversary Γ (workspaceOperator (ι := Coord d M) Γ))
        (PhysicalOracles.physicalSplit (ι := FourierModel.Coord d M) (alternativeMeasure d M a) f)) := by
  change PhysicalOracles.physicalSplit (ι := FourierModel.Coord d M) (phaseMeasure d M)
    (VectorPrior.tensor Γ ((PhysicalOracles.U1 hd ha hM).lift f) -
      (PhysicalOracles.U0 hd hM).lift (VectorPrior.tensor Γ f)) = _
  rw [map_sub, physicalSplit_tensor, PhysicalOracles.U1_lift_reflectionBlock,
    PhysicalOracles.U0_lift_reflectionBlock, physicalSplit_tensor]
  rfl

/-- Lemma 1 on the real finite physical Hilbert space, before adding the
control qubit and arbitrary tester workspace. -/
theorem base_query_norm (moments : External.DirichletJointMomentLaw)
    (hd : 2 ≤ d) (ha : 0 < a) (hM : 0 < M) (A : ℝ) (hA : 1 ≤ A)
    (hparam : 16 * A ^ 2 * LA A ≤ (M : ℝ)) :
    ‖VectorPrior.tensor (gamma (M := M) (by omega : 0 < d) ha A) ∘L
        (PhysicalOracles.U1 (by omega : 0 < d) ha hM).lift.toLinearIsometry.toContinuousLinearMap -
      (PhysicalOracles.U0 (by omega : 0 < d) hM).lift.toLinearIsometry.toContinuousLinearMap ∘L
        VectorPrior.tensor (gamma (M := M) (by omega : 0 < d) ha A)‖ ≤ lemma1RHS A a d := by
  have hb := FullQueryBound.query_norm_le_printed (M := M) moments hd ha A hA hparam
  have hB : 0 ≤ lemma1RHS A a d := (norm_nonneg _).trans hb
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro f
  rw [← (PhysicalOracles.physicalSplit (ι := FourierModel.Coord d M) (phaseMeasure d M)).norm_map,
    physicalSplit_query_difference (by omega : 0 < d) ha hM]
  exact (ContinuousLinearMap.le_opNorm _ _).trans (by
    rw [(PhysicalOracles.physicalSplit (ι := FourierModel.Coord d M) (alternativeMeasure d M a)).norm_map]
    exact mul_le_mul_of_nonneg_right hb (norm_nonneg f))

end BasePhysical

section TransportedTensor
variable {X Y H ι : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype ι] [DecidableEq ι]
  {μ : Measure X} {ν : Measure Y}

/-- The actual finite-dimensional physical tensor in any fixed physical
coordinate equivalence, including the tester's nested finite registers. -/
def transportTensor (E : H ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι)
    (Γ : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ) : Lp H 2 ν →L[ℂ] Lp H 2 μ :=
  (PhysicalRegisters.lpTransport E μ).symm.toLinearIsometry.toContinuousLinearMap ∘L
    VectorPrior.tensor (ι := ι) Γ ∘L
      (PhysicalRegisters.lpTransport E ν).toLinearIsometry.toContinuousLinearMap

theorem transportTensor_norm_le (E : H ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι)
    (Γ : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ) : ‖transportTensor E Γ‖ ≤ ‖Γ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  change ‖(PhysicalRegisters.lpTransport E μ).symm
    (VectorPrior.tensor Γ (PhysicalRegisters.lpTransport E ν f))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact ((VectorPrior.tensor Γ).le_opNorm _).trans (by
    rw [LinearIsometryEquiv.norm_map]
    exact mul_le_mul_of_nonneg_right (VectorPrior.tensor_norm_le Γ) (norm_nonneg _))

omit [DecidableEq ι] in
theorem lpTransport_const (E : H ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι)
    (μ : Measure X) [IsFiniteMeasure μ] (v : H) :
    PhysicalRegisters.lpTransport E μ (Lp.const 2 μ v) = Lp.const 2 μ (E v) := by
  apply Lp.ext
  filter_upwards [PhysicalRegisters.lpTransport_ae E μ (Lp.const 2 μ v),
    Lp.coeFn_const 2 μ v, Lp.coeFn_const 2 μ (E v)] with x hE hv hEv
  rw [hE, hv, hEv]
  rfl

omit [DecidableEq ι] in
theorem lpTransport_compLpL (E : H ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι)
    (μ : Measure X) (L : H →L[ℂ] H) (f : Lp H 2 μ) :
    PhysicalRegisters.lpTransport E μ (L.compLpL 2 μ f) =
      ((E : H →L[ℂ] EuclideanSpace ℂ ι) ∘L L ∘L
        (E.symm : EuclideanSpace ℂ ι →L[ℂ] H)).compLpL 2 μ
          (PhysicalRegisters.lpTransport E μ f) := by
  apply Lp.ext
  filter_upwards [PhysicalRegisters.lpTransport_ae E μ (L.compLpL 2 μ f),
    L.coeFn_compLpL f, PhysicalRegisters.lpTransport_ae E μ f,
    ((E : H →L[ℂ] EuclideanSpace ℂ ι) ∘L L ∘L
      (E.symm : EuclideanSpace ℂ ι →L[ℂ] H)).coeFn_compLpL
        (PhysicalRegisters.lpTransport E μ f)] with x hE hL hf hright
  rw [hE, hL, hright, hf]
  simp

/-- Arbitrary oracle-independent physical maps commute with the constructed
nested-register tensor; no commutation condition is assumed. -/
theorem transportTensor_intertwines (E : H ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι)
    (Γ : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ) (L : H →L[ℂ] H) (f : Lp H 2 ν) :
    transportTensor E Γ (L.compLpL 2 ν f) = L.compLpL 2 μ (transportTensor E Γ f) := by
  apply (PhysicalRegisters.lpTransport E μ).injective
  change PhysicalRegisters.lpTransport E μ ((PhysicalRegisters.lpTransport E μ).symm
    (VectorPrior.tensor Γ (PhysicalRegisters.lpTransport E ν (L.compLpL 2 ν f)))) =
      PhysicalRegisters.lpTransport E μ
        (L.compLpL 2 μ ((PhysicalRegisters.lpTransport E μ).symm
          (VectorPrior.tensor Γ (PhysicalRegisters.lpTransport E ν f))))
  rw [LinearIsometryEquiv.apply_symm_apply, lpTransport_compLpL, lpTransport_compLpL,
    LinearIsometryEquiv.apply_symm_apply]
  exact congrArg (fun D => D (PhysicalRegisters.lpTransport E ν f))
    (VectorPrior.tensor_intertwines Γ
      ((E : H →L[ℂ] EuclideanSpace ℂ ι) ∘L L ∘L
        (E.symm : EuclideanSpace ℂ ι →L[ℂ] H)))

theorem transportTensor_constant [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : H ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι) (Γ : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ) (A : ℂ)
    (hΓ : Γ (Lp.const 2 ν (1 : ℂ)) = A • Lp.const 2 μ (1 : ℂ)) (v : H) :
    transportTensor E Γ (Lp.const 2 ν v) = A • Lp.const 2 μ v := by
  apply (PhysicalRegisters.lpTransport E μ).injective
  change PhysicalRegisters.lpTransport E μ ((PhysicalRegisters.lpTransport E μ).symm
    (VectorPrior.tensor Γ (PhysicalRegisters.lpTransport E ν (Lp.const 2 ν v)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply, lpTransport_const,
    VectorPrior.tensor_constant_of_one Γ A hΓ, map_smul, lpTransport_const]

/-- Fixed physical unitary computation agrees with its ordinary pointwise
continuous-linear-map lift on L², for arbitrary finite register syntax. -/
theorem constant_lift_eq (μ : Measure X) (U : H ≃ₗᵢ[ℂ] H) :
    (constantUnitary (μ := μ) U).lift.toLinearIsometry.toContinuousLinearMap =
      U.toLinearIsometry.toContinuousLinearMap.compLpL 2 μ := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [(constantUnitary (μ := μ) U).lift_apply_ae f,
    U.toLinearIsometry.toContinuousLinearMap.coeFn_compLpL f] with x hU hL
  exact hU.trans hL.symm

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- All structural conditions for any actual circuit are automatic for the
constructed tensor. This internal theorem isolates only its genuine query
norm estimate, subsequently discharged by the concrete hard-oracle theorem. -/
theorem transportTensor_conditions (E : H ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι)
    (C : Circuit H) (U₀ : PointwiseUnitary μ H) (U₁ : PointwiseUnitary ν H)
    (Γ : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ) (A B : ℝ)
    (hnorm : ‖Γ‖ ≤ A)
    (hconst : Γ (Lp.const 2 ν (1 : ℂ)) = (A : ℂ) • Lp.const 2 μ (1 : ℂ))
    (hquery : ∀ t,
      ‖(transportTensor E Γ).comp ((C.priorEvolution U₁).query t : Lp H 2 ν →L[ℂ] Lp H 2 ν) -
        ((C.priorEvolution U₀).query t : Lp H 2 μ →L[ℂ] Lp H 2 μ).comp
          (transportTensor E Γ)‖ ≤ B) :
    TestingLowerBound.AdversaryConditions C U₀ U₁ (transportTensor E Γ) A B where
  norm_le := (transportTensor_norm_le E Γ).trans hnorm
  on_constant := transportTensor_constant E Γ (A : ℂ) hconst
  free_commutation t y := by
    change transportTensor E Γ ((constantUnitary (μ := ν) (C.free (t+1))).lift y) =
      (constantUnitary (μ := μ) (C.free (t+1))).lift (transportTensor E Γ y)
    change transportTensor E Γ
      ((constantUnitary (μ := ν) (C.free (t+1))).lift.toLinearIsometry.toContinuousLinearMap y) =
      (constantUnitary (μ := μ) (C.free (t+1))).lift.toLinearIsometry.toContinuousLinearMap
        (transportTensor E Γ y)
    rw [constant_lift_eq, constant_lift_eq]
    exact transportTensor_intertwines E Γ (C.free (t+1)).toLinearIsometry.toContinuousLinearMap y
  measurement_commutation y := by
    exact (transportTensor_intertwines E Γ C.measurement.reject y).symm
  query_difference := hquery

end TransportedTensor

section TesterData
variable {d M : ℕ} {a : ℝ}

/-- The concrete vector-valued adversary on the tester's actual nested
workspace/control/preparation register. -/
def testerGamma (hd : 0 < d) (ha : 0 < a) (A : ℝ) (C : SourceTargets.TesterFamily d) :
    Lp (SourceTargets.TestSpace d M (C.workspace M)) 2 (alternativeMeasure d M a) →L[ℂ]
      Lp (SourceTargets.TestSpace d M (C.workspace M)) 2 (phaseMeasure d M) :=
  transportTensor (PhysicalRegisters.flatten d M (C.workspace M)) (gamma hd ha A)

private theorem workspace_symm_of_symm {H ι : Type*} [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : H ≃ₗᵢ[ℂ] H) (hU : U.symm = U) :
    (withWorkspace (ι := ι) U).symm = withWorkspace (ι := ι) U := by
  apply LinearIsometryEquiv.ext
  intro x
  apply PiLp.ext
  intro i
  change U.symm (x i) = U (x i)
  rw [hU]

private theorem test_unitary_symm (v : Coord d M → ℂ) (W : ℕ) :
    (withWorkspace (ι := Fin W) (controlled (PhysicalOracles.unitary v))).symm =
      withWorkspace (ι := Fin W) (controlled (PhysicalOracles.unitary v)) := by
  apply workspace_symm_of_symm
  rw [controlled_inverse, PhysicalOracles.unitary_symm]

theorem nullField_symm (C : SourceTargets.TesterFamily d)
    (hd : 0 < d) (hM : 0 < M) (x : Torus d M) :
    ((TesterPromises.nullField C hd hM).unitary x).symm =
      (TesterPromises.nullField C hd hM).unitary x :=
  test_unitary_symm (fun q => FourierPreparation.nullAmplitude q x) (C.workspace M)

theorem alternativeField_symm (C : SourceTargets.TesterFamily d)
    (hd : 0 < d) (ha : 0 < a) (hM : 0 < M) (x : (Fin d → ℝ) × Torus d M) :
    ((TesterPromises.alternativeField C hd ha hM).unitary x).symm =
      (TesterPromises.alternativeField C hd ha hM).unitary x :=
  test_unitary_symm (fun q => FourierPreparation.altAmplitude q x) (C.workspace M)

end TesterData

section ConcreteConditions
variable {d M : ℕ} {a : ℝ}

/-- The concrete Fourier--Dirichlet hard instances satisfy every structural
adversary condition for an arbitrary actual tester circuit. The only
analytic external input is the disclosed standard Dirichlet moment law. -/
theorem tester_conditions (moments : External.DirichletJointMomentLaw)
    (hd : 2 ≤ d) (ha : 0 < a) (hM : 0 < M) (A : ℝ) (hA : 1 ≤ A)
    (hparam : 16 * A ^ 2 * LA A ≤ (M : ℝ)) (C : SourceTargets.TesterFamily d) :
    letI : IsProbabilityMeasure (alternativeMeasure d M a) := alternative_probability d M ha
    TestingLowerBound.AdversaryConditions (C.circuit M)
      (TesterPromises.nullField C (by omega : 0 < d) hM)
      (TesterPromises.alternativeField C (by omega : 0 < d) ha hM)
      (testerGamma (M := M) (by omega : 0 < d) ha A C) A (lemma1RHS A a d) := by
  letI : IsProbabilityMeasure (alternativeMeasure d M a) := alternative_probability d M ha
  refine transportTensor_conditions (PhysicalRegisters.flatten d M (C.workspace M))
    (C.circuit M) (TesterPromises.nullField C (by omega : 0 < d) hM)
    (TesterPromises.alternativeField C (by omega : 0 < d) ha hM)
    (gamma (M := M) (by omega : 0 < d) ha A) A (lemma1RHS A a d)
    (gamma_norm moments hd ha (by linarith : 0 < A)).le
    (gamma_constant moments hd ha (by linarith : 0 < A)) ?_
  intro t
  change ‖transportTensor (PhysicalRegisters.flatten d M (C.workspace M))
      (gamma (M := M) (by omega : 0 < d) ha A) ∘L
        (queryUnitary (TesterPromises.alternativeField C (by omega : 0 < d) ha hM).lift
          ((C.circuit M).direction t)).toLinearIsometry.toContinuousLinearMap -
      (queryUnitary (TesterPromises.nullField C (by omega : 0 < d) hM).lift
        ((C.circuit M).direction t)).toLinearIsometry.toContinuousLinearMap ∘L
      transportTensor (PhysicalRegisters.flatten d M (C.workspace M))
        (gamma (M := M) (by omega : 0 < d) ha A)‖ ≤ _
  rw [query_lift_eq_of_symm _ (alternativeField_symm C (by omega : 0 < d) ha hM),
    query_lift_eq_of_symm _ (nullField_symm C (by omega : 0 < d) hM)]
  exact PhysicalRegisters.physical_query_bound d M (C.workspace M)
    (gamma (M := M) (by omega : 0 < d) ha A)
    (PhysicalOracles.U0 (by omega : 0 < d) hM)
    (PhysicalOracles.U1 (by omega : 0 < d) ha hM)
    (base_query_norm moments hd ha hM A hA hparam)

/-- Existence packaging for the main theorem: Γ is the actual constructed
vector-valued tensor, and no structural adversary or query norm hypothesis
is left for the caller to assume. -/
theorem exists_tester_adversary (moments : External.DirichletJointMomentLaw)
    (hd : 2 ≤ d) (ha : 0 < a) (hM : 0 < M) (A : ℝ) (hA : 1 ≤ A)
    (hparam : 16 * A ^ 2 * LA A ≤ (M : ℝ)) (C : SourceTargets.TesterFamily d) :
    letI : IsProbabilityMeasure (alternativeMeasure d M a) := alternative_probability d M ha
    ∃ Γ : Lp (SourceTargets.TestSpace d M (C.workspace M)) 2 (alternativeMeasure d M a) →L[ℂ]
        Lp (SourceTargets.TestSpace d M (C.workspace M)) 2 (phaseMeasure d M),
      TestingLowerBound.AdversaryConditions (C.circuit M)
        (TesterPromises.nullField C (by omega : 0 < d) hM)
        (TesterPromises.alternativeField C (by omega : 0 < d) ha hM)
        Γ A (lemma1RHS A a d) := by
  letI : IsProbabilityMeasure (alternativeMeasure d M a) := alternative_probability d M ha
  exact ⟨testerGamma (M := M) (by omega : 0 < d) ha A C,
    tester_conditions moments hd ha hM A hA hparam C⟩

end ConcreteConditions

end PUT.AdversaryConstruction
