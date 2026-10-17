import PUT.QueryModel
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Lifting actual oracle circuits to continuous-prior latent Hilbert spaces

A parameter-dependent oracle acts pointwise on vector-valued `L²(μ)`. Its
lift is constructed here as a genuine linear isometric equivalence; in
particular it cannot expose the latent parameter as an algorithm register.
The scalar measure `μ` is arbitrary and is not replaced by a finite prior.
-/
noncomputable section

namespace PUT.QueryModel

open MeasureTheory
open scoped ENNReal

variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] {μ : Measure X}

/-- A measurable field of arbitrary unitaries. The measurability laws ensure
that both pointwise directions define operations on actual `L²` classes. -/
structure PointwiseUnitary (μ : Measure X) (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] where
  unitary : X → H ≃ₗᵢ[ℂ] H
  measurable : ∀ f : X → H, AEStronglyMeasurable f μ →
    AEStronglyMeasurable (fun x => unitary x (f x)) μ
  inverse_measurable : ∀ f : X → H, AEStronglyMeasurable f μ →
    AEStronglyMeasurable (fun x => (unitary x).symm (f x)) μ

def PointwiseUnitary.inverse (U : PointwiseUnitary μ H) : PointwiseUnitary μ H where
  unitary x := (U.unitary x).symm
  measurable := U.inverse_measurable
  inverse_measurable := U.measurable

theorem PointwiseUnitary.memLp (U : PointwiseUnitary μ H) (f : Lp H 2 μ) :
    MemLp (fun x => U.unitary x (f x)) 2 μ := by
  apply (Lp.memLp f).congr_norm (U.measurable f (Lp.aestronglyMeasurable f))
  exact Filter.Eventually.of_forall (fun x => (U.unitary x).norm_map (f x) |>.symm)

def PointwiseUnitary.liftFun (U : PointwiseUnitary μ H) (f : Lp H 2 μ) : Lp H 2 μ :=
  (U.memLp f).toLp (fun x => U.unitary x (f x))

theorem PointwiseUnitary.liftFun_ae (U : PointwiseUnitary μ H) (f : Lp H 2 μ) :
    U.liftFun f =ᵐ[μ] fun x => U.unitary x (f x) :=
  (U.memLp f).coeFn_toLp

theorem PointwiseUnitary.liftFun_add (U : PointwiseUnitary μ H) (f g : Lp H 2 μ) :
    U.liftFun (f+g) = U.liftFun f + U.liftFun g := by
  apply Lp.ext
  filter_upwards [U.liftFun_ae (f+g), U.liftFun_ae f, U.liftFun_ae g,
    Lp.coeFn_add f g, Lp.coeFn_add (U.liftFun f) (U.liftFun g)] with x hfg hf hg hi ho
  simp only [hfg, ho, hi, Pi.add_apply, hf, hg, map_add]

theorem PointwiseUnitary.liftFun_smul (U : PointwiseUnitary μ H) (c : ℂ) (f : Lp H 2 μ) :
    U.liftFun (c • f) = c • U.liftFun f := by
  apply Lp.ext
  filter_upwards [U.liftFun_ae (c • f), U.liftFun_ae f,
    Lp.coeFn_smul c f, Lp.coeFn_smul c (U.liftFun f)] with x hcf hf hi ho
  simp only [hcf, ho, hi, Pi.smul_apply, hf, map_smul]

theorem PointwiseUnitary.liftFun_norm (U : PointwiseUnitary μ H) (f : Lp H 2 μ) :
    ‖U.liftFun f‖ = ‖f‖ := by
  rw [PointwiseUnitary.liftFun, Lp.norm_toLp, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
  exact Filter.Eventually.of_forall (fun x => (U.unitary x).norm_map (f x))

theorem PointwiseUnitary.inverse_liftFun (U : PointwiseUnitary μ H) (f : Lp H 2 μ) :
    U.inverse.liftFun (U.liftFun f) = f := by
  apply Lp.ext
  filter_upwards [U.inverse.liftFun_ae (U.liftFun f), U.liftFun_ae f] with x hi hf
  rw [hi, hf]
  exact (U.unitary x).symm_apply_apply (f x)

theorem PointwiseUnitary.liftFun_inverse (U : PointwiseUnitary μ H) (f : Lp H 2 μ) :
    U.liftFun (U.inverse.liftFun f) = f := by
  apply Lp.ext
  filter_upwards [U.liftFun_ae (U.inverse.liftFun f), U.inverse.liftFun_ae f] with x hi hf
  rw [hi, hf]
  exact (U.unitary x).apply_symm_apply (f x)

/-- The actual oracle operation on the latent/physical Hilbert space. -/
def PointwiseUnitary.lift (U : PointwiseUnitary μ H) : Lp H 2 μ ≃ₗᵢ[ℂ] Lp H 2 μ where
  toFun := U.liftFun
  invFun := U.inverse.liftFun
  left_inv := U.inverse_liftFun
  right_inv := U.liftFun_inverse
  map_add' := U.liftFun_add
  map_smul' := U.liftFun_smul
  norm_map' := U.liftFun_norm

theorem PointwiseUnitary.lift_apply_ae (U : PointwiseUnitary μ H) (f : Lp H 2 μ) :
    U.lift f =ᵐ[μ] fun x => U.unitary x (f x) := U.liftFun_ae f

/-- Known computation acts by the same unitary at every latent parameter. -/
def constantUnitary (V : H ≃ₗᵢ[ℂ] H) : PointwiseUnitary μ H where
  unitary _ := V
  measurable _ hf := V.continuous.comp_aestronglyMeasurable hf
  inverse_measurable _ hf := V.symm.continuous.comp_aestronglyMeasurable hf

theorem PointwiseUnitary.lift_symm (U : PointwiseUnitary μ H) :
    U.lift.symm = U.inverse.lift := by
  apply LinearIsometryEquiv.ext
  intro f
  apply U.lift.injective
  rw [U.lift.apply_symm_apply]
  exact (U.liftFun_inverse f).symm

theorem PointwiseUnitary.query_lift_ae (U : PointwiseUnitary μ H)
    (q : Direction) (f : Lp H 2 μ) :
    queryUnitary U.lift q f =ᵐ[μ] fun x => queryUnitary (U.unitary x) q (f x) := by
  cases q with
  | forward => exact U.lift_apply_ae f
  | inverse =>
    change U.lift.symm f =ᵐ[μ] fun x => (U.unitary x).symm (f x)
    rw [U.lift_symm]
    exact U.inverse.lift_apply_ae f

/-- A physical binary measurement acts pointwise on the latent Hilbert space. -/
def Measurement.lift (P : Measurement H) : Measurement (Lp H 2 μ) where
  reject := P.reject.compLpL 2 μ
  idem f := by
    apply Lp.ext
    filter_upwards [P.reject.coeFn_compLpL (P.reject.compLpL 2 μ f),
      P.reject.coeFn_compLpL f] with x hpp hp
    rw [hpp, hp, P.idem]
  hermitian f g := by
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [P.reject.coeFn_compLpL f, P.reject.coeFn_compLpL g] with x hf hg
    rw [hf, hg, P.hermitian]

/-- The Hilbert norm is the integral of the physical squared norm. -/
theorem prior_norm_sq (f : Lp H 2 μ) : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  calc
    ‖f‖ ^ 2 = (inner ℂ f f).re := (inner_self_eq_norm_sq (𝕜 := ℂ) f).symm
    _ = (∫ x, inner ℂ (f x) (f x) ∂μ).re := by rw [L2.inner_def]
    _ = ∫ x, (inner ℂ (f x) (f x)).re ∂μ :=
      (integral_re (𝕜 := ℂ) (L2.integrable_inner (𝕜 := ℂ) f f)).symm
    _ = ∫ x, ‖f x‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => inner_self_eq_norm_sq (𝕜 := ℂ) (f x))

section ProbabilityPrior
variable [IsProbabilityMeasure μ]

/-- The actual circuit run lifted under a continuous prior. The only
algorithm register remains `H`; the latent parameter is inaccessible. -/
def Circuit.priorEvolution (C : Circuit H) (U : PointwiseUnitary μ H) :
    Evolution (Lp H 2 μ) where
  initial := Lp.const 2 μ (C.free 0 C.initial)
  initial_norm := by
    rw [Lp.norm_const' 2 μ _ (by simp) (by simp)]
    simpa using C.initial_norm
  query t := queryUnitary U.lift (C.direction t)
  free t := (constantUnitary (μ := μ) (C.free (t+1))).lift

/-- The latent evolution is pointwise exactly the original arbitrary
oracle circuit, including inverse calls and arbitrary free computation. -/
theorem Circuit.priorEvolution_state_ae (C : Circuit H) (U : PointwiseUnitary μ H)
    (t : ℕ) : (C.priorEvolution U).state t =ᵐ[μ]
      fun x => C.state (U.unitary x) t := by
  induction t with
  | zero => exact Lp.coeFn_const 2 μ (C.free 0 C.initial)
  | succ t ht =>
    let f := (C.priorEvolution U).state t
    have hf := U.query_lift_ae (C.direction t) f
    have hfree := (constantUnitary (μ := μ) (C.free (t+1))).lift_apply_ae
      (queryUnitary U.lift (C.direction t) f)
    filter_upwards [hfree, hf, ht] with x hfree hf ht
    change ((constantUnitary (μ := μ) (C.free (t+1))).lift
      (queryUnitary U.lift (C.direction t) f)) x = _
    rw [hfree, hf]
    change C.free (t+1) (queryUnitary (U.unitary x) (C.direction t) (f x)) = _
    rw [show f x = C.state (U.unitary x) t from ht]
    rfl

/-- The final latent Born probability is exactly the original algorithm's
rejection probability averaged over the actual (possibly continuous) prior. -/
theorem Circuit.prior_rejection_probability (C : Circuit H) (U : PointwiseUnitary μ H)
    (T : ℕ) :
    (C.measurement.lift (μ := μ)).rejectionProbability ((C.priorEvolution U).state T) =
      ∫ x, C.rejectProbability (U.unitary x) T ∂μ := by
  rw [Measurement.rejectionProbability, prior_norm_sq]
  apply integral_congr_ae
  filter_upwards [C.measurement.reject.coeFn_compLpL ((C.priorEvolution U).state T),
    C.priorEvolution_state_ae U T] with x hP hs
  change ‖(C.measurement.reject.compLpL 2 μ ((C.priorEvolution U).state T)) x‖ ^ 2 = _
  rw [hP, hs]
  rfl

end ProbabilityPrior

end PUT.QueryModel
