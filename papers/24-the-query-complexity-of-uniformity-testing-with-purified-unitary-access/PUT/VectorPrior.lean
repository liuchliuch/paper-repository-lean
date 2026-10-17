import PUT.QueryPrior
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Finite physical registers commute with the latent L² construction

The equivalence and tensor lift below are constructed, not supplied as an
external theorem. They identify the actual vector-valued prior Hilbert space
with finitely many scalar prior Hilbert spaces, with its Euclidean norm.
-/
noncomputable section
set_option maxHeartbeats 1000000
namespace PUT.VectorPrior
open MeasureTheory PUT.QueryModel
open scoped ENNReal

variable {X Y ι : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [Fintype ι] [DecidableEq ι]

abbrev Physical (ι : Type*) [Fintype ι] := EuclideanSpace ℂ ι
abbrev Scalars (μ : Measure X) (ι : Type*) := Register ι (Lp ℂ 2 μ)

def coordinate (μ : Measure X) (i : ι) : Lp (Physical ι) 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (EuclideanSpace.proj i).compLpL 2 μ

theorem coordinate_ae (μ : Measure X) (i : ι) (f : Lp (Physical ι) 2 μ) :
    coordinate μ i f =ᵐ[μ] fun x => f x i :=
  (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL f

def splitLinear (μ : Measure X) : Lp (Physical ι) 2 μ →ₗ[ℂ] Scalars μ ι where
  toFun f := WithLp.toLp 2 (fun i => coordinate μ i f)
  map_add' f g := by ext i; simp [map_add]
  map_smul' c f := by ext i; simp [map_smul]

@[simp] theorem splitLinear_apply (μ : Measure X) (f : Lp (Physical ι) 2 μ) (i : ι) :
    splitLinear μ f i = coordinate μ i f := rfl

private theorem coordinate_square_integrable (μ : Measure X) (f : Lp (Physical ι) 2 μ) (i : ι) :
    Integrable (fun x => ‖f x i‖ ^ 2) μ := by
  have h := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (coordinate μ i f))).mp
    (Lp.memLp (coordinate μ i f))
  apply h.congr
  filter_upwards [coordinate_ae μ i f] with x hx
  rw [hx]

/-- Pythagoras and integration give the actual tensor/direct-sum isometry. -/
theorem splitLinear_norm (μ : Measure X) (f : Lp (Physical ι) 2 μ) :
    ‖splitLinear μ f‖ = ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, prior_norm_sq]
  calc
    (∑ i, ‖coordinate μ i f‖ ^ 2) = ∑ i, ∫ x, ‖f x i‖ ^ 2 ∂μ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [prior_norm_sq]
      apply integral_congr_ae
      filter_upwards [coordinate_ae μ i f] with x hx
      rw [hx]
    _ = ∫ x, (∑ i, ‖f x i‖ ^ 2) ∂μ := by
      rw [integral_finset_sum _ (fun i _ => coordinate_square_integrable μ f i)]
    _ = ∫ x, ‖f x‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => (PiLp.norm_sq_eq_of_L2 _ (f x)).symm)

def singleMap (i : ι) : ℂ →L[ℂ] Physical ι :=
  (ContinuousLinearMap.id ℂ ℂ).smulRight (EuclideanSpace.single i 1)

def merge (μ : Measure X) (v : Scalars μ ι) : Lp (Physical ι) 2 μ :=
  ∑ i, (singleMap i).compLpL 2 μ (v i)

private theorem coordinate_single (μ : Measure X) (i j : ι) (f : Lp ℂ 2 μ) :
    coordinate μ i ((singleMap j).compLpL 2 μ f) = if i = j then f else 0 := by
  apply Lp.ext
  filter_upwards [coordinate_ae μ i ((singleMap j).compLpL 2 μ f),
    (singleMap j).coeFn_compLpL f,
    Lp.coeFn_zero (E := ℂ) (p := (2 : ℝ≥0∞)) (μ := μ)] with x hc hs hz
  rw [hc, hs]
  by_cases hij : i = j
  · subst j
    simp [singleMap]
  · simp only [if_neg hij]
    change (singleMap j (f x)) i = (0 : Lp ℂ 2 μ) x
    rw [hz]
    simp [singleMap, hij]

theorem split_merge (μ : Measure X) (v : Scalars μ ι) : splitLinear μ (merge μ v) = v := by
  apply WithLp.ofLp_injective
  funext i
  change coordinate μ i (∑ j, (singleMap j).compLpL 2 μ (v j)) = v i
  rw [map_sum]
  simp [coordinate_single]

/-- Actual L² finite-register equivalence, valid for every measure. -/
def split (μ : Measure X) : Lp (Physical ι) 2 μ ≃ₗᵢ[ℂ] Scalars μ ι :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := splitLinear μ, norm_map' := splitLinear_norm μ }
    (fun v => ⟨merge μ v, split_merge μ v⟩)

@[simp] theorem split_apply (μ : Measure X) (f : Lp (Physical ι) 2 μ) (i : ι) :
    split μ f i = coordinate μ i f := rfl

@[simp] theorem split_symm_apply (μ : Measure X) (v : Scalars μ ι) :
    (split μ).symm v = merge μ v := by
  apply (split μ).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact (split_merge μ v).symm

variable {μ : Measure X} {ν : Measure Y}

/-- The actual operator `Γ ⊗ I_physical`, on vector-valued prior spaces. -/
def tensor (Γ : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ) :
    Lp (Physical ι) 2 ν →L[ℂ] Lp (Physical ι) 2 μ :=
  (split (ι := ι) μ).symm.toLinearIsometry.toContinuousLinearMap ∘L workspaceOperator (ι := ι) Γ ∘L
    (split (ι := ι) ν).toLinearIsometry.toContinuousLinearMap

theorem tensor_coordinate (Γ : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ)
    (f : Lp (Physical ι) 2 ν) (i : ι) :
    coordinate μ i (tensor Γ f) = Γ (coordinate ν i f) := by
  change ((split (ι := ι) μ) ((split (ι := ι) μ).symm
    (workspaceOperator (ι := ι) Γ (split (ι := ι) ν f)))) i = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem tensor_norm_le (Γ : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ) : ‖tensor (ι := ι) Γ‖ ≤ ‖Γ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  change ‖(split (ι := ι) μ).symm (workspaceOperator (ι := ι) Γ (split (ι := ι) ν f))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact ((workspaceOperator (ι := ι) Γ).le_opNorm _).trans (by
    rw [LinearIsometryEquiv.norm_map]
    exact mul_le_mul_of_nonneg_right (workspaceOperator_norm (ι := ι) Γ) (norm_nonneg _))


/-! ## Arbitrary physical computation automatically intertwines the tensor -/

private theorem lp_sum_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (μ : Measure X) {κ : Type*} (s : Finset κ) (f : κ → Lp E 2 μ) :
    ((∑ i ∈ s, f i : Lp E 2 μ) : X → E) =ᵐ[μ] fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Lp.coeFn_zero (E := E) (p := (2 : ℝ≥0∞)) (μ := μ))
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (f i) (∑ j ∈ s, f j), ih] with x had hs
    rw [had, Pi.add_apply, hs]

theorem physical_matrix_apply {κ : Type*} [Fintype κ] [DecidableEq κ]
    (L : Physical ι →L[ℂ] Physical κ) (v : Physical ι) (i : κ) :
    L v i = ∑ j, (L (EuclideanSpace.single j 1) i) * v j := by
  have hv : v = ∑ j, v j • EuclideanSpace.single j 1 := by
    apply WithLp.ofLp_injective
    funext j
    change v j = (EuclideanSpace.proj j) (∑ t, v t • EuclideanSpace.single t 1)
    rw [map_sum]
    simp
  conv_lhs => rw [hv, map_sum]
  simp only [map_smul]
  change (EuclideanSpace.proj i) (∑ j, v j • L (EuclideanSpace.single j 1)) = _
  rw [map_sum]
  simp [map_smul, mul_comm]

/-- A physical continuous linear map acts by its finite complex matrix on
the scalar prior coordinates. Its coefficients do not depend on the prior. -/
theorem coordinate_compLpL {κ : Type*} [Fintype κ] [DecidableEq κ]
    (μ : Measure X) (L : Physical ι →L[ℂ] Physical κ)
    (f : Lp (Physical ι) 2 μ) (i : κ) :
    coordinate μ i (L.compLpL 2 μ f) =
      ∑ j, (L (EuclideanSpace.single j 1) i) • coordinate μ j f := by
  apply Lp.ext
  have hc : ∀ᵐ x ∂μ, ∀ j : ι, coordinate μ j f x = f x j :=
    Filter.eventually_all.mpr (fun j => coordinate_ae μ j f)
  have hsm : ∀ᵐ x ∂μ, ∀ j : ι,
      ((L (EuclideanSpace.single j 1) i) • coordinate μ j f) x =
        (L (EuclideanSpace.single j 1) i) * (coordinate μ j f x) := by
    apply Filter.eventually_all.mpr
    intro j
    exact Lp.coeFn_smul (L (EuclideanSpace.single j 1) i) (coordinate μ j f)
  filter_upwards [coordinate_ae μ i (L.compLpL 2 μ f), L.coeFn_compLpL f,
    lp_sum_ae μ Finset.univ (fun j => (L (EuclideanSpace.single j 1) i) • coordinate μ j f),
    hc, hsm] with x ho hL hsum hcoord hsmul
  rw [ho, hL, hsum, physical_matrix_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [hsmul j, hcoord j]

/-- `Γ ⊗ I` commutes with every fixed physical operation, with no
commutation assumption on the arbitrary latent operator `Γ`. -/
theorem tensor_intertwines (Γ : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ)
    (L : Physical ι →L[ℂ] Physical ι) :
    tensor (ι := ι) Γ ∘L L.compLpL 2 ν =
      L.compLpL 2 μ ∘L tensor (ι := ι) Γ := by
  apply ContinuousLinearMap.ext
  intro f
  apply (split (ι := ι) μ).injective
  apply WithLp.ofLp_injective
  funext i
  change coordinate μ i (tensor Γ (L.compLpL 2 ν f)) =
    coordinate μ i (L.compLpL 2 μ (tensor Γ f))
  rw [tensor_coordinate, coordinate_compLpL, map_sum, coordinate_compLpL]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, tensor_coordinate]

/-! ## Constant initial physical states -/

theorem coordinate_const (μ : Measure X) [IsFiniteMeasure μ]
    (v : Physical ι) (i : ι) :
    coordinate μ i (Lp.const 2 μ v) = Lp.const 2 μ (v i) := by
  apply Lp.ext
  filter_upwards [coordinate_ae μ i (Lp.const 2 μ v), Lp.coeFn_const 2 μ v,
    Lp.coeFn_const 2 μ (v i)] with x hc hv hs
  rw [hc, hv, hs]
  rfl

/-- Constant-action of `Γ` lifts to every actual finite physical state. -/
theorem tensor_constant [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (Γ : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ) (A : ℂ)
    (hΓ : ∀ z : ℂ, Γ (Lp.const 2 ν z) = A • Lp.const 2 μ z)
    (v : Physical ι) :
    tensor (ι := ι) Γ (Lp.const 2 ν v) = A • Lp.const 2 μ v := by
  apply (split (ι := ι) μ).injective
  apply WithLp.ofLp_injective
  funext i
  change coordinate μ i (tensor Γ (Lp.const 2 ν v)) =
    coordinate μ i (A • Lp.const 2 μ v)
  rw [tensor_coordinate, coordinate_const, hΓ, map_smul, coordinate_const]

/-- It suffices to verify the latent constant-action at the scalar one. -/
theorem tensor_constant_of_one [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (Γ : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ) (A : ℂ)
    (hΓ : Γ (Lp.const 2 ν (1 : ℂ)) = A • Lp.const 2 μ (1 : ℂ))
    (v : Physical ι) :
    tensor (ι := ι) Γ (Lp.const 2 ν v) = A • Lp.const 2 μ v := by
  apply tensor_constant Γ A _ v
  intro z
  have heν : Lp.const 2 ν z = z • Lp.const 2 ν (1 : ℂ) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_const 2 ν z, Lp.coeFn_const 2 ν (1 : ℂ),
      Lp.coeFn_smul z (Lp.const 2 ν (1 : ℂ))] with x hz h1 hs
    rw [hz, hs, Pi.smul_apply, h1]
    simp
  have heμ : Lp.const 2 μ z = z • Lp.const 2 μ (1 : ℂ) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_const 2 μ z, Lp.coeFn_const 2 μ (1 : ℂ),
      Lp.coeFn_smul z (Lp.const 2 μ (1 : ℂ))] with x hz h1 hs
    rw [hz, hs, Pi.smul_apply, h1]
    simp
  rw [heν, map_smul, hΓ, heμ]
  module


/-- The constant physical unitary lift used by actual circuits agrees with
the ordinary pointwise continuous-linear-map lift. -/
theorem constantUnitary_lift_eq (μ : Measure X)
    (U : Physical ι ≃ₗᵢ[ℂ] Physical ι) :
    (constantUnitary (μ := μ) U).lift.toLinearIsometry.toContinuousLinearMap =
      U.toLinearIsometry.toContinuousLinearMap.compLpL 2 μ := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [(constantUnitary (μ := μ) U).lift_apply_ae f,
    U.toLinearIsometry.toContinuousLinearMap.coeFn_compLpL f] with x hU hL
  exact hU.trans hL.symm

/-- Thus oracle-independent computation automatically preserves the latent
progress measure in the operational circuit model. -/
theorem tensor_intertwines_unitary (Γ : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ)
    (U : Physical ι ≃ₗᵢ[ℂ] Physical ι) :
    tensor (ι := ι) Γ ∘L (constantUnitary (μ := ν) U).lift.toLinearIsometry.toContinuousLinearMap =
      (constantUnitary (μ := μ) U).lift.toLinearIsometry.toContinuousLinearMap ∘L tensor (ι := ι) Γ := by
  rw [constantUnitary_lift_eq, constantUnitary_lift_eq]
  exact tensor_intertwines Γ U.toLinearIsometry.toContinuousLinearMap


/-- Rectangular naturality: the latent tensor respects every physical
continuous linear map between arbitrary finite registers. This includes
flattening maps, inclusions, projections and changes of register shape. -/
theorem tensor_natural {κ : Type*} [Fintype κ] [DecidableEq κ]
    (Γ : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ) (L : Physical ι →L[ℂ] Physical κ) :
    tensor (ι := κ) Γ ∘L L.compLpL 2 ν =
      L.compLpL 2 μ ∘L tensor (ι := ι) Γ := by
  apply ContinuousLinearMap.ext
  intro f
  apply (split (ι := κ) μ).injective
  apply WithLp.ofLp_injective
  funext i
  change coordinate μ i (tensor Γ (L.compLpL 2 ν f)) =
    coordinate μ i (L.compLpL 2 μ (tensor Γ f))
  rw [tensor_coordinate, coordinate_compLpL, map_sum, coordinate_compLpL]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, tensor_coordinate]

end PUT.VectorPrior
