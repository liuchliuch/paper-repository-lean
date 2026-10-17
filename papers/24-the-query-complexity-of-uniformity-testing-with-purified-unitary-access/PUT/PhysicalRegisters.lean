import PUT.SourceTargets
import PUT.VectorPrior
import PUT.Oracle
import PUT.PhysicalOracles

/-!
# Transport of actual physical circuits and vector-valued prior registers

All transports below are constructed linear isometric equivalences.  In
particular the finite register and the continuous latent parameter are never
identified as an algorithm-accessible tensor factor.
-/

noncomputable section
namespace PUT.PhysicalRegisters
open MeasureTheory QueryModel
open scoped ENNReal InnerProductSpace

abbrev TestIndex (d M W : ℕ) := Fin W × Bool × HQ d M

/-- The actual nested workspace/control/query register, flattened without
changing its Hilbert norm or its computational coordinates. -/
def flatten (d M W : ℕ) : SourceTargets.TestSpace d M W ≃ₗᵢ[ℂ]
    EuclideanSpace ℂ (TestIndex d M W) where
  toFun x := WithLp.toLp 2 (fun q => x q.1 q.2.1 q.2.2)
  invFun x := WithLp.toLp 2 (fun w => WithLp.toLp 2 (fun b =>
    WithLp.toLp 2 (fun q => x (w,b,q))))
  left_inv x := by ext w b q; rfl
  right_inv x := by ext ⟨w,b,q⟩; rfl
  map_add' x y := by ext ⟨w,b,q⟩; rfl
  map_smul' c x := by ext ⟨w,b,q⟩; rfl
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖(WithLp.toLp 2 (fun q : TestIndex d M W => x q.1 q.2.1 q.2.2) :
      EuclideanSpace ℂ (TestIndex d M W))‖ ^ 2 = ‖x‖ ^ 2
    simp only [PiLp.norm_sq_eq_of_L2, PiLp.toLp_apply, Fintype.sum_prod_type]

@[simp] theorem flatten_apply (d M W : ℕ) (x : SourceTargets.TestSpace d M W)
    (w : Fin W) (b : Bool) (q : HQ d M) : flatten d M W x (w,b,q) = x w b q := rfl

section Transport
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

def transportUnitary (E : H ≃ₗᵢ[ℂ] K) (U : H ≃ₗᵢ[ℂ] H) : K ≃ₗᵢ[ℂ] K :=
  E.symm.trans (U.trans E)

@[simp] theorem transportUnitary_apply (E : H ≃ₗᵢ[ℂ] K) (U : H ≃ₗᵢ[ℂ] H) (y : K) :
    transportUnitary E U y = E (U (E.symm y)) := rfl

theorem transport_queryUnitary (E : H ≃ₗᵢ[ℂ] K) (U : H ≃ₗᵢ[ℂ] H) (q : Direction) :
    queryUnitary (transportUnitary E U) q = transportUnitary E (queryUnitary U q) := by
  cases q <;> rfl

def transportMeasurement (E : H ≃ₗᵢ[ℂ] K) (P : Measurement H) : Measurement K where
  reject := (E : H →L[ℂ] K) ∘L P.reject ∘L (E.symm : K →L[ℂ] H)
  idem y := by simp [P.idem]
  hermitian x y := by
    change inner ℂ (E (P.reject (E.symm x))) y = inner ℂ x (E (P.reject (E.symm y)))
    rw [E.inner_map_eq_flip]
    have hr : inner ℂ x (E (P.reject (E.symm y))) =
        inner ℂ (E.symm x) (P.reject (E.symm y)) := by
      simpa using (E.inner_map_map (E.symm x) (P.reject (E.symm y)))
    rw [hr]
    exact P.hermitian _ _

@[simp] theorem transportMeasurement_probability (E : H ≃ₗᵢ[ℂ] K) (P : Measurement H)
    (x : H) : (transportMeasurement E P).rejectionProbability (E x) = P.rejectionProbability x := by
  simp [Measurement.rejectionProbability, transportMeasurement]

def transportCircuit (E : H ≃ₗᵢ[ℂ] K) (C : Circuit H) : Circuit K where
  initial := E C.initial
  initial_norm := by simpa using C.initial_norm
  free t := transportUnitary E (C.free t)
  direction := C.direction
  measurement := transportMeasurement E C.measurement

theorem transportCircuit_state (E : H ≃ₗᵢ[ℂ] K) (C : Circuit H) (U : H ≃ₗᵢ[ℂ] H) (t : ℕ) :
    (transportCircuit E C).state (transportUnitary E U) t = E (C.state U t) := by
  induction t with
  | zero => simp [Circuit.state, transportCircuit]
  | succ t ht =>
    change transportUnitary E (C.free (t + 1))
      (queryUnitary (transportUnitary E U) (C.direction t)
        ((transportCircuit E C).state (transportUnitary E U) t)) =
      E (C.free (t + 1) (queryUnitary U (C.direction t) (C.state U t)))
    rw [ht, transport_queryUnitary]
    simp only [transportUnitary_apply, LinearIsometryEquiv.symm_apply_apply]

theorem transportCircuit_rejectProbability (E : H ≃ₗᵢ[ℂ] K) (C : Circuit H)
    (U : H ≃ₗᵢ[ℂ] H) (t : ℕ) :
    (transportCircuit E C).rejectProbability (transportUnitary E U) t = C.rejectProbability U t := by
  simp only [Circuit.rejectProbability, transportCircuit_state]
  exact transportMeasurement_probability E C.measurement (C.state U t)

variable {X : Type*} [MeasurableSpace X]

theorem lpTransport_norm (E : H ≃ₗᵢ[ℂ] K) (μ : Measure X) (f : Lp H 2 μ) :
    ‖(E : H →L[ℂ] K).compLpL 2 μ f‖ = ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [prior_norm_sq, prior_norm_sq]
  apply integral_congr_ae
  filter_upwards [(E : H →L[ℂ] K).coeFn_compLpL f] with x hx
  rw [hx]
  change ‖E (f x)‖ ^ 2 = ‖f x‖ ^ 2
  rw [E.norm_map]

private theorem lpTransport_inverse (E : H ≃ₗᵢ[ℂ] K) (μ : Measure X) (f : Lp H 2 μ) :
    (E.symm : K →L[ℂ] H).compLpL 2 μ ((E : H →L[ℂ] K).compLpL 2 μ f) = f := by
  apply Lp.ext
  filter_upwards [(E.symm : K →L[ℂ] H).coeFn_compLpL ((E : H →L[ℂ] K).compLpL 2 μ f),
    (E : H →L[ℂ] K).coeFn_compLpL f] with x h₁ h₂
  rw [h₁, h₂]
  change E.symm (E (f x)) = f x
  exact E.symm_apply_apply _

/-- Functorial vector-valued `L²` transport by a fixed physical isometry. -/
def lpTransport (E : H ≃ₗᵢ[ℂ] K) (μ : Measure X) : Lp H 2 μ ≃ₗᵢ[ℂ] Lp K 2 μ where
  toFun := (E : H →L[ℂ] K).compLpL 2 μ
  invFun := (E.symm : K →L[ℂ] H).compLpL 2 μ
  left_inv := lpTransport_inverse E μ
  right_inv f := by simpa using lpTransport_inverse E.symm μ f
  map_add' := map_add ((E : H →L[ℂ] K).compLpL 2 μ)
  map_smul' := map_smul ((E : H →L[ℂ] K).compLpL 2 μ)
  norm_map' := lpTransport_norm E μ

theorem lpTransport_ae (E : H ≃ₗᵢ[ℂ] K) (μ : Measure X) (f : Lp H 2 μ) :
    lpTransport E μ f =ᵐ[μ] fun x => E (f x) :=
  (E : H →L[ℂ] K).coeFn_compLpL f

theorem lpTransport_symm_ae (E : H ≃ₗᵢ[ℂ] K) (μ : Measure X) (f : Lp K 2 μ) :
    (lpTransport E μ).symm f =ᵐ[μ] fun x => E.symm (f x) :=
  (E.symm : K →L[ℂ] H).coeFn_compLpL f

end Transport

section Conjugation
variable {H₀ H₁ K₀ K₁ : Type*}
  [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup K₀] [InnerProductSpace ℂ K₀]
  [NormedAddCommGroup K₁] [InnerProductSpace ℂ K₁]

def conjugate (E₀ : H₀ ≃ₗᵢ[ℂ] K₀) (E₁ : H₁ ≃ₗᵢ[ℂ] K₁)
    (D : H₁ →L[ℂ] H₀) : K₁ →L[ℂ] K₀ :=
  (E₀ : H₀ →L[ℂ] K₀) ∘L D ∘L (E₁.symm : K₁ →L[ℂ] H₁)

@[simp] theorem conjugate_apply (E₀ : H₀ ≃ₗᵢ[ℂ] K₀) (E₁ : H₁ ≃ₗᵢ[ℂ] K₁)
    (D : H₁ →L[ℂ] H₀) (y : K₁) : conjugate E₀ E₁ D y = E₀ (D (E₁.symm y)) := rfl

theorem norm_conjugate (E₀ : H₀ ≃ₗᵢ[ℂ] K₀) (E₁ : H₁ ≃ₗᵢ[ℂ] K₁)
    (D : H₁ →L[ℂ] H₀) : ‖conjugate E₀ E₁ D‖ = ‖D‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg D)
    intro y
    change ‖E₀ (D (E₁.symm y))‖ ≤ ‖D‖ * ‖y‖
    simpa only [E₀.norm_map, E₁.symm.norm_map] using D.le_opNorm (E₁.symm y)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (conjugate E₀ E₁ D))
    intro x
    have h := (conjugate E₀ E₁ D).le_opNorm (E₁ x)
    simpa only [conjugate_apply, E₁.symm_apply_apply, E₀.norm_map, E₁.norm_map] using h

theorem conjugate_query_difference (E₀ : H₀ ≃ₗᵢ[ℂ] K₀) (E₁ : H₁ ≃ₗᵢ[ℂ] K₁)
    (Γ : H₁ →L[ℂ] H₀) (U₀ : H₀ ≃ₗᵢ[ℂ] H₀) (U₁ : H₁ ≃ₗᵢ[ℂ] H₁) :
    conjugate E₀ E₁ Γ ∘L (transportUnitary E₁ U₁ : K₁ →L[ℂ] K₁) -
      (transportUnitary E₀ U₀ : K₀ →L[ℂ] K₀) ∘L conjugate E₀ E₁ Γ =
        conjugate E₀ E₁ (Γ ∘L (U₁ : H₁ →L[ℂ] H₁) - (U₀ : H₀ →L[ℂ] H₀) ∘L Γ) := by
  ext y
  change E₀ (Γ (E₁.symm (E₁ (U₁ (E₁.symm y))))) -
      E₀ (U₀ (E₀.symm (E₀ (Γ (E₁.symm y))))) =
        E₀ (Γ (U₁ (E₁.symm y)) - U₀ (Γ (E₁.symm y)))
  simp only [LinearIsometryEquiv.symm_apply_apply, map_sub]

end Conjugation

section RegisterSplit
variable {X ι H : Type*} [MeasurableSpace X] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def registerCoordinate (μ : Measure X) (i : ι) :
    Lp (Register ι H) 2 μ →L[ℂ] Lp H 2 μ :=
  (PiLp.proj 2 (fun _ : ι => H) i).compLpL 2 μ

omit [DecidableEq ι] in
theorem registerCoordinate_ae (μ : Measure X) (i : ι) (f : Lp (Register ι H) 2 μ) :
    registerCoordinate μ i f =ᵐ[μ] fun x => f x i :=
  (PiLp.proj (𝕜 := ℂ) 2 (fun _ : ι => H) i).coeFn_compLpL f

def registerSplitLinear (μ : Measure X) :
    Lp (Register ι H) 2 μ →ₗ[ℂ] Register ι (Lp H 2 μ) where
  toFun f := WithLp.toLp 2 (fun i => registerCoordinate μ i f)
  map_add' f g := by ext i; simp [map_add]
  map_smul' c f := by ext i; simp [map_smul]

omit [DecidableEq ι] in
private theorem registerCoordinate_square_integrable (μ : Measure X)
    (f : Lp (Register ι H) 2 μ) (i : ι) : Integrable (fun x => ‖f x i‖ ^ 2) μ := by
  have h := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (registerCoordinate μ i f))).mp
    (Lp.memLp (registerCoordinate μ i f))
  apply h.congr
  filter_upwards [registerCoordinate_ae μ i f] with x hx
  rw [hx]

omit [DecidableEq ι] in
theorem registerSplitLinear_norm (μ : Measure X) (f : Lp (Register ι H) 2 μ) :
    ‖registerSplitLinear μ f‖ = ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, prior_norm_sq]
  calc
    (∑ i, ‖registerCoordinate μ i f‖ ^ 2) = ∑ i, ∫ x, ‖f x i‖ ^ 2 ∂μ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [prior_norm_sq]
      apply integral_congr_ae
      filter_upwards [registerCoordinate_ae μ i f] with x hx
      rw [hx]
    _ = ∫ x, (∑ i, ‖f x i‖ ^ 2) ∂μ := by
      rw [integral_finset_sum _ (fun i _ => registerCoordinate_square_integrable μ f i)]
    _ = ∫ x, ‖f x‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => (PiLp.norm_sq_eq_of_L2 _ (f x)).symm)

def registerSingle (i : ι) : H →ₗᵢ[ℂ] Register ι H where
  toFun x := WithLp.toLp 2 (Pi.single i x)
  map_add' x y := by ext j; by_cases h : j = i <;> simp [h]
  map_smul' c x := by ext j; by_cases h : j = i <;> simp [h]
  norm_map' x := PiLp.norm_toLp_single 2 (fun _ : ι => H) i x

def registerMerge (μ : Measure X) (v : Register ι (Lp H 2 μ)) : Lp (Register ι H) 2 μ :=
  ∑ i, (registerSingle (H := H) i).toContinuousLinearMap.compLpL 2 μ (v i)

private theorem registerCoordinate_single (μ : Measure X) (i j : ι) (f : Lp H 2 μ) :
    registerCoordinate μ i ((registerSingle (H := H) j).toContinuousLinearMap.compLpL 2 μ f) =
      if i = j then f else 0 := by
  apply Lp.ext
  filter_upwards [registerCoordinate_ae μ i
    ((registerSingle (H := H) j).toContinuousLinearMap.compLpL 2 μ f),
    (registerSingle (H := H) j).toContinuousLinearMap.coeFn_compLpL f,
    Lp.coeFn_zero (E := H) (p := (2 : ℝ≥0∞)) (μ := μ)] with x hc hs hz
  rw [hc, hs]
  by_cases hij : i = j
  · subst j
    simp [registerSingle]
  · simp only [if_neg hij]
    change (registerSingle j (f x)) i = (0 : Lp H 2 μ) x
    rw [hz]
    simp [registerSingle, hij]

theorem registerSplit_merge (μ : Measure X) (v : Register ι (Lp H 2 μ)) :
    registerSplitLinear μ (registerMerge μ v) = v := by
  apply WithLp.ofLp_injective
  funext i
  change registerCoordinate μ i (∑ j,
    (registerSingle (H := H) j).toContinuousLinearMap.compLpL 2 μ (v j)) = v i
  rw [map_sum]
  simp [registerCoordinate_single]

/-- Splitting a finite physical register commutes with the continuous prior,
for arbitrary Hilbert-valued coordinates and arbitrary measures. -/
def registerSplit (μ : Measure X) :
    Lp (Register ι H) 2 μ ≃ₗᵢ[ℂ] Register ι (Lp H 2 μ) :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := registerSplitLinear μ, norm_map' := registerSplitLinear_norm μ }
    (fun v => ⟨registerMerge μ v, registerSplit_merge μ v⟩)

@[simp] theorem registerSplit_apply (μ : Measure X) (f : Lp (Register ι H) 2 μ) (i : ι) :
    registerSplit μ f i = registerCoordinate μ i f := rfl

end RegisterSplit

variable {X : Type*} [MeasurableSpace X]

def priorSplit (d M W : ℕ) (μ : Measure X) :
    Lp (SourceTargets.TestSpace d M W) 2 μ ≃ₗᵢ[ℂ]
      Register (Fin W) (Register Bool (Lp (PurificationSpace d M) 2 μ)) :=
  (registerSplit (ι := Fin W) (H := Register Bool (PurificationSpace d M)) μ).trans
    (LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Fin W =>
      registerSplit (ι := Bool) (H := PurificationSpace d M) μ))

@[simp] theorem priorSplit_apply (d M W : ℕ) (μ : Measure X)
    (f : Lp (SourceTargets.TestSpace d M W) 2 μ) (w : Fin W) (b : Bool) :
    priorSplit d M W μ f w b = registerCoordinate μ b (registerCoordinate μ w f) := rfl

section TensorTransport
variable {Y H ι : Type*} [MeasurableSpace Y] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {μ : Measure X} {ν : Measure Y}

/-- The scalar latent adversary on a physical register represented by an
actual finite Euclidean isometry. This is the circuit assembler's tensor. -/
def transportTensor (E : H ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι)
    (Γ : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ) : Lp H 2 ν →L[ℂ] Lp H 2 μ :=
  (lpTransport E μ).symm.toLinearIsometry.toContinuousLinearMap ∘L
    VectorPrior.tensor Γ ∘L (lpTransport E ν).toLinearIsometry.toContinuousLinearMap

/-- A fixed physical component, after undoing the finite-register flattening. -/
def componentMap (d M W : ℕ) (w : Fin W) (b : Bool) :
    EuclideanSpace ℂ (TestIndex d M W) →L[ℂ] PurificationSpace d M :=
  PiLp.proj 2 (fun _ : Bool => PurificationSpace d M) b ∘L
    PiLp.proj 2 (fun _ : Fin W => Register Bool (PurificationSpace d M)) w ∘L
      (flatten d M W).symm.toLinearIsometry.toContinuousLinearMap

theorem componentMap_transport (d M W : ℕ) (μ : Measure X) (w : Fin W) (b : Bool)
    (f : Lp (SourceTargets.TestSpace d M W) 2 μ) :
    (componentMap d M W w b).compLpL 2 μ (lpTransport (flatten d M W) μ f) =
      priorSplit d M W μ f w b := by
  apply Lp.ext
  filter_upwards [(componentMap d M W w b).coeFn_compLpL (lpTransport (flatten d M W) μ f),
    lpTransport_ae (flatten d M W) μ f,
    registerCoordinate_ae μ b (registerCoordinate μ w f),
    registerCoordinate_ae μ w f] with x hL hE hb hw
  rw [hL, hE]
  change ((flatten d M W).symm (flatten d M W (f x))) w b =
    (registerCoordinate μ b (registerCoordinate μ w f)) x
  rw [LinearIsometryEquiv.symm_apply_apply, hb, hw]

/-- The transported actual TestSpace tensor is the nested workspace lift
of the genuine base-query tensor. This is an equality of actual operators,
not an assumed factorization of a query norm. -/
theorem priorSplit_tensor (d M W : ℕ)
    (Γ : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ) (f : Lp (SourceTargets.TestSpace d M W) 2 ν) :
    priorSplit d M W μ (transportTensor (flatten d M W) Γ f) =
      workspaceOperator (ι := Fin W)
        (workspaceOperator (ι := Bool) (VectorPrior.tensor (ι := HQ d M) Γ))
          (priorSplit d M W ν f) := by
  apply WithLp.ofLp_injective
  funext w
  apply WithLp.ofLp_injective
  funext b
  change priorSplit d M W μ (transportTensor (flatten d M W) Γ f) w b =
    VectorPrior.tensor (ι := HQ d M) Γ (priorSplit d M W ν f w b)
  rw [← componentMap_transport, ← componentMap_transport]
  have h := DFunLike.congr_fun
    (VectorPrior.tensor_natural Γ (componentMap d M W w b)) (lpTransport (flatten d M W) ν f)
  change (componentMap d M W w b).compLpL 2 μ
      (lpTransport (flatten d M W) μ
        ((lpTransport (flatten d M W) μ).symm
          (VectorPrior.tensor Γ (lpTransport (flatten d M W) ν f)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact h.symm

end TensorTransport

section RegisterFields
variable {ι H : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem registerSplit_workspace_lift (μ : Measure X) (U : PointwiseUnitary μ H)
    (f : Lp (Register ι H) 2 μ) :
    registerSplit μ ((U.withWorkspace (ι := ι)).lift f) =
      withWorkspace (ι := ι) U.lift (registerSplit μ f) := by
  apply WithLp.ofLp_injective
  funext i
  change registerCoordinate μ i ((U.withWorkspace (ι := ι)).lift f) =
    U.lift (registerCoordinate μ i f)
  apply Lp.ext
  filter_upwards [registerCoordinate_ae μ i ((U.withWorkspace (ι := ι)).lift f),
    (U.withWorkspace (ι := ι)).lift_apply_ae f,
    U.lift_apply_ae (registerCoordinate μ i f), registerCoordinate_ae μ i f] with x hc hW hU hf
  rw [hc, hW, hU, hf]
  rfl

theorem registerSplit_controlled_lift (μ : Measure X) (U : PointwiseUnitary μ H)
    (f : Lp (Register Bool H) 2 μ) :
    registerSplit μ (U.controlled.lift f) = controlled U.lift (registerSplit μ f) := by
  apply WithLp.ofLp_injective
  funext b
  cases b
  · change registerCoordinate μ false (U.controlled.lift f) = registerCoordinate μ false f
    apply Lp.ext
    filter_upwards [registerCoordinate_ae μ false (U.controlled.lift f),
      U.controlled.lift_apply_ae f, registerCoordinate_ae μ false f] with x hc hU hf
    rw [hc, hU, hf]
    change controlled (U.unitary x) (f x) false = f x false
    exact controlled_false _ _
  · change registerCoordinate μ true (U.controlled.lift f) = U.lift (registerCoordinate μ true f)
    apply Lp.ext
    filter_upwards [registerCoordinate_ae μ true (U.controlled.lift f),
      U.controlled.lift_apply_ae f, U.lift_apply_ae (registerCoordinate μ true f),
      registerCoordinate_ae μ true f] with x hc hC hU hf
    rw [hc, hC, hU, hf]
    change controlled (U.unitary x) (f x) true = U.unitary x (f x true)
    exact controlled_true _ _

end RegisterFields

def testField (d M W : ℕ) {μ : Measure X} (U : PointwiseUnitary μ (PurificationSpace d M)) :
    PointwiseUnitary μ (SourceTargets.TestSpace d M W) :=
  U.controlled.withWorkspace (ι := Fin W)

theorem priorSplit_test_lift (d M W : ℕ) (μ : Measure X)
    (U : PointwiseUnitary μ (PurificationSpace d M))
    (f : Lp (SourceTargets.TestSpace d M W) 2 μ) :
    priorSplit d M W μ ((testField d M W U).lift f) =
      withWorkspace (ι := Fin W) (controlled U.lift) (priorSplit d M W μ f) := by
  change (LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Fin W =>
    registerSplit (ι := Bool) (H := PurificationSpace d M) μ))
      (registerSplit μ ((U.controlled.withWorkspace (ι := Fin W)).lift f)) = _
  rw [registerSplit_workspace_lift]
  apply WithLp.ofLp_injective
  funext w
  change registerSplit μ (U.controlled.lift (registerCoordinate μ w f)) =
    controlled U.lift (registerSplit μ (registerCoordinate μ w f))
  exact registerSplit_controlled_lift μ U _

theorem testField_lift_eq_transport (d M W : ℕ) (μ : Measure X)
    (U : PointwiseUnitary μ (PurificationSpace d M)) :
    (testField d M W U).lift = transportUnitary (priorSplit d M W μ).symm
      (withWorkspace (ι := Fin W) (controlled U.lift)) := by
  apply LinearIsometryEquiv.ext
  intro f
  apply (priorSplit d M W μ).injective
  rw [priorSplit_test_lift]
  simp only [transportUnitary_apply, LinearIsometryEquiv.symm_symm,
    LinearIsometryEquiv.apply_symm_apply]

section PhysicalQueryBound
variable {Y : Type*} [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}

theorem transportTensor_eq_conjugate_nested (d M W : ℕ)
    (Γ : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ) :
    transportTensor (flatten d M W) Γ =
      conjugate (priorSplit d M W μ).symm (priorSplit d M W ν).symm
        (workspaceOperator (ι := Fin W)
          (workspaceOperator (ι := Bool) (VectorPrior.tensor (ι := HQ d M) Γ))) := by
  apply ContinuousLinearMap.ext
  intro f
  apply (priorSplit d M W μ).injective
  simpa only [conjugate_apply, LinearIsometryEquiv.symm_symm,
    LinearIsometryEquiv.apply_symm_apply] using priorSplit_tensor d M W Γ f

/-- The actual controlled/workspace oracle query on the physical TestSpace
has no larger adversary norm than the actual base full-query operator.
Every factor and every prior lift in this statement is constructed above. -/
theorem physical_query_bound (d M W : ℕ)
    (Γ : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ)
    (U₀ : PointwiseUnitary μ (PurificationSpace d M))
    (U₁ : PointwiseUnitary ν (PurificationSpace d M)) {B : ℝ}
    (hbase : ‖VectorPrior.tensor (ι := HQ d M) Γ ∘L
        (U₁.lift : Lp (PurificationSpace d M) 2 ν →L[ℂ] Lp (PurificationSpace d M) 2 ν) -
      (U₀.lift : Lp (PurificationSpace d M) 2 μ →L[ℂ] Lp (PurificationSpace d M) 2 μ) ∘L
        VectorPrior.tensor (ι := HQ d M) Γ‖ ≤ B) :
    ‖transportTensor (flatten d M W) Γ ∘L
        ((testField d M W U₁).lift : Lp (SourceTargets.TestSpace d M W) 2 ν →L[ℂ]
          Lp (SourceTargets.TestSpace d M W) 2 ν) -
      ((testField d M W U₀).lift : Lp (SourceTargets.TestSpace d M W) 2 μ →L[ℂ]
          Lp (SourceTargets.TestSpace d M W) 2 μ) ∘L transportTensor (flatten d M W) Γ‖ ≤ B := by
  have hc := controlled_query_bound (VectorPrior.tensor (ι := HQ d M) Γ) U₀.lift U₁.lift hbase
  have hw := workspace_query_bound (ι := Fin W)
    (workspaceOperator (ι := Bool) (VectorPrior.tensor (ι := HQ d M) Γ))
    (controlled U₀.lift) (controlled U₁.lift) hc
  simpa only [transportTensor_eq_conjugate_nested, testField_lift_eq_transport,
    conjugate_query_difference, norm_conjugate] using hw

end PhysicalQueryBound

end PUT.PhysicalRegisters
