import PUT.FourierPreparation
import PUT.ReflectionOracle
import PUT.OperatorBridge
import PUT.VectorPrior
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# Physical reflection oracles for the actual phase-torus priors

The full physical unitary is reflection in the span of `(bot+v)/sqrt(2)`.
This definition is a unitary for every ambient parameter, including points
outside the simplex. On valid probability vectors its action is exactly
paper (3), and it prepares the required phase-randomized purification.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace PUT.PhysicalOracles
open QueryModel FourierModel FourierPreparation

abbrev Physical (ι : Type*) [Fintype ι] := EuclideanSpace ℂ (Unit ⊕ ι)

def bot {ι : Type*} [Fintype ι] [DecidableEq ι] : Physical ι :=
  EuclideanSpace.single (Sum.inl ()) 1

def output {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) : Physical ι :=
  WithLp.toLp 2 (Sum.elim (fun _ => 0) v)

def source {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) : Physical ι :=
  ((1 / Real.sqrt 2 : ℝ) : ℂ) • (bot + output v)

@[simp] theorem source_bot {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) (u : Unit) :
    source v (Sum.inl u) = ((1 / Real.sqrt 2 : ℝ) : ℂ) := by
  cases u
  simp [source, bot, output, EuclideanSpace.single_apply]

@[simp] theorem source_output {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) (q : ι) :
    source v (Sum.inr q) = ((1 / Real.sqrt 2 : ℝ) : ℂ) * v q := by
  simp [source, bot, output, EuclideanSpace.single_apply]

theorem source_norm {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℂ)
    (hv : ∑ q, ‖v q‖ ^ 2 = 1) : ‖source v‖ = 1 := by
  have hc : (1 / Real.sqrt 2 : ℝ) ^ 2 = 1 / 2 := by
    norm_num [div_pow]
  have hs : ‖source v‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type]
    simp only [source_bot, source_output, norm_mul, mul_pow, Complex.norm_real,
      Real.norm_eq_abs, sq_abs, hc, Fintype.sum_unique]
    rw [← Finset.mul_sum, hv]
    norm_num
  nlinarith [norm_nonneg (source v)]

/-- A genuine physical unitary, even outside the normalized parameter set. -/
def unitary {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) : Physical ι ≃ₗᵢ[ℂ] Physical ι :=
  (ℂ ∙ source v).reflection

@[simp] theorem unitary_symm {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) :
    (unitary v).symm = unitary v := Submodule.reflection_symm

def dotOutput {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) (x : Physical ι) : ℂ :=
  ∑ q, conj (v q) * x (Sum.inr q)

theorem source_inner {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) (x : Physical ι) :
    inner ℂ (source v) x = ((1 / Real.sqrt 2 : ℝ) : ℂ) *
      (x (Sum.inl ()) + dotOutput v x) := by
  rw [PiLp.inner_apply, Fintype.sum_sum_type]
  simp only [RCLike.inner_apply', source_bot, source_output, map_mul,
    Complex.conj_ofReal, Fintype.sum_unique, dotOutput]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, mul_add]

theorem unitary_apply_bot_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℂ)
    (hv : ∑ q, ‖v q‖ ^ 2 = 1) (x : Physical ι) :
    unitary v x (Sum.inl ()) = dotOutput v x := by
  rw [unitary, Submodule.reflection_singleton_apply, source_norm v hv]
  simp only [RCLike.ofReal_one, one_pow, div_one, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul, source_bot, source_inner, two_smul]
  have hc := two_mul_inv_sqrt_two_sq
  linear_combination hc * (x (Sum.inl ()) + dotOutput v x)

theorem unitary_apply_output_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℂ)
    (hv : ∑ q, ‖v q‖ ^ 2 = 1) (x : Physical ι) (q : ι) :
    unitary v x (Sum.inr q) =
      v q * x (Sum.inl ()) + v q * dotOutput v x - x (Sum.inr q) := by
  rw [unitary, Submodule.reflection_singleton_apply, source_norm v hv]
  simp only [RCLike.ofReal_one, one_pow, div_one, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul, source_output, source_inner, two_smul]
  have hc := two_mul_inv_sqrt_two_sq
  linear_combination hc * (x (Sum.inl ()) + dotOutput v x) * v q

theorem unitary_prepares {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℂ)
    (hv : ∑ q, ‖v q‖ ^ 2 = 1) : unitary v bot = output v := by
  ext q
  cases q with
  | inl u =>
      cases u
      rw [unitary_apply_bot_coordinate v hv]
      simp [dotOutput, bot, output, EuclideanSpace.single_apply]
  | inr q =>
      rw [unitary_apply_output_coordinate v hv]
      simp [dotOutput, bot, output, EuclideanSpace.single_apply]

section Pointwise
variable {X H : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Measurability of singleton reflections uses their explicit formula;
the inverse norm in that formula is measurable also at zero. -/
theorem reflection_aestronglyMeasurable (s f : X → H)
    (hs : AEStronglyMeasurable s μ) (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => (ℂ ∙ s x).reflection (f x)) μ := by
  have hn : AEMeasurable (fun x => ((‖s x‖ : ℝ) : ℂ) ^ 2) μ :=
    (Complex.measurable_ofReal.comp_aemeasurable hs.norm.aemeasurable).pow_const 2
  have hc : AEStronglyMeasurable
      (fun x => inner ℂ (s x) (f x) / ((‖s x‖ : ℝ) : ℂ) ^ 2) μ :=
    ((hs.inner hf).aemeasurable.div hn).aestronglyMeasurable
  have ht := hc.smul hs
  apply (ht.add ht |>.sub hf).congr
  filter_upwards [] with x
  simp [Submodule.reflection_singleton_apply, two_smul, add_smul]

/-- Every measurable vector field gives a pointwise unitary field. -/
def reflectionField (s : X → H) (hs : AEStronglyMeasurable s μ) :
    PointwiseUnitary μ H where
  unitary x := (ℂ ∙ s x).reflection
  measurable f hf := reflection_aestronglyMeasurable s f hs hf
  inverse_measurable f hf := by
    simpa only [Submodule.reflection_symm] using reflection_aestronglyMeasurable s f hs hf

end Pointwise

section PreparationField
variable {X ι : Type*} [MeasurableSpace X] [Fintype ι] [DecidableEq ι] {μ : Measure X}

private theorem source_eq_sum (v : ι → ℂ) :
    source v = ((1 / Real.sqrt 2 : ℝ) : ℂ) •
      (bot + ∑ q, v q • EuclideanSpace.single (Sum.inr q) 1) := by
  unfold source
  congr 1
  congr 1
  ext q
  change output v q = (EuclideanSpace.proj q) (∑ j, v j • EuclideanSpace.single (Sum.inr j) 1)
  rw [map_sum]
  cases q with
  | inl u => simp [output, EuclideanSpace.single_apply]
  | inr q => simp [output, EuclideanSpace.single_apply]

theorem source_field_measurable (v : Preparation μ ι) :
    AEStronglyMeasurable (fun x => source (fun q => v.amplitude q x)) μ := by
  have hs : AEStronglyMeasurable
      (fun x => ∑ q, v.amplitude q x •
        EuclideanSpace.single (Sum.inr q : Unit ⊕ ι) (1 : ℂ)) μ := by
    apply Finset.aestronglyMeasurable_fun_sum
    intro q _
    exact (v.measurable q).smul
      (aestronglyMeasurable_const (b := EuclideanSpace.single (Sum.inr q : Unit ⊕ ι) (1 : ℂ)))
  have hb : AEStronglyMeasurable (fun _ : X => (bot : Physical ι)) μ :=
    aestronglyMeasurable_const
  have ht := (hb.add hs).const_smul (((1 / Real.sqrt 2 : ℝ) : ℂ))
  apply ht.congr
  exact Filter.Eventually.of_forall (fun x => (source_eq_sum (fun q => v.amplitude q x)).symm)

def preparationField (v : Preparation μ ι) : PointwiseUnitary μ (Physical ι) :=
  reflectionField (fun x => source (fun q => v.amplitude q x)) (source_field_measurable v)

end PreparationField

/-- The actual null-prior reflection field, indexed by the phase torus. -/
def U0 {d M : ℕ} (hd : 0 < d) (hM : 0 < M) :
    PointwiseUnitary (phaseMeasure d M) (PurificationSpace d M) :=
  preparationField (nullPreparation d M hd hM)

/-- The actual alternative-prior reflection field on the entire ambient
parameter space. Invalid ambient probabilities still give unitary operators. -/
def U1 {d M : ℕ} {a : ℝ} (hd : 0 < d) (ha : 0 < a) (hM : 0 < M) :
    PointwiseUnitary (alternativeMeasure d M a) (PurificationSpace d M) :=
  preparationField (alternativePreparation d M a hd ha hM)

/-- Normalized phase garbage on the actual torus, including zero-probability
labels where the preparation condition still requires a unit vector. -/
def garbage {d M : ℕ} (θ : Torus d M) (i : Fin d) : EuclideanSpace ℂ (Fin M) :=
  WithLp.toLp 2 (fun j => ((1 / Real.sqrt M : ℝ) : ℂ) * phase (i,j) θ)

theorem garbage_norm {d M : ℕ} (hM : 0 < M) (θ : Torus d M) (i : Fin d) :
    ‖garbage θ i‖ = 1 := by
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hs : ‖garbage θ i‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [garbage, PiLp.toLp_apply, norm_mul, phase_norm, mul_one,
      Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, one_pow,
      Real.sq_sqrt (Nat.cast_nonneg M), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  nlinarith [norm_nonneg (garbage θ i)]

theorem alternative_normalized {d M : ℕ} (hM : 0 < M)
    (p : Fin d → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (θ : Torus d M) :
    ∑ q : Coord d M, ‖altAmplitude q (p,θ)‖ ^ 2 = 1 := by
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have he (q : Coord d M) : ‖altAmplitude q (p,θ)‖ ^ 2 = p q.1 / M := by
    simp only [altAmplitude, norm_mul, phase_norm, mul_one, Complex.norm_real,
      Real.norm_eq_abs, sq_abs, div_pow]
    rw [Real.sq_sqrt (hp q.1), Real.sq_sqrt (Nat.cast_nonneg M)]
  simp only [he, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_div_cancel₀ _ hm]
  exact hsum

/-- A valid preparation oracle for every actual probability vector and every
actual torus phase, with the entire physical reflection action retained. -/
def preparationOracle {d M : ℕ} (p : Fin d → ℝ) (θ : Torus d M)
    (hM : 0 < M) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    PreparationOracle d M where
  unitary := unitary (fun q => altAmplitude q (p,θ))
  probability := p
  nonnegative := hp
  total := hsum
  garbage := garbage θ
  garbage_norm := garbage_norm hM θ
  preparation_bot := by
    change unitary (fun q => altAmplitude q (p,θ)) bot (Sum.inl ()) = 0
    rw [unitary_prepares _ (alternative_normalized hM p hp hsum θ)]
    rfl
  preparation_output := by
    intro i j
    change unitary (fun q => altAmplitude q (p,θ)) bot (Sum.inr (i,j)) = _
    rw [unitary_prepares _ (alternative_normalized hM p hp hsum θ)]
    simp only [output, altAmplitude, garbage, PiLp.toLp_apply, Sum.elim_inr, Complex.ofReal_div,
      Complex.ofReal_one]
    ring

theorem uniform_amplitude {d M : ℕ} (θ : Torus d M) (q : Coord d M) :
    altAmplitude q (uniform d, θ) = nullAmplitude q θ := by
  change ((Real.sqrt (1 / (d : ℝ)) / Real.sqrt M : ℝ) : ℂ) * phase q θ =
    ((1 / (Real.sqrt d * Real.sqrt M) : ℝ) : ℂ) * phase q θ
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one, div_div]

/-- The null field is a valid oracle for the uniform distribution. -/
def nullOracle {d M : ℕ} (hd : 0 < d) (hM : 0 < M) (θ : Torus d M) :
    PreparationOracle d M :=
  preparationOracle (uniform d) θ hM (fun _ => by unfold uniform; positivity)
    (by simp [uniform, hd.ne'])

@[simp] theorem nullOracle_probability {d M : ℕ} (hd : 0 < d) (hM : 0 < M)
    (θ : Torus d M) : (nullOracle hd hM θ).probability = uniform d := rfl

theorem U0_unitary_nullOracle {d M : ℕ} (hd : 0 < d) (hM : 0 < M) (θ : Torus d M) :
    (U0 hd hM).unitary θ = (nullOracle hd hM θ).unitary := by
  change unitary (fun q => nullAmplitude q θ) = unitary (fun q => altAmplitude q (uniform d, θ))
  congr 1
  funext q
  exact (uniform_amplitude θ q).symm

/-- On every valid probability vector, the alternative field is exactly the
valid preparation oracle, including its full physical unitary action. -/
theorem U1_unitary_preparationOracle {d M : ℕ} {a : ℝ} (hd : 0 < d) (ha : 0 < a)
    (hM : 0 < M) (p : Fin d → ℝ) (θ : Torus d M)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    (U1 hd ha hM).unitary (p,θ) = (preparationOracle p θ hM hp hsum).unitary := rfl

section Erasure
variable {X ι : Type*} [MeasurableSpace X] [Fintype ι] [DecidableEq ι] {μ : Measure X}

/-- Conjugating a physical amplitude gives the actual erasure multiplier. -/
def conjugateMultiplier (b : Multiplier μ) : Multiplier μ where
  value x := conj (b.value x)
  measurable := continuous_star.comp_aestronglyMeasurable b.measurable
  bound := by simpa using b.bound

theorem multiplier_adjoint (b : Multiplier μ) :
    b.map.adjoint = (conjugateMultiplier b).map := by
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_left ℂ
  intro f
  rw [ContinuousLinearMap.adjoint_inner_right, L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [b.map_ae f, (conjugateMultiplier b).map_ae g] with x hf hg
  rw [hf, hg]
  simp [RCLike.inner_apply', conjugateMultiplier, mul_comm, mul_left_comm, mul_assoc]

/-- Actual global erasure operator, assembled from conjugate multipliers. -/
def erase (v : Preparation μ ι) : Register ι (Lp ℂ 2 μ) →L[ℂ] Lp ℂ 2 μ :=
  ∑ q, (conjugateMultiplier (v.multiplier q)).map ∘L
    PiLp.proj 2 (fun _ : ι => Lp ℂ 2 μ) q

theorem preparation_adjoint_eq_erase (v : Preparation μ ι) :
    v.isometry.toContinuousLinearMap.adjoint = erase v := by
  apply ContinuousLinearMap.ext
  intro h
  apply ext_inner_left ℂ
  intro f
  rw [ContinuousLinearMap.adjoint_inner_right, PiLp.inner_apply]
  simp only [erase, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    inner_sum]
  apply Finset.sum_congr rfl
  intro q _
  change inner ℂ ((v.multiplier q).map f) (h q) =
    inner ℂ f ((conjugateMultiplier (v.multiplier q)).map (h q))
  rw [← multiplier_adjoint, ContinuousLinearMap.adjoint_inner_right]

/-- Coercing a finite sum of scalar L² vectors commutes with the sum a.e. -/
theorem lp_sum_ae (f : ι → Lp ℂ 2 μ) :
    ((∑ q, f q) : Lp ℂ 2 μ) =ᵐ[μ] (fun x => ∑ q, f q x) := by
  have hs (t : Finset ι) : ((∑ q ∈ t, f q) : Lp ℂ 2 μ) =ᵐ[μ] fun x => ∑ q ∈ t, f q x := by
    induction t using Finset.induction_on with
    | empty => simpa using (Lp.coeFn_zero (α := X) (E := ℂ) (p := 2) (μ := μ))
    | @insert q t hqt ih =>
        simp only [Finset.sum_insert hqt]
        filter_upwards [Lp.coeFn_add (f q) (∑ r ∈ t, f r), ih] with x ha ht
        simp only [ha, ht, Pi.add_apply]
  exact hs Finset.univ

theorem erase_apply_ae (v : Preparation μ ι) (h : Register ι (Lp ℂ 2 μ)) :
    erase v h =ᵐ[μ] fun x => ∑ q, conj (v.amplitude q x) * h q x := by
  have hs := lp_sum_ae (fun q => (conjugateMultiplier (v.multiplier q)).map (h q))
  have hm : ∀ᵐ x ∂μ, ∀ q,
      (conjugateMultiplier (v.multiplier q)).map (h q) x =
        conj (v.amplitude q x) * h q x :=
    Filter.eventually_all.mpr (fun q => (conjugateMultiplier (v.multiplier q)).map_ae (h q))
  simp only [erase, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    PiLp.proj_apply]
  change ((∑ q, (conjugateMultiplier (v.multiplier q)).map (h q)) : Lp ℂ 2 μ) =ᵐ[μ] _
  filter_upwards [hs, hm] with x hsum hmul
  rw [hsum]
  simp only [hmul]

theorem reflectionBlock_bot_ae (v : Preparation μ ι)
    (x : WithLp 2 (Lp ℂ 2 μ × Register ι (Lp ℂ 2 μ))) :
    (OperatorBridge.reflectionBlock v.isometry.toContinuousLinearMap x).fst =ᵐ[μ]
      fun z => ∑ q, conj (v.amplitude q z) * x.snd q z := by
  simpa only [OperatorBridge.reflectionBlock, OperatorBridge.block_apply,
    ContinuousLinearMap.zero_apply, zero_add, WithLp.toLp_fst,
    preparation_adjoint_eq_erase] using erase_apply_ae v x.snd

theorem reflectionBlock_output_ae (v : Preparation μ ι)
    (x : WithLp 2 (Lp ℂ 2 μ × Register ι (Lp ℂ 2 μ))) (q : ι) :
    (OperatorBridge.reflectionBlock v.isometry.toContinuousLinearMap x).snd q =ᵐ[μ]
      fun z => v.amplitude q z * x.fst z +
        v.amplitude q z * (∑ r, conj (v.amplitude r z) * x.snd r z) - x.snd q z := by
  have he := erase_apply_ae v x.snd
  have h₁ := (v.multiplier q).map_ae x.fst
  have h₂ := (v.multiplier q).map_ae (erase v x.snd)
  change ((v.multiplier q).map x.fst +
    ((v.multiplier q).map (v.isometry.toContinuousLinearMap.adjoint x.snd) - x.snd q)) =ᵐ[μ] _
  rw [preparation_adjoint_eq_erase]
  filter_upwards [he, h₁, h₂,
    Lp.coeFn_sub ((v.multiplier q).map (erase v x.snd)) (x.snd q),
    Lp.coeFn_add ((v.multiplier q).map x.fst)
      ((v.multiplier q).map (erase v x.snd) - x.snd q)] with z her hp hpe hsub hadd
  rw [hadd, Pi.add_apply, hsub, Pi.sub_apply, hp, hpe, her]
  dsimp [Preparation.multiplier]
  ring

end Erasure

section Flag
variable {ι H : Type*} [Fintype ι] [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- Separate the designated input flag in the genuine Euclidean direct sum. -/
def flagSplit : Register (Unit ⊕ ι) H ≃ₗᵢ[ℂ] WithLp 2 (H × Register ι H) where
  toFun x := WithLp.toLp 2 (x (Sum.inl ()), WithLp.toLp 2 (fun q => x (Sum.inr q)))
  invFun x := WithLp.toLp 2 (Sum.elim (fun _ => x.fst) (fun q => x.snd q))
  left_inv x := by
    ext q
    cases q with
    | inl u => cases u; rfl
    | inr q => rfl
  right_inv x := by
    apply WithLp.ofLp_injective
    apply Prod.ext
    · rfl
    · rfl
  map_add' x y := by
    apply WithLp.ofLp_injective
    apply Prod.ext
    · rfl
    · rfl
  map_smul' c x := by
    apply WithLp.ofLp_injective
    apply Prod.ext
    · rfl
    · rfl
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2,
      PiLp.norm_sq_eq_of_L2, Fintype.sum_sum_type]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, PiLp.toLp_apply, Fintype.sum_unique]
    rfl

@[simp] theorem flagSplit_fst (x : Register (Unit ⊕ ι) H) :
    (flagSplit x).fst = x (Sum.inl ()) := rfl

@[simp] theorem flagSplit_snd (x : Register (Unit ⊕ ι) H) (q : ι) :
    (flagSplit x).snd q = x (Sum.inr q) := rfl

end Flag

section LiftIdentification
variable {X ι : Type*} [MeasurableSpace X] [Fintype ι] [DecidableEq ι]

/-- The actual finite-coordinate and input-flag isometry for vector L². -/
def physicalSplit (μ : Measure X) : Lp (Physical ι) 2 μ ≃ₗᵢ[ℂ]
    WithLp 2 (Lp ℂ 2 μ × Register ι (Lp ℂ 2 μ)) :=
  (VectorPrior.split (ι := Unit ⊕ ι) μ).trans flagSplit

@[simp] theorem physicalSplit_fst (μ : Measure X) (f : Lp (Physical ι) 2 μ) :
    (physicalSplit μ f).fst = VectorPrior.coordinate μ (Sum.inl ()) f := rfl

@[simp] theorem physicalSplit_snd (μ : Measure X) (f : Lp (Physical ι) 2 μ) (q : ι) :
    (physicalSplit μ f).snd q = VectorPrior.coordinate μ (Sum.inr q) f := rfl

/-- The lift of the actual physical reflection is exactly the full block
reflection of the actual multiplication preparation isometry. -/
theorem physicalSplit_lift (μ : Measure X) (v : Preparation μ ι)
    (f : Lp (Physical ι) 2 μ) :
    physicalSplit μ ((preparationField v).lift f) =
      OperatorBridge.reflectionBlock v.isometry.toContinuousLinearMap (physicalSplit μ f) := by
  have hb := VectorPrior.coordinate_ae μ (Sum.inl ()) f
  have hc : ∀ᵐ z ∂μ, ∀ q : ι, (physicalSplit μ f).snd q z = f z (Sum.inr q) :=
    Filter.eventually_all.mpr (fun q => VectorPrior.coordinate_ae μ (Sum.inr q) f)
  apply WithLp.ofLp_injective
  apply Prod.ext
  · change VectorPrior.coordinate μ (Sum.inl ()) ((preparationField v).lift f) =
      (OperatorBridge.reflectionBlock v.isometry.toContinuousLinearMap (physicalSplit μ f)).fst
    apply Lp.ext
    filter_upwards [VectorPrior.coordinate_ae μ (Sum.inl ()) ((preparationField v).lift f),
      (preparationField v).lift_apply_ae f,
      reflectionBlock_bot_ae v (physicalSplit μ f), v.normalized, hc]
      with z hl hu hr hv hcoords
    rw [hl, hu, hr]
    change unitary (fun q => v.amplitude q z) (f z) (Sum.inl ()) = _
    rw [unitary_apply_bot_coordinate _ hv]
    simp only [dotOutput, hcoords]
  · apply PiLp.ext
    intro q
    change VectorPrior.coordinate μ (Sum.inr q) ((preparationField v).lift f) =
      (OperatorBridge.reflectionBlock v.isometry.toContinuousLinearMap (physicalSplit μ f)).snd q
    apply Lp.ext
    filter_upwards [VectorPrior.coordinate_ae μ (Sum.inr q) ((preparationField v).lift f),
      (preparationField v).lift_apply_ae f,
      reflectionBlock_output_ae v (physicalSplit μ f) q, v.normalized, hb, hc]
      with z hl hu hr hv hbot hcoords
    rw [hl, hu, hr]
    change unitary (fun r => v.amplitude r z) (f z) (Sum.inr q) = _
    rw [unitary_apply_output_coordinate _ hv]
    change v.amplitude q z * f z (Sum.inl ()) + v.amplitude q z * dotOutput _ (f z)
      - f z (Sum.inr q) = _
    simp only [dotOutput, physicalSplit_fst, hbot, hcoords]

theorem physicalSplit_lift_operator (μ : Measure X) (v : Preparation μ ι) :
    (physicalSplit (ι := ι) μ).toLinearIsometry.toContinuousLinearMap ∘L
      (preparationField v).lift.toLinearIsometry.toContinuousLinearMap =
    OperatorBridge.reflectionBlock v.isometry.toContinuousLinearMap ∘L
      (physicalSplit (ι := ι) μ).toLinearIsometry.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  exact physicalSplit_lift μ v

end LiftIdentification

theorem U0_lift_reflectionBlock {d M : ℕ} (hd : 0 < d) (hM : 0 < M)
    (f : Lp (PurificationSpace d M) 2 (phaseMeasure d M)) :
    physicalSplit (phaseMeasure d M) ((U0 hd hM).lift f) =
      OperatorBridge.reflectionBlock (V0 hd hM).toContinuousLinearMap
        (physicalSplit (phaseMeasure d M) f) :=
  physicalSplit_lift (phaseMeasure d M) (nullPreparation d M hd hM) f

theorem U1_lift_reflectionBlock {d M : ℕ} {a : ℝ}
    (hd : 0 < d) (ha : 0 < a) (hM : 0 < M)
    (f : Lp (PurificationSpace d M) 2 (alternativeMeasure d M a)) :
    physicalSplit (alternativeMeasure d M a) ((U1 hd ha hM).lift f) =
      OperatorBridge.reflectionBlock (V1 hd ha hM).toContinuousLinearMap
        (physicalSplit (alternativeMeasure d M a) f) :=
  physicalSplit_lift (alternativeMeasure d M a) (alternativePreparation d M a hd ha hM) f

end PUT.PhysicalOracles

namespace PUT.QueryModel

section RegisterFields
variable {X H ι : Type*} [MeasurableSpace X] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] {μ : Measure X} [Fintype ι] [DecidableEq ι]

private def registerSingle (i : ι) : H →L[ℂ] Register ι H :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.single ℂ (fun _ : ι => H) i

private theorem registerSingle_apply (i j : ι) (h : H) :
    registerSingle i h j = if j = i then h else 0 := by
  simp [registerSingle, Pi.single_apply]

/-- A finite Hilbert-valued register is strongly measurable whenever each
of its genuine Hilbert coordinates is strongly measurable. -/
theorem register_aestronglyMeasurable (g : X → Register ι H)
    (hg : ∀ i, AEStronglyMeasurable (fun x => g x i) μ) :
    AEStronglyMeasurable g μ := by
  have hs : AEStronglyMeasurable
      (fun x => ∑ i, registerSingle i (g x i)) μ :=
    Finset.aestronglyMeasurable_fun_sum Finset.univ (fun i _ =>
      (registerSingle i).continuous.comp_aestronglyMeasurable (hg i))
  have he : (fun x => ∑ i, registerSingle i (g x i)) = g := by
    funext x
    apply PiLp.ext
    intro j
    change (PiLp.proj (𝕜 := ℂ) 2 (fun _ : ι => H) j) (∑ i, registerSingle i (g x i)) = _
    rw [map_sum]
    simp only [PiLp.proj_apply, registerSingle_apply]
    simp
  rwa [he] at hs

/-- Extend the actual pointwise unitary by an arbitrary finite workspace. -/
def PointwiseUnitary.withWorkspace (U : PointwiseUnitary μ H) :
    PointwiseUnitary μ (Register ι H) where
  unitary x := QueryModel.withWorkspace (U.unitary x)
  measurable f hf := by
    apply register_aestronglyMeasurable
    intro i
    change AEStronglyMeasurable (fun x => U.unitary x (f x i)) μ
    exact U.measurable (fun x => f x i)
      ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : ι => H) i).continuous.comp_aestronglyMeasurable hf)
  inverse_measurable f hf := by
    apply register_aestronglyMeasurable
    intro i
    change AEStronglyMeasurable (fun x => (U.unitary x).symm (f x i)) μ
    exact U.inverse_measurable (fun x => f x i)
      ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : ι => H) i).continuous.comp_aestronglyMeasurable hf)

@[simp] theorem PointwiseUnitary.withWorkspace_unitary (U : PointwiseUnitary μ H)
    (x : X) : (U.withWorkspace (ι := ι)).unitary x =
      QueryModel.withWorkspace (ι := ι) (U.unitary x) := rfl

@[simp] theorem PointwiseUnitary.withWorkspace_unitary_apply
    (U : PointwiseUnitary μ H) (x : X) (f : Register ι H) (i : ι) :
    (U.withWorkspace (ι := ι)).unitary x f i = U.unitary x (f i) := rfl

end RegisterFields

section ControlField
variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] {μ : Measure X}

/-- The actual pointwise controlled call, with a measurable inverse. -/
def PointwiseUnitary.controlled (U : PointwiseUnitary μ H) :
    PointwiseUnitary μ (Register Bool H) where
  unitary x := QueryModel.controlled (U.unitary x)
  measurable f hf := by
    apply register_aestronglyMeasurable
    intro b
    cases b with
    | false =>
      simpa only [QueryModel.controlled_false] using
        (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Bool => H) false).continuous.comp_aestronglyMeasurable hf
    | true =>
      simpa only [QueryModel.controlled_true] using U.measurable (fun x => f x true)
        ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Bool => H) true).continuous.comp_aestronglyMeasurable hf)
  inverse_measurable f hf := by
    apply register_aestronglyMeasurable
    intro b
    cases b with
    | false =>
      change AEStronglyMeasurable (fun x => f x false) μ
      exact (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Bool => H) false).continuous.comp_aestronglyMeasurable hf
    | true =>
      change AEStronglyMeasurable (fun x => (U.unitary x).symm (f x true)) μ
      exact U.inverse_measurable (fun x => f x true)
        ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Bool => H) true).continuous.comp_aestronglyMeasurable hf)

@[simp] theorem PointwiseUnitary.controlled_unitary (U : PointwiseUnitary μ H)
    (x : X) : U.controlled.unitary x = QueryModel.controlled (U.unitary x) := rfl

@[simp] theorem PointwiseUnitary.controlled_unitary_false (U : PointwiseUnitary μ H)
    (x : X) (f : Register Bool H) : U.controlled.unitary x f false = f false := by
  simp

@[simp] theorem PointwiseUnitary.controlled_unitary_true (U : PointwiseUnitary μ H)
    (x : X) (f : Register Bool H) : U.controlled.unitary x f true = U.unitary x (f true) := by
  simp

end ControlField
end PUT.QueryModel

namespace PUT.PhysicalOracles

abbrev workspaceField := @QueryModel.PointwiseUnitary.withWorkspace
abbrev controlledField := @QueryModel.PointwiseUnitary.controlled

end PUT.PhysicalOracles
