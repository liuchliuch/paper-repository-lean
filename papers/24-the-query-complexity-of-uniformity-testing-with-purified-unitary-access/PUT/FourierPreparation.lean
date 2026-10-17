import PUT.FourierModel

/-!
# Pointwise preparation operators on the actual latent priors

The operators in this file act by multiplication by the physical oracle
amplitudes. They are constructed as genuine linear isometries, without
assuming an operator norm bound for a query difference.
-/
noncomputable section
namespace PUT.FourierPreparation
open MeasureTheory
open scoped ENNReal

section Multiplier
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

structure Multiplier (μ : Measure X) where
  value : X → ℂ
  measurable : AEStronglyMeasurable value μ
  bound : ∀ᵐ x ∂μ, ‖value x‖ ≤ 1

namespace Multiplier

def memLp (b : Multiplier μ) (h : Lp ℂ 2 μ) :
    MemLp (fun x => b.value x * h x) 2 μ := by
  apply (Lp.memLp h).mono (b.measurable.mul (Lp.aestronglyMeasurable h))
  filter_upwards [b.bound] with x hx
  change ‖b.value x * h x‖ ≤ ‖h x‖
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) hx

def applyFun (b : Multiplier μ) (h : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (b.memLp h).toLp (fun x => b.value x * h x)

theorem applyFun_ae (b : Multiplier μ) (h : Lp ℂ 2 μ) :
    b.applyFun h =ᵐ[μ] fun x => b.value x * h x := (b.memLp h).coeFn_toLp

def map (b : Multiplier μ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous
    { toFun := b.applyFun
      map_add' := by
        intro h g
        apply Lp.ext
        filter_upwards [b.applyFun_ae (h+g), b.applyFun_ae h, b.applyFun_ae g,
          Lp.coeFn_add h g, Lp.coeFn_add (b.applyFun h) (b.applyFun g)]
          with x hsum hh hg hi ho
        simp only [hsum, ho, hi, Pi.add_apply, hh, hg]
        ring
      map_smul' := by
        intro c h
        change b.applyFun (c • h) = c • b.applyFun h
        apply Lp.ext
        filter_upwards [b.applyFun_ae (c • h), b.applyFun_ae h,
          Lp.coeFn_smul c h, Lp.coeFn_smul c (b.applyFun h)] with x hsum hh hi ho
        simp only [hsum, ho, hi, Pi.smul_apply, smul_eq_mul, hh]
        ring }
    1 (by
      intro h
      simp only [one_mul]
      change ‖b.applyFun h‖ ≤ ‖h‖
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [b.applyFun_ae h, b.bound] with x hm hb
      rw [hm, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) hb)

theorem map_ae (b : Multiplier μ) (h : Lp ℂ 2 μ) :
    b.map h =ᵐ[μ] fun x => b.value x * h x := b.applyFun_ae h

end Multiplier

section Preparation
variable {ι : Type*} [Fintype ι]

/-- A finite field of physical unit vectors. -/
structure Preparation (μ : Measure X) (ι : Type*) [Fintype ι] where
  amplitude : ι → X → ℂ
  measurable : ∀ q, AEStronglyMeasurable (amplitude q) μ
  normalized : ∀ᵐ x ∂μ, ∑ q, ‖amplitude q x‖ ^ 2 = 1

def Preparation.multiplier (v : Preparation μ ι) (q : ι) : Multiplier μ where
  value := v.amplitude q
  measurable := v.measurable q
  bound := by
    filter_upwards [v.normalized] with x hx
    have hq : ‖v.amplitude q x‖ ^ 2 ≤ 1 := by
      rw [← hx]
      exact Finset.single_le_sum (fun (t : ι) _ => sq_nonneg (‖v.amplitude t x‖)) (Finset.mem_univ q)
    nlinarith [norm_nonneg (v.amplitude q x)]

def Preparation.applyFun (v : Preparation μ ι) (h : Lp ℂ 2 μ) :
    QueryModel.Register ι (Lp ℂ 2 μ) :=
  WithLp.toLp 2 (fun q => (v.multiplier q).map h)

theorem Preparation.applyFun_norm (v : Preparation μ ι) (h : Lp ℂ 2 μ) :
    ‖v.applyFun h‖ = ‖h‖ := by
  have hsq : ‖v.applyFun h‖ ^ 2 = ‖h‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, QueryModel.prior_norm_sq]
    change (∑ q, ‖(v.multiplier q).map h‖ ^ 2) = _
    simp_rw [QueryModel.prior_norm_sq]
    rw [← integral_finset_sum]
    · apply integral_congr_ae
      have hm : ∀ᵐ x ∂μ, ∀ q, (v.multiplier q).map h x = v.amplitude q x * h x :=
        Filter.eventually_all.mpr (fun q => (v.multiplier q).map_ae h)
      filter_upwards [hm, v.normalized] with x hmul hn
      simp only [hmul, norm_mul, mul_pow]
      rw [← Finset.sum_mul, hn, one_mul]
    · intro q _
      exact (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable
        ((v.multiplier q).map h))).mp (Lp.memLp ((v.multiplier q).map h))
  nlinarith [norm_nonneg (v.applyFun h), norm_nonneg h]

/-- The actual isometric operator `h↦h|v⟩` on the inaccessible latent space. -/
def Preparation.isometry (v : Preparation μ ι) :
    Lp ℂ 2 μ →ₗᵢ[ℂ] QueryModel.Register ι (Lp ℂ 2 μ) where
  toFun := v.applyFun
  map_add' h g := by
    apply WithLp.ofLp_injective
    funext q
    exact map_add (v.multiplier q).map h g
  map_smul' c h := by
    apply WithLp.ofLp_injective
    funext q
    exact map_smul (v.multiplier q).map c h
  norm_map' := v.applyFun_norm

end Preparation
end Multiplier


open FourierModel
attribute [local instance] Real.fact_zero_lt_one

/-- Unit phase in physical output coordinate `(i,j)`. -/
def phase {d M : ℕ} (q : Coord d M) (θ : Torus d M) : ℂ := fourier 1 (θ q)

@[simp] theorem phase_norm {d M : ℕ} (q : Coord d M) (θ : Torus d M) :
    ‖phase q θ‖ = 1 := by
  simp [phase, fourier_apply]

def nullAmplitude {d M : ℕ} (q : Coord d M) (θ : Torus d M) : ℂ :=
  ((1 / (Real.sqrt d * Real.sqrt M) : ℝ) : ℂ) * phase q θ

def altAmplitude {d M : ℕ} (q : Coord d M) (x : (Fin d → ℝ) × Torus d M) : ℂ :=
  ((Real.sqrt (x.1 q.1) / Real.sqrt M : ℝ) : ℂ) * phase q x.2

theorem altAmplitude_norm_sq {d M : ℕ} (hM : 0 < M) (q : Coord d M)
    (x : (Fin d → ℝ) × Torus d M) (hx : x.1 ∈ positiveSimplex d) :
    ‖altAmplitude q x‖ ^ 2 = x.1 q.1 / M := by
  simp only [altAmplitude, norm_mul, phase_norm, mul_one, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, div_pow]
  rw [Real.sq_sqrt (hx.1 q.1).le, Real.sq_sqrt (Nat.cast_nonneg M)]

def nullPreparation (d M : ℕ) (hd : 0 < d) (hM : 0 < M) :
    Preparation (phaseMeasure d M) (Coord d M) where
  amplitude := nullAmplitude
  measurable q := by
    exact (continuous_const.mul ((fourier 1).continuous.comp
      (continuous_apply q))).measurable.aestronglyMeasurable
  normalized := Filter.Eventually.of_forall (fun θ => by
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    have heq (q : Coord d M) : ‖nullAmplitude q θ‖ ^ 2 = 1 / ((d : ℝ) * M) := by
      simp only [nullAmplitude, norm_mul, phase_norm, mul_one, Complex.norm_real,
        Real.norm_eq_abs, sq_abs, div_pow, one_pow, mul_pow,
        Real.sq_sqrt (Nat.cast_nonneg d), Real.sq_sqrt (Nat.cast_nonneg M)]
    simp only [heq, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
    field_simp)

def alternativePreparation (d M : ℕ) (a : ℝ) (hd : 0 < d) (ha : 0 < a) (hM : 0 < M) :
    Preparation (alternativeMeasure d M a) (Coord d M) where
  amplitude := altAmplitude
  measurable q := by
    apply Measurable.aestronglyMeasurable
    apply Measurable.mul
    · exact Complex.measurable_ofReal.comp ((Real.continuous_sqrt.measurable.comp
        ((measurable_pi_apply q.1).comp measurable_fst)).div_const _)
    · exact (fourier 1).continuous.measurable.comp
        ((measurable_pi_apply q).comp measurable_snd)
  normalized := by
    filter_upwards [alternative_ae_simplex (M := M) hd ha] with x hx
    simp_rw [altAmplitude_norm_sq hM _ x hx]
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    simp only [mul_div_cancel₀ _ hMR]
    exact hx.2

def V0 {d M : ℕ} (hd : 0 < d) (hM : 0 < M) :
    NullL2 d M →ₗᵢ[ℂ] QueryModel.Register (Coord d M) (NullL2 d M) :=
  (nullPreparation d M hd hM).isometry

def V1 {d M : ℕ} {a : ℝ} (hd : 0 < d) (ha : 0 < a) (hM : 0 < M) :
    AltL2 d M a →ₗᵢ[ℂ] QueryModel.Register (Coord d M) (AltL2 d M a) :=
  (alternativePreparation d M a hd ha hM).isometry

theorem V0_apply_ae {d M : ℕ} (hd : 0 < d) (hM : 0 < M)
    (h : NullL2 d M) (q : Coord d M) :
    V0 hd hM h q =ᵐ[phaseMeasure d M] fun θ => nullAmplitude q θ * h θ :=
  ((nullPreparation d M hd hM).multiplier q).map_ae h

theorem V1_apply_ae {d M : ℕ} {a : ℝ} (hd : 0 < d) (ha : 0 < a) (hM : 0 < M)
    (h : AltL2 d M a) (q : Coord d M) :
    V1 hd ha hM h q =ᵐ[alternativeMeasure d M a] fun x => altAmplitude q x * h x :=
  ((alternativePreparation d M a hd ha hM).multiplier q).map_ae h

theorem V0_e {d M : ℕ} (hd : 0 < d) (hM : 0 < M)
    (n : PhaseIndex d M) (q : Coord d M) :
    V0 hd hM (e n) q =
      ((1 / (Real.sqrt d * Real.sqrt M) : ℝ) : ℂ) • e (shift n q.1 q.2) := by
  apply Lp.ext
  filter_upwards [V0_apply_ae hd hM (e n) q, e_ae n, e_ae (shift n q.1 q.2),
    Lp.coeFn_smul ((1 / (Real.sqrt d * Real.sqrt M) : ℝ) : ℂ) (e (shift n q.1 q.2))]
    with θ hv hn hs hsm
  rw [hv, hn, hsm, Pi.smul_apply, hs, smul_eq_mul, character_shift]
  simp only [nullAmplitude, phase]
  ring

/-- Exact creation/erasure Fourier shift of the actual preparation operator
on the whole radial sector, before choosing the principal moment vector. -/
theorem V1_sector {d M : ℕ} {a : ℝ} (hd : 0 < d) (ha : 0 < a) (hM : 0 < M)
    (n : PhaseIndex d M) (h : RadialL2 d a) (q : Coord d M) :
    V1 hd ha hM (sector ha n h) q =
      ((1 / Real.sqrt M : ℝ) : ℂ) •
        sector ha (shift n q.1 q.2) (sqrtMultiply hd ha q.1 h) := by
  apply Lp.ext
  have hmul := (Measure.quasiMeasurePreserving_fst (μ := dirichletMeasure d a)
    (ν := phaseMeasure d M)).ae_eq (sqrtMultiply_ae hd ha q.1 h)
  filter_upwards [V1_apply_ae hd ha hM (sectorFun n h) q, sectorFun_ae n h,
    sectorFun_ae (shift n q.1 q.2) (sqrtMultiply hd ha q.1 h),
    Lp.coeFn_smul ((1 / Real.sqrt M : ℝ) : ℂ)
      (sectorFun (shift n q.1 q.2) (sqrtMultiply hd ha q.1 h)), hmul]
      with x hv hn hs hsm hm
  change (sqrtMultiply hd ha q.1 h) x.1 = (Real.sqrt (x.1 q.1) : ℂ) * h x.1 at hm
  change (V1 hd ha hM (sectorFun n h) q) x =
    (((1 / Real.sqrt M : ℝ) : ℂ) • sectorFun (shift n q.1 q.2) (sqrtMultiply hd ha q.1 h)) x
  change (sectorFun n h) x = _ at hn
  rw [hv, hn, hsm, Pi.smul_apply, smul_eq_mul, hs]
  change altAmplitude q x * sectorFunction n h x =
    ((1 / Real.sqrt M : ℝ) : ℂ) * sectorFunction (shift n q.1 q.2) (sqrtMultiply hd ha q.1 h) x
  rw [sectorFunction, sectorFunction, hm, character_shift]
  simp only [altAmplitude, phase, Complex.ofReal_div, Complex.ofReal_one]
  ring


open scoped ComplexConjugate

@[simp] theorem phase_conj_mul {d M : ℕ} (q : Coord d M) (θ : Torus d M) :
    conj (phase q θ) * phase q θ = 1 := by
  rw [Complex.conj_mul', phase_norm]
  simp

/-- The exact null-side erasure multiplier on every Fourier mode. -/
theorem nullMultiplier_adjoint_e {d M : ℕ} (hd : 0 < d) (hM : 0 < M)
    (n : PhaseIndex d M) (q : Coord d M) :
    ((nullPreparation d M hd hM).multiplier q).map.adjoint (e (shift n q.1 q.2)) =
      ((1 / (Real.sqrt d * Real.sqrt M) : ℝ) : ℂ) • e n := by
  apply ext_inner_left ℂ
  intro g
  rw [ContinuousLinearMap.adjoint_inner_right, L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [((nullPreparation d M hd hM).multiplier q).map_ae g,
    e_ae (shift n q.1 q.2), e_ae n,
    Lp.coeFn_smul ((1 / (Real.sqrt d * Real.sqrt M) : ℝ) : ℂ) (e n)]
      with θ hv hs hn hsm
  change (((nullPreparation d M hd hM).multiplier q).map g) θ = nullAmplitude q θ * g θ at hv
  rw [hv, hs, hsm, Pi.smul_apply, hn, character_shift]
  simp only [RCLike.inner_apply, nullAmplitude, map_mul, Complex.conj_ofReal, smul_eq_mul]
  calc
    _ = (((1 / (Real.sqrt d * Real.sqrt M) : ℝ) : ℂ) * character n θ * conj (g θ)) *
        (conj (phase q θ) * phase q θ) := by dsimp only [phase]; ring
    _ = _ := by rw [phase_conj_mul, mul_one]

/-- The exact alternative-side erasure on an arbitrary radial vector,
including the full radial complement. -/
theorem altMultiplier_adjoint_sector {d M : ℕ} {a : ℝ}
    (hd : 0 < d) (ha : 0 < a) (hM : 0 < M)
    (n : PhaseIndex d M) (h : RadialL2 d a) (q : Coord d M) :
    ((alternativePreparation d M a hd ha hM).multiplier q).map.adjoint
        (sector ha (shift n q.1 q.2) h) =
      ((1 / Real.sqrt M : ℝ) : ℂ) • sector ha n (sqrtMultiply hd ha q.1 h) := by
  apply ext_inner_left ℂ
  intro g
  change inner ℂ g (((alternativePreparation d M a hd ha hM).multiplier q).map.adjoint
      (sectorFun (shift n q.1 q.2) h)) =
    inner ℂ g (((1 / Real.sqrt M : ℝ) : ℂ) • sectorFun n (sqrtMultiply hd ha q.1 h))
  rw [ContinuousLinearMap.adjoint_inner_right, L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  have hmul := (Measure.quasiMeasurePreserving_fst (μ := dirichletMeasure d a)
    (ν := phaseMeasure d M)).ae_eq (sqrtMultiply_ae hd ha q.1 h)
  filter_upwards [((alternativePreparation d M a hd ha hM).multiplier q).map_ae g,
    sectorFun_ae (shift n q.1 q.2) h, sectorFun_ae n (sqrtMultiply hd ha q.1 h),
    Lp.coeFn_smul ((1 / Real.sqrt M : ℝ) : ℂ) (sectorFun n (sqrtMultiply hd ha q.1 h)), hmul]
      with x hv hs hn hsm hm
  change (((alternativePreparation d M a hd ha hM).multiplier q).map g) x =
    altAmplitude q x * g x at hv
  change (sqrtMultiply hd ha q.1 h) x.1 = (Real.sqrt (x.1 q.1) : ℂ) * h x.1 at hm
  rw [hv, hs, hsm, Pi.smul_apply, hn, sectorFunction, sectorFunction, hm, character_shift]
  simp only [RCLike.inner_apply, altAmplitude, map_mul, Complex.conj_ofReal, smul_eq_mul,
    Complex.ofReal_div, Complex.ofReal_one]
  simp only [map_div₀, Complex.conj_ofReal]
  calc
    _ = ((1 / (Real.sqrt M : ℂ)) *
        (((Real.sqrt (x.1 q.1) : ℂ) * h x.1) * character n x.2) * conj (g x)) *
        (conj (phase q x.2) * phase q x.2) := by dsimp only [phase]; ring
    _ = _ := by rw [phase_conj_mul, mul_one]

end PUT.FourierPreparation
