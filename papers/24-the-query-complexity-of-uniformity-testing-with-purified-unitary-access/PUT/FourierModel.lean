import PUT.QueryPrior
import PUT.ExternalMoments
import PUT.FiniteAdversary
import PUT.Moments
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# The actual Fourier–Dirichlet latent spaces

The phase prior below is normalized Haar measure on the finite dimensional
unit torus.  The radial prior is the continuous normalized-gamma law, and the
only analytic input is the separately disclosed standard Dirichlet moment
law.  In particular the orthonormal family and the finite-rank adversary in
this module are actual `L²` functions and continuous linear maps.
-/
noncomputable section
namespace PUT.FourierModel
open MeasureTheory
open scoped ENNReal ComplexConjugate

attribute [local instance] Real.fact_zero_lt_one
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

abbrev Coord (d M : ℕ) := Fin d × Fin M
abbrev Torus (d M : ℕ) := UnitAddTorus (Coord d M)

def phaseMeasure (d M : ℕ) : Measure (Torus d M) := volume

instance (d M : ℕ) : IsProbabilityMeasure (phaseMeasure d M) := by
  unfold phaseMeasure
  infer_instance

def alternativeMeasure (d M : ℕ) (a : ℝ) : Measure ((Fin d → ℝ) × Torus d M) :=
  (dirichletMeasure d a).prod (phaseMeasure d M)

theorem alternative_probability (d M : ℕ) {a : ℝ} (ha : 0 < a) :
    IsProbabilityMeasure (alternativeMeasure d M a) := by
  letI := isProbabilityMeasure_dirichletMeasure d ha
  unfold alternativeMeasure
  infer_instance

abbrev NullL2 (d M : ℕ) := Lp ℂ 2 (phaseMeasure d M)
abbrev AltL2 (d M : ℕ) (a : ℝ) := Lp ℂ 2 (alternativeMeasure d M a)
abbrev RadialL2 (d : ℕ) (a : ℝ) := Lp ℂ 2 (dirichletMeasure d a)

def flatten {d M : ℕ} (n : PhaseIndex d M) : Coord d M → ℤ := fun ij => n ij.1 ij.2

theorem flatten_injective {d M : ℕ} : Function.Injective (@flatten d M) := by
  intro n m h
  funext i j
  exact congrFun h (i,j)

def character {d M : ℕ} (n : PhaseIndex d M) : C(Torus d M, ℂ) :=
  UnitAddTorus.mFourier (flatten n)

def e {d M : ℕ} (n : PhaseIndex d M) : NullL2 d M :=
  UnitAddTorus.mFourierLp 2 (flatten n)

theorem e_ae {d M : ℕ} (n : PhaseIndex d M) :
    e n =ᵐ[phaseMeasure d M] character n :=
  UnitAddTorus.coeFn_mFourierLp 2 (flatten n)

theorem e_orthonormal (d M : ℕ) : Orthonormal ℂ (@e d M) :=
  UnitAddTorus.orthonormal_mFourier.comp flatten flatten_injective

@[simp] theorem character_zero {d M : ℕ} (θ : Torus d M) :
    character (zeroPhase (d := d) (M := M)) θ = 1 := by
  change UnitAddTorus.mFourier (0 : Coord d M → ℤ) θ = 1
  rw [UnitAddTorus.mFourier_zero]
  rfl

/-- A coordinate Fourier shift; it remains invertible for negative indices. -/
def shift {d M : ℕ} (n : PhaseIndex d M) (i : Fin d) (j : Fin M) : PhaseIndex d M :=
  Function.update n i (Function.update (n i) j (n i j + 1))

@[simp] theorem shift_same {d M : ℕ} (n : PhaseIndex d M) (i : Fin d) (j : Fin M) :
    shift n i j i j = n i j + 1 := by simp [shift]

theorem shift_injective {d M : ℕ} (i : Fin d) (j : Fin M) :
    Function.Injective (fun n : PhaseIndex d M => shift n i j) := by
  intro n m h
  funext l t
  by_cases hl : l = i
  · subst l
    by_cases ht : t = j
    · subst t
      have hh := congrFun (congrFun h i) j
      simp only [shift_same] at hh
      omega
    · have hh := congrFun (congrFun h i) t
      simpa [shift, ht] using hh
  · have hh := congrFun (congrFun h l) t
    simpa [shift, hl] using hh

/-- Output coordinate, output Fourier index determine a unique input sector.
This is the column orthogonality / disjoint row block argument of Section 3. -/
theorem sector_coordinate_injective {d M : ℕ} :
    Function.Injective (fun x : PhaseIndex d M × Coord d M =>
      (x.2, shift x.1 x.2.1 x.2.2)) := by
  rintro ⟨n, i, j⟩ ⟨m, l, t⟩ h
  have hij : (i,j) = (l,t) := congrArg Prod.fst h
  cases hij
  have hnm := shift_injective i j (congrArg Prod.snd h)
  cases hnm
  rfl

theorem flatten_shift {d M : ℕ} (n : PhaseIndex d M) (i : Fin d) (j : Fin M) :
    flatten (shift n i j) = flatten n + Pi.single (i,j) 1 := by
  funext ⟨l,t⟩
  by_cases hl : l = i <;> by_cases ht : t = j <;>
    simp [flatten, shift, hl, ht, Pi.single_apply]

theorem character_shift {d M : ℕ} (n : PhaseIndex d M)
    (i : Fin d) (j : Fin M) (θ : Torus d M) :
    character (shift n i j) θ = character n θ * fourier 1 (θ (i,j)) := by
  unfold character
  rw [flatten_shift, UnitAddTorus.mFourier_add,
    UnitAddTorus.mFourier_single]

theorem degree_shift_creation {d M : ℕ} (n : PhaseIndex d M)
    (i : Fin d) (j : Fin M) (hn : 0 ≤ n i j) :
    degreeOf (shift n i j) = degUp (degreeOf n) i := by
  funext l
  by_cases hl : l = i
  · subst l
    unfold degreeOf labelDegree
    simp only [shift, Function.update_self, degUp, Function.update_self]
    have heq : (fun t => (Function.update (n i) j (n i j + 1) t).natAbs) =
        Function.update (fun t => (n i t).natAbs) j (n i j + 1).natAbs := by
      funext t
      by_cases ht : t = j
      · subst t; simp only [Function.update_self]
      · simp only [Function.update_of_ne ht]
    rw [heq, Finset.sum_update_of_mem (Finset.mem_univ j)]
    have hsum := Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ j)
      (fun t : Fin M => (n i t).natAbs)
    have h := Int.natAbs_of_nonneg hn
    have h' := Int.natAbs_of_nonneg (show 0 ≤ n i j + 1 by omega)
    omega
  · simp [degreeOf, labelDegree, shift, degUp, hl]

theorem degree_shift_erasure {d M : ℕ} (n : PhaseIndex d M)
    (i : Fin d) (j : Fin M) (hn : n i j < 0) :
    degreeOf (shift n i j) = degDown (degreeOf n) i := by
  funext l
  by_cases hl : l = i
  · subst l
    unfold degreeOf labelDegree
    simp only [shift, Function.update_self, degDown, Function.update_self]
    have heq : (fun t => (Function.update (n i) j (n i j + 1) t).natAbs) =
        Function.update (fun t => (n i t).natAbs) j (n i j + 1).natAbs := by
      funext t
      by_cases ht : t = j
      · subst t; simp only [Function.update_self]
      · simp only [Function.update_of_ne ht]
    rw [heq, Finset.sum_update_of_mem (Finset.mem_univ j)]
    have hh : (n i j + 1).natAbs + 1 = (n i j).natAbs := by omega
    have hsum := Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ j)
      (fun t : Fin M => (n i t).natAbs)
    omega
  · simp [degreeOf, labelDegree, shift, degDown, hl]

/-! ## Normalized radial vectors from the actual moment integral -/

theorem weight_measurable {d : ℕ} (a : ℝ) (k : Fin d → ℕ) :
    Measurable (weight a k) := by
  unfold weight
  fun_prop

theorem coordinate_le_one {d : ℕ} {p : Fin d → ℝ}
    (hp : p ∈ positiveSimplex d) (i : Fin d) : p i ≤ 1 := by
  rw [← hp.2]
  exact Finset.single_le_sum (fun j _ => (hp.1 j).le) (Finset.mem_univ i)

theorem weight_nonneg {d : ℕ} {a : ℝ} (k : Fin d → ℕ)
    {p : Fin d → ℝ} (hp : p ∈ positiveSimplex d) : 0 ≤ weight a k p := by
  unfold weight
  exact div_nonneg (Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (hp.1 i).le _))
    (Real.sqrt_nonneg _)

theorem weight_le {d : ℕ} (a : ℝ) (k : Fin d → ℕ)
    {p : Fin d → ℝ} (hp : p ∈ positiveSimplex d) :
    weight a k p ≤ 1 / Real.sqrt (dirMoment a k) := by
  unfold weight
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply Finset.prod_le_one
  · intro i _
    exact Real.rpow_nonneg (hp.1 i).le _
  · intro i _
    exact Real.rpow_le_one (hp.1 i).le (coordinate_le_one hp i) (by positivity)

theorem weight_sq {d : ℕ} {a : ℝ} (ha : 0 < a) (k : Fin d → ℕ)
    {p : Fin d → ℝ} (hp : p ∈ positiveSimplex d) :
    weight a k p ^ 2 = (∏ i, p i ^ k i) / dirMoment a k := by
  unfold weight
  rw [div_pow, Real.sq_sqrt (dirMoment_pos a k ha).le, ← Finset.prod_pow]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [← Real.rpow_mul_natCast (hp.1 i).le]
  convert Real.rpow_natCast (p i) (k i) using 1 <;> congr 1 <;> ring

theorem radial_memLp {d : ℕ} {a : ℝ} (hd : 0 < d) (ha : 0 < a) (k : Fin d → ℕ) :
    MemLp (fun p => (weight a k p : ℂ)) 2 (dirichletMeasure d a) := by
  letI := isProbabilityMeasure_dirichletMeasure d ha
  apply MemLp.of_bound (Complex.measurable_ofReal.comp (weight_measurable a k)).aestronglyMeasurable
    (1 / Real.sqrt (dirMoment a k))
  filter_upwards [dirichletMeasure_ae_positiveSimplex hd ha] with p hp
  change ‖(weight a k p : ℂ)‖ ≤ _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (weight_nonneg k hp)]
  exact weight_le a k hp

def radial {d : ℕ} {a : ℝ} (hd : 0 < d) (ha : 0 < a) (k : Fin d → ℕ) : RadialL2 d a :=
  (radial_memLp hd ha k).toLp (fun p => (weight a k p : ℂ))

theorem radial_ae {d : ℕ} {a : ℝ} (hd : 0 < d) (ha : 0 < a) (k : Fin d → ℕ) :
    radial hd ha k =ᵐ[dirichletMeasure d a] fun p => (weight a k p : ℂ) :=
  (radial_memLp hd ha k).coeFn_toLp

theorem integral_weight_sq (moments : External.DirichletJointMomentLaw)
    {d : ℕ} {a : ℝ} (hd : 2 ≤ d) (ha : 0 < a) (k : Fin d → ℕ) :
    (∫ p, weight a k p ^ 2 ∂dirichletMeasure d a) = 1 := by
  calc
    _ = ∫ p, (∏ i, p i ^ k i) / dirMoment a k ∂dirichletMeasure d a := by
      apply integral_congr_ae
      filter_upwards [dirichletMeasure_ae_positiveSimplex (by omega) ha] with p hp
      exact weight_sq ha k hp
    _ = (∫ p, ∏ i, p i ^ k i ∂dirichletMeasure d a) / dirMoment a k :=
      integral_div _ _
    _ = 1 := by rw [(moments d a k hd ha).2, div_self (dirMoment_ne_zero a k ha)]

theorem radial_norm (moments : External.DirichletJointMomentLaw)
    {d : ℕ} {a : ℝ} (hd : 2 ≤ d) (ha : 0 < a) (k : Fin d → ℕ) :
    ‖radial (by omega : 0 < d) ha k‖ = 1 := by
  have hs : ‖radial (by omega : 0 < d) ha k‖ ^ 2 = 1 := by
    rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def]
    have hi : (∫ p, inner ℂ (radial (by omega : 0 < d) ha k p)
        (radial (by omega : 0 < d) ha k p) ∂dirichletMeasure d a) =
        (∫ p, weight a k p ^ 2 ∂dirichletMeasure d a : ℝ) := by
      rw [← integral_complex_ofReal]
      apply integral_congr_ae
      filter_upwards [radial_ae (by omega : 0 < d) ha k] with p hp
      rw [hp]
      simp [RCLike.inner_apply, pow_two]
    rw [hi, integral_weight_sq moments hd ha]
    rfl
  nlinarith [norm_nonneg (radial (by omega : 0 < d) ha k)]


/-! ## The actual product-prior Fourier family -/

theorem character_norm {d M : ℕ} (n : PhaseIndex d M) (θ : Torus d M) :
    ‖character n θ‖ = 1 := by
  simp [character, UnitAddTorus.mFourier, fourier_apply, norm_prod, Circle.norm_coe]

def fFunction {d M : ℕ} (a : ℝ) (n : PhaseIndex d M)
    (x : (Fin d → ℝ) × Torus d M) : ℂ :=
  (weight a (degreeOf n) x.1 : ℂ) * character n x.2

theorem fFunction_measurable {d M : ℕ} (a : ℝ) (n : PhaseIndex d M) :
    Measurable (fFunction a n) := by
  apply Measurable.mul
  · exact (Complex.measurable_ofReal.comp (weight_measurable a (degreeOf n))).comp measurable_fst
  · exact (character n).continuous.measurable.comp measurable_snd

theorem alternative_ae_simplex {d M : ℕ} {a : ℝ} (hd : 0 < d) (ha : 0 < a) :
    ∀ᵐ x ∂alternativeMeasure d M a, x.1 ∈ positiveSimplex d :=
  Measure.quasiMeasurePreserving_fst.ae (dirichletMeasure_ae_positiveSimplex hd ha)

theorem f_memLp {d M : ℕ} {a : ℝ} (hd : 0 < d) (ha : 0 < a) (n : PhaseIndex d M) :
    MemLp (fFunction a n) 2 (alternativeMeasure d M a) := by
  letI := alternative_probability d M ha
  apply MemLp.of_bound (fFunction_measurable a n).aestronglyMeasurable
    (1 / Real.sqrt (dirMoment a (degreeOf n)))
  filter_upwards [alternative_ae_simplex (M := M) hd ha] with x hx
  rw [fFunction, norm_mul, character_norm, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (weight_nonneg (degreeOf n) hx)]
  exact weight_le a (degreeOf n) hx

def f {d M : ℕ} {a : ℝ} (hd : 0 < d) (ha : 0 < a) (n : PhaseIndex d M) : AltL2 d M a :=
  (f_memLp hd ha n).toLp (fFunction a n)

theorem f_ae {d M : ℕ} {a : ℝ} (hd : 0 < d) (ha : 0 < a) (n : PhaseIndex d M) :
    f hd ha n =ᵐ[alternativeMeasure d M a] fFunction a n :=
  (f_memLp hd ha n).coeFn_toLp

theorem integral_character_inner {d M : ℕ} (n m : PhaseIndex d M) :
    (∫ θ, conj (character n θ) * character m θ ∂phaseMeasure d M) =
      if n = m then 1 else 0 := by
  have hh := orthonormal_iff_ite.mp (e_orthonormal d M) n m
  rw [L2.inner_def] at hh
  convert hh using 1
  apply integral_congr_ae
  filter_upwards [e_ae n, e_ae m] with θ hn hm
  simp [hn, hm, RCLike.inner_apply, mul_comm]

theorem f_inner {d M : ℕ} {a : ℝ} (hd : 0 < d) (ha : 0 < a)
    (n m : PhaseIndex d M) :
    inner ℂ (f hd ha n) (f hd ha m) =
      (∫ p, (weight a (degreeOf n) p : ℂ) * weight a (degreeOf m) p
        ∂dirichletMeasure d a) * (if n = m then 1 else 0) := by
  letI := isProbabilityMeasure_dirichletMeasure d ha
  rw [L2.inner_def]
  calc
    _ = ∫ x : (Fin d → ℝ) × Torus d M,
        ((weight a (degreeOf n) x.1 : ℂ) * weight a (degreeOf m) x.1) *
          (conj (character n x.2) * character m x.2) ∂alternativeMeasure d M a := by
      apply integral_congr_ae
      filter_upwards [f_ae hd ha n, f_ae hd ha m] with x hn hm
      simp only [hn, hm, fFunction, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
      ring
    _ = _ := by
      change (∫ x : (Fin d → ℝ) × Torus d M,
        (fun p : Fin d → ℝ => (weight a (degreeOf n) p : ℂ) * weight a (degreeOf m) p) x.1 *
        (fun θ : Torus d M => conj (character n θ) * character m θ) x.2
        ∂(dirichletMeasure d a).prod (phaseMeasure d M)) = _
      calc
        _ = (∫ p, (weight a (degreeOf n) p : ℂ) * weight a (degreeOf m) p
            ∂dirichletMeasure d a) *
          (∫ θ, conj (character n θ) * character m θ ∂phaseMeasure d M) :=
          integral_prod_mul (μ := dirichletMeasure d a) (ν := phaseMeasure d M)
            (fun p : Fin d → ℝ => (weight a (degreeOf n) p : ℂ) * weight a (degreeOf m) p)
            (fun θ : Torus d M => conj (character n θ) * character m θ)
        _ = _ := by rw [integral_character_inner]

theorem f_orthonormal (moments : External.DirichletJointMomentLaw)
    {d M : ℕ} {a : ℝ} (hd : 2 ≤ d) (ha : 0 < a) :
    Orthonormal ℂ (f (M := M) (by omega : 0 < d) ha) := by
  rw [orthonormal_iff_ite]
  intro n m
  rw [f_inner]
  split_ifs with h
  · subst m
    rw [mul_one]
    have heq : (fun p : Fin d → ℝ =>
        (weight a (degreeOf n) p : ℂ) * weight a (degreeOf n) p) =
        fun p => ((weight a (degreeOf n) p ^ 2 : ℝ) : ℂ) := by
      funext p
      simp [pow_two]
    rw [heq, integral_complex_ofReal, integral_weight_sq moments hd ha]
    rfl
  · exact mul_zero _

/-- Equation (7) is instantiated on the paper's two genuine continuous-prior
latent Hilbert spaces, with finite support proved in `FiniteAdversary`. -/
def gamma {d M : ℕ} {a : ℝ} (hd : 0 < d) (ha : 0 < a) (A : ℝ) :
    AltL2 d M a →L[ℂ] NullL2 d M :=
  FiniteAdversary.gamma A e (f hd ha)

theorem gamma_norm (moments : External.DirichletJointMomentLaw)
    {d M : ℕ} {a A : ℝ} (hd : 2 ≤ d) (ha : 0 < a) (hA : 0 < A) :
    ‖gamma (M := M) (by omega : 0 < d) ha A‖ = A :=
  FiniteAdversary.gamma_norm A hA e (f (by omega : 0 < d) ha)
    (e_orthonormal d M) (f_orthonormal moments hd ha)

theorem gamma_on_zero (moments : External.DirichletJointMomentLaw)
    {d M : ℕ} {a A : ℝ} (hd : 2 ≤ d) (ha : 0 < a) (hA : 0 < A) :
    gamma (M := M) (by omega : 0 < d) ha A (f (by omega : 0 < d) ha zeroPhase) =
      (A : ℂ) • e zeroPhase :=
  FiniteAdversary.gamma_on_zero A hA e (f (by omega : 0 < d) ha)
    (f_orthonormal moments hd ha)


/-! ## Every radial direction in each Fourier sector

`sector n` is an isometry of the entire radial Hilbert space, rather than
just its selected moment vector.  Its range can therefore contain all
radial complements used in the full-operator estimate.
-/

def sectorFunction {d M : ℕ} {a : ℝ} (n : PhaseIndex d M) (h : RadialL2 d a)
    (x : (Fin d → ℝ) × Torus d M) : ℂ := h x.1 * character n x.2

theorem sectorFunction_memLp {d M : ℕ} {a : ℝ} (n : PhaseIndex d M) (h : RadialL2 d a) :
    MemLp (sectorFunction n h) 2 (alternativeMeasure d M a) := by
  have hfst := (Lp.memLp h).comp_measurePreserving
    (measurePreserving_fst (μ := dirichletMeasure d a) (ν := phaseMeasure d M))
  apply hfst.congr_norm
  · exact hfst.aestronglyMeasurable.mul
      ((character n).continuous.measurable.comp measurable_snd).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun x => by
      simp [sectorFunction, norm_mul, character_norm])

def sectorFun {d M : ℕ} {a : ℝ} (n : PhaseIndex d M) (h : RadialL2 d a) : AltL2 d M a :=
  (sectorFunction_memLp n h).toLp (sectorFunction n h)

theorem sectorFun_ae {d M : ℕ} {a : ℝ} (n : PhaseIndex d M) (h : RadialL2 d a) :
    sectorFun n h =ᵐ[alternativeMeasure d M a] sectorFunction n h :=
  (sectorFunction_memLp n h).coeFn_toLp

theorem sectorFun_add {d M : ℕ} {a : ℝ} (n : PhaseIndex d M) (h g : RadialL2 d a) :
    sectorFun n (h + g) = sectorFun n h + sectorFun n g := by
  apply Lp.ext
  have had := (Measure.quasiMeasurePreserving_fst (μ := dirichletMeasure d a) (ν := phaseMeasure d M)).ae_eq (Lp.coeFn_add h g)
  filter_upwards [sectorFun_ae n (h+g), sectorFun_ae n h, sectorFun_ae n g,
    Lp.coeFn_add (sectorFun n h) (sectorFun n g), had] with x hfg hf hg ho hi
  change (h+g) x.1 = h x.1 + g x.1 at hi
  simp only [hfg, ho, sectorFunction, hi, Pi.add_apply, hf, hg]
  ring

theorem sectorFun_smul {d M : ℕ} {a : ℝ} (n : PhaseIndex d M) (c : ℂ) (h : RadialL2 d a) :
    sectorFun n (c • h) = c • sectorFun n h := by
  apply Lp.ext
  have had := (Measure.quasiMeasurePreserving_fst (μ := dirichletMeasure d a) (ν := phaseMeasure d M)).ae_eq (Lp.coeFn_smul c h)
  filter_upwards [sectorFun_ae n (c • h), sectorFun_ae n h,
    Lp.coeFn_smul c (sectorFun n h), had] with x hc hf ho hi
  change (c • h) x.1 = c • h x.1 at hi
  simp only [hc, ho, sectorFunction, hi, Pi.smul_apply, smul_eq_mul, hf]
  ring

theorem sectorFun_norm {d M : ℕ} {a : ℝ} (ha : 0 < a)
    (n : PhaseIndex d M) (h : RadialL2 d a) : ‖sectorFun n h‖ = ‖h‖ := by
  letI := isProbabilityMeasure_dirichletMeasure d ha
  have hs : ‖sectorFun n h‖ ^ 2 = ‖h‖ ^ 2 := by
    rw [QueryModel.prior_norm_sq, QueryModel.prior_norm_sq]
    calc
      _ = ∫ x : (Fin d → ℝ) × Torus d M, ‖h x.1‖ ^ 2 * (1 : ℝ)
          ∂alternativeMeasure d M a := by
        apply integral_congr_ae
        filter_upwards [sectorFun_ae n h] with x hx
        simp [hx, sectorFunction, norm_mul, character_norm]
      _ = (∫ p, ‖h p‖ ^ 2 ∂dirichletMeasure d a) *
          (∫ _ : Torus d M, (1 : ℝ) ∂phaseMeasure d M) :=
        integral_prod_mul (μ := dirichletMeasure d a) (ν := phaseMeasure d M)
          (fun p => ‖h p‖ ^ 2) (fun _ => (1 : ℝ))
      _ = _ := by simp
  nlinarith [norm_nonneg (sectorFun n h), norm_nonneg h]

def sector {d M : ℕ} {a : ℝ} (ha : 0 < a) (n : PhaseIndex d M) :
    RadialL2 d a →ₗᵢ[ℂ] AltL2 d M a where
  toFun := sectorFun n
  map_add' := sectorFun_add n
  map_smul' := sectorFun_smul n
  norm_map' := sectorFun_norm ha n

theorem sector_inner {d M : ℕ} {a : ℝ} (ha : 0 < a) (n m : PhaseIndex d M)
    (h g : RadialL2 d a) :
    inner ℂ (sector ha n h) (sector ha m g) =
      inner ℂ h g * (if n = m then 1 else 0) := by
  letI := isProbabilityMeasure_dirichletMeasure d ha
  rw [L2.inner_def h g]
  change inner ℂ (sectorFun n h) (sectorFun m g) = _
  rw [L2.inner_def]
  calc
    _ = ∫ x : (Fin d → ℝ) × Torus d M, (inner ℂ (h x.1) (g x.1)) *
        (conj (character n x.2) * character m x.2) ∂alternativeMeasure d M a := by
      apply integral_congr_ae
      filter_upwards [sectorFun_ae n h, sectorFun_ae m g] with x hn hm
      simp only [hn, hm, sectorFunction, RCLike.inner_apply, map_mul]
      ring
    _ = (∫ p, inner ℂ (h p) (g p) ∂dirichletMeasure d a) *
        (∫ θ, conj (character n θ) * character m θ ∂phaseMeasure d M) :=
      integral_prod_mul (μ := dirichletMeasure d a) (ν := phaseMeasure d M)
        (fun p => inner ℂ (h p) (g p))
        (fun θ => conj (character n θ) * character m θ)
    _ = _ := by rw [integral_character_inner]

theorem sector_orthogonal {d M : ℕ} {a : ℝ} (ha : 0 < a)
    {n m : PhaseIndex d M} (hnm : n ≠ m) (h g : RadialL2 d a) :
    inner ℂ (sector ha n h) (sector ha m g) = 0 := by
  rw [sector_inner, if_neg hnm, mul_zero]

theorem f_eq_sector_radial {d M : ℕ} {a : ℝ} (hd : 0 < d) (ha : 0 < a)
    (n : PhaseIndex d M) : f hd ha n = sector ha n (radial hd ha (degreeOf n)) := by
  apply Lp.ext
  have hr := (Measure.quasiMeasurePreserving_fst (μ := dirichletMeasure d a) (ν := phaseMeasure d M)).ae_eq (radial_ae hd ha (degreeOf n))
  filter_upwards [f_ae hd ha n, sectorFun_ae n (radial hd ha (degreeOf n)), hr]
    with x hf hs hr
  change (radial hd ha (degreeOf n)) x.1 = (weight a (degreeOf n) x.1 : ℂ) at hr
  change (f hd ha n) x = (sectorFun n (radial hd ha (degreeOf n))) x
  rw [hf, hs, sectorFunction, fFunction, hr]


/-! ## Actual bounded radial coordinate multiplication -/

def sqrtProduct {d : ℕ} {a : ℝ} (i : Fin d) (h : RadialL2 d a) (p : Fin d → ℝ) : ℂ :=
  (Real.sqrt (p i) : ℂ) * h p

theorem sqrtProduct_norm_le {d : ℕ} {a : ℝ} (i : Fin d) (h : RadialL2 d a)
    {p : Fin d → ℝ} (hp : p ∈ positiveSimplex d) : ‖sqrtProduct i h p‖ ≤ ‖h p‖ := by
  have hs : Real.sqrt (p i) ≤ 1 := by
    exact (Real.sqrt_le_one).mpr (coordinate_le_one hp i)
  simp only [sqrtProduct, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_of_le_one_left (norm_nonneg _) hs

theorem sqrtProduct_memLp {d : ℕ} {a : ℝ} (hd : 0 < d) (ha : 0 < a)
    (i : Fin d) (h : RadialL2 d a) : MemLp (sqrtProduct i h) 2 (dirichletMeasure d a) := by
  apply (Lp.memLp h).mono
  · exact (Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp
      (measurable_pi_apply i))).aestronglyMeasurable.mul (Lp.aestronglyMeasurable h)
  · filter_upwards [dirichletMeasure_ae_positiveSimplex hd ha] with p hp
    exact sqrtProduct_norm_le i h hp

def sqrtMultiplyFun {d : ℕ} {a : ℝ} (hd : 0 < d) (ha : 0 < a)
    (i : Fin d) (h : RadialL2 d a) : RadialL2 d a :=
  (sqrtProduct_memLp hd ha i h).toLp (sqrtProduct i h)

theorem sqrtMultiplyFun_ae {d : ℕ} {a : ℝ} (hd : 0 < d) (ha : 0 < a)
    (i : Fin d) (h : RadialL2 d a) :
    sqrtMultiplyFun hd ha i h =ᵐ[dirichletMeasure d a] sqrtProduct i h :=
  (sqrtProduct_memLp hd ha i h).coeFn_toLp

def sqrtMultiply {d : ℕ} {a : ℝ} (hd : 0 < d) (ha : 0 < a) (i : Fin d) :
    RadialL2 d a →L[ℂ] RadialL2 d a :=
  LinearMap.mkContinuous
    { toFun := sqrtMultiplyFun hd ha i
      map_add' := by
        intro h g
        apply Lp.ext
        filter_upwards [sqrtMultiplyFun_ae hd ha i (h+g), sqrtMultiplyFun_ae hd ha i h,
          sqrtMultiplyFun_ae hd ha i g, Lp.coeFn_add h g,
          Lp.coeFn_add (sqrtMultiplyFun hd ha i h) (sqrtMultiplyFun hd ha i g)]
          with p hsum hh hg hi ho
        simp only [hsum, ho, sqrtProduct, hi, Pi.add_apply, hh, hg]
        ring
      map_smul' := by
        intro c h
        change sqrtMultiplyFun hd ha i (c • h) = c • sqrtMultiplyFun hd ha i h
        apply Lp.ext
        filter_upwards [sqrtMultiplyFun_ae hd ha i (c • h), sqrtMultiplyFun_ae hd ha i h,
          Lp.coeFn_smul c h, Lp.coeFn_smul c (sqrtMultiplyFun hd ha i h)]
          with p hsum hh hi ho
        simp only [hsum, ho, sqrtProduct, hi, Pi.smul_apply, smul_eq_mul, hh]
        ring }
    1 (by
      intro h
      simp only [one_mul]
      change ‖sqrtMultiplyFun hd ha i h‖ ≤ ‖h‖
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [sqrtMultiplyFun_ae hd ha i h,
        dirichletMeasure_ae_positiveSimplex hd ha] with p hm hp
      rw [hm]
      exact sqrtProduct_norm_le i h hp)

theorem sqrtMultiply_ae {d : ℕ} {a : ℝ} (hd : 0 < d) (ha : 0 < a)
    (i : Fin d) (h : RadialL2 d a) :
    sqrtMultiply hd ha i h =ᵐ[dirichletMeasure d a]
      fun p => (Real.sqrt (p i) : ℂ) * h p := sqrtMultiplyFun_ae hd ha i h

theorem sqrtMultiply_norm_le {d : ℕ} {a : ℝ} (hd : 0 < d) (ha : 0 < a) (i : Fin d) :
    ‖sqrtMultiply hd ha i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro h
  simp only [one_mul]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [sqrtMultiply_ae hd ha i h, dirichletMeasure_ae_positiveSimplex hd ha]
    with p hm hp
  rw [hm]
  exact sqrtProduct_norm_le i h hp

theorem sqrtMultiply_inner {d : ℕ} {a : ℝ} (hd : 0 < d) (ha : 0 < a)
    (i : Fin d) (h g : RadialL2 d a) :
    inner ℂ (sqrtMultiply hd ha i h) g = inner ℂ h (sqrtMultiply hd ha i g) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [sqrtMultiply_ae hd ha i h, sqrtMultiply_ae hd ha i g] with p hh hg
  simp only [hh, hg, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

theorem sqrtMultiply_adjoint {d : ℕ} {a : ℝ} (hd : 0 < d) (ha : 0 < a) (i : Fin d) :
    (sqrtMultiply hd ha i).adjoint = sqrtMultiply hd ha i := by
  apply ContinuousLinearMap.ext
  intro h
  apply ext_inner_left ℂ
  intro g
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact sqrtMultiply_inner hd ha i g h

/-- Equation (10) as equality of actual radial `L²` vectors. -/
theorem sqrtMultiply_radial_creation {d : ℕ} {a : ℝ}
    (hd : 0 < d) (ha : 0 < a) (k : Fin d → ℕ) (i : Fin d) :
    sqrtMultiply hd ha i (radial hd ha k) =
      (createCoeff a k i : ℂ) • radial hd ha (degUp k i) := by
  apply Lp.ext
  filter_upwards [sqrtMultiply_ae hd ha i (radial hd ha k), radial_ae hd ha k,
    radial_ae hd ha (degUp k i),
    Lp.coeFn_smul (createCoeff a k i : ℂ) (radial hd ha (degUp k i)),
    dirichletMeasure_ae_positiveSimplex hd ha] with p hm hk hu hsm hp
  rw [hm, hk, hsm, Pi.smul_apply, hu, smul_eq_mul]
  exact_mod_cast create_weight_id a k i p hp.1 ha

/-- Equation (11) as equality of actual radial `L²` vectors. -/
theorem sqrtMultiply_radial_erasure {d : ℕ} {a : ℝ}
    (hd : 0 < d) (ha : 0 < a) (k : Fin d → ℕ) (i : Fin d) (hki : 0 < k i) :
    sqrtMultiply hd ha i (radial hd ha (degDown k i)) =
      (eraseCoeff a k i : ℂ) • radial hd ha k := by
  apply Lp.ext
  filter_upwards [sqrtMultiply_ae hd ha i (radial hd ha (degDown k i)),
    radial_ae hd ha (degDown k i), radial_ae hd ha k,
    Lp.coeFn_smul (eraseCoeff a k i : ℂ) (radial hd ha k),
    dirichletMeasure_ae_positiveSimplex hd ha] with p hm hk hu hsm hp
  rw [hm, hk, hsm, Pi.smul_apply, hu, smul_eq_mul]
  exact_mod_cast erase_weight_id a k i p hp.1 ha hki


/-! ## Constant state and exact finite-adversary sector action -/

theorem weight_zero {d : ℕ} (a : ℝ) (p : Fin d → ℝ) :
    weight a (fun _ : Fin d => 0) p = 1 := by
  simp [weight, dirMoment, degK]

theorem e_zero_eq_const (d M : ℕ) :
    e (zeroPhase (d := d) (M := M)) = Lp.const 2 (phaseMeasure d M) (1 : ℂ) := by
  apply Lp.ext
  filter_upwards [e_ae (zeroPhase (d := d) (M := M)),
    Lp.coeFn_const 2 (phaseMeasure d M) (1 : ℂ)] with θ he hc
  rw [he, hc, character_zero]
  rfl

theorem f_zero_eq_const {d M : ℕ} {a : ℝ} [IsFiniteMeasure (alternativeMeasure d M a)]
    (hd : 0 < d) (ha : 0 < a) :
    f (M := M) hd ha zeroPhase = Lp.const 2 (alternativeMeasure d M a) (1 : ℂ) := by
  letI := alternative_probability d M ha
  apply Lp.ext
  filter_upwards [f_ae hd ha (zeroPhase (d := d) (M := M)),
    Lp.coeFn_const 2 (alternativeMeasure d M a) (1 : ℂ)] with x hf hc
  rw [hf, hc, fFunction, degreeOf_zero, weight_zero, character_zero]
  simp

theorem gamma_constant (moments : External.DirichletJointMomentLaw)
    {d M : ℕ} {a A : ℝ} [IsFiniteMeasure (alternativeMeasure d M a)]
    (hd : 2 ≤ d) (ha : 0 < a) (hA : 0 < A) :
    gamma (M := M) (by omega : 0 < d) ha A
      (Lp.const 2 (alternativeMeasure d M a) (1 : ℂ)) =
        (A : ℂ) • Lp.const 2 (phaseMeasure d M) (1 : ℂ) := by
  rw [← f_zero_eq_const (by omega : 0 < d) ha,
    gamma_on_zero moments hd ha hA, e_zero_eq_const]

theorem sector_adjoint_sector {d M : ℕ} {a : ℝ} (ha : 0 < a)
    (n m : PhaseIndex d M) (h : RadialL2 d a) :
    (sector ha n).toContinuousLinearMap.adjoint (sector ha m h) =
      if n = m then h else 0 := by
  apply ext_inner_left ℂ
  intro g
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (sector ha n g) (sector ha m h) = _
  rw [sector_inner]
  by_cases hnm : n = m <;> simp [hnm]

/-- Exact action on an arbitrary vector in an entire radial Fourier sector.
This also proves that unselected radial directions are erased by Γ. -/
theorem gamma_sector {d M : ℕ} {a : ℝ} (hd : 0 < d) (ha : 0 < a)
    (A : ℝ) (n : PhaseIndex d M) (h : RadialL2 d a) :
    gamma hd ha A (sector ha n h) =
      ((gammaWeight A n : ℂ) * inner ℂ (radial hd ha (degreeOf n)) h) • e n := by
  classical
  unfold gamma FiniteAdversary.gamma
  rw [FiniteAdversary.operator_apply]
  simp_rw [f_eq_sector_radial, sector_inner]
  by_cases hn : n ∈ (FiniteAdversary.support_finite d M A).toFinset
  · simpa only [mul_ite, mul_one, mul_zero, ite_smul, zero_smul] using
      (Finset.sum_eq_single n
        (fun m hm hmn => by simp [hmn])
        (fun hn' => (hn' hn).elim) :
        (∑ m ∈ (FiniteAdversary.support_finite d M A).toFinset,
          ((gammaWeight A m : ℂ) *
            (inner ℂ (radial hd ha (degreeOf m)) h * if m = n then 1 else 0)) • e m) = _)
  · have hz : gammaWeight A n = 0 := by
      simpa only [Set.Finite.mem_toFinset, FiniteAdversary.support, Set.mem_setOf_eq,
        not_not] using hn
    rw [hz, Complex.ofReal_zero, zero_mul, zero_smul]
    apply Finset.sum_eq_zero
    intro m hm
    have hmn : m ≠ n := by intro hmn; subst m; exact hn hm
    simp [hmn]

end PUT.FourierModel
