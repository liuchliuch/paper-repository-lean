import Paper08.ZeroFree
import Paper08.MomentSeries
import Paper08.Support
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Nat.Choose.Multinomial

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace Paper08.MultiMoments
open Integral

/-- One uniform coordinate on the unit interval. -/
def intervalMeasure : Measure ℝ := volume.restrict (Set.Icc 0 1)

instance : IsProbabilityMeasure intervalMeasure := by
  constructor
  simp [intervalMeasure, Real.volume_Icc]

/-- Product of the actual uniform coordinate measures. -/
def unitMeasure (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi fun _ => intervalMeasure

instance (ι : Type*) [Fintype ι] : IsProbabilityMeasure (unitMeasure ι) := by
  unfold unitMeasure
  infer_instance

lemma unitMeasure_fin (n : ℕ) : unitMeasure (Fin n) = volume.restrict (cube n) := by
  rw [volume_pi, cube, Measure.restrict_pi_pi]
  rfl

/-- Extend a tuple on one coordinate block by zero on the other block. -/
def extend {ι : Type*} [DecidableEq ι] (S : Finset ι) (x : S → ℝ) : ι → ℝ :=
  fun i => if h : i ∈ S then x ⟨i, h⟩ else 0

/-- Functions depending on disjoint coordinate blocks factor under the actual
product Lebesgue cube measure. No independence certificate is assumed. -/
theorem cubeIntegral_mul_of_depends {n : ℕ} (S T : Finset (Fin n))
    (hST : Disjoint S T) (f g : (Fin n → ℝ) → ℝ)
    (hf : ∀ x y, (∀ i ∈ S, x i = y i) → f x = f y)
    (hg : ∀ x y, (∀ i ∈ T, x i = y i) → g x = g y) :
    cubeIntegral (fun x => f x * g x) = cubeIntegral f * cubeIntegral g := by
  classical
  letI : Fintype {i : Fin n // i ∈ S} := Subtype.fintype (fun i => i ∈ S)
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) (fun i => i ∈ S)
  let F : ({i : Fin n // i ∈ S} → ℝ) → ℝ := fun x => f (extend S x)
  let G : ({i : Fin n // i ∉ S} → ℝ) → ℝ :=
    fun x => g (fun i => if h : i ∉ S then x ⟨i, h⟩ else 0)
  have heF : ∀ x : Fin n → ℝ, F (e x).1 = f x := by
    intro x
    apply hf
    intro i hi
    simp [F, extend, e, hi]
  have heG : ∀ x : Fin n → ℝ, G (e x).2 = g x := by
    intro x
    apply hg
    intro i hi
    have hn : i ∉ S := fun hs => Finset.disjoint_left.mp hST hs hi
    simp [G, e, hn]
  have hmp := measurePreserving_piEquivPiSubtypeProd
    (fun _ : Fin n => intervalMeasure) (fun i => i ∈ S)
  have hmul := hmp.integral_comp e.measurableEmbedding (fun z => F z.1 * G z.2)
  have hleft := hmp.integral_comp e.measurableEmbedding (fun z => F z.1)
  have hright := hmp.integral_comp e.measurableEmbedding (fun z => G z.2)
  change (∫ x, F (e x).1 * G (e x).2 ∂unitMeasure (Fin n)) = _ at hmul
  change (∫ x, F (e x).1 ∂unitMeasure (Fin n)) = _ at hleft
  change (∫ x, G (e x).2 ∂unitMeasure (Fin n)) = _ at hright
  simp only [heF, heG] at hmul hleft hright
  rw [integral_prod_mul] at hmul
  have hF : (∫ z, F z.1 ∂(unitMeasure {i : Fin n // i ∈ S}).prod (unitMeasure {i : Fin n // i ∉ S})) =
      ∫ x, F x ∂unitMeasure {i : Fin n // i ∈ S} := by
    simpa using integral_prod_mul (μ := unitMeasure {i : Fin n // i ∈ S})
      (ν := unitMeasure {i : Fin n // i ∉ S}) F (fun _ => (1 : ℝ))
  have hG : (∫ z, G z.2 ∂(unitMeasure {i : Fin n // i ∈ S}).prod (unitMeasure {i : Fin n // i ∉ S})) =
      ∫ x, G x ∂unitMeasure {i : Fin n // i ∉ S} := by
    simpa using integral_prod_mul (μ := unitMeasure {i : Fin n // i ∈ S})
      (ν := unitMeasure {i : Fin n // i ∉ S}) (fun _ => (1 : ℝ)) G
  simp only [unitMeasure] at hF hG
  have hleft₁ := hleft.trans hF
  have hright₁ := hright.trans hG
  change (∫ x, f x * g x ∂unitMeasure (Fin n)) = _ at hmul
  rw [← hleft₁, ← hright₁] at hmul
  simpa only [cubeIntegral, unitMeasure_fin] using hmul

/-- Coordinate union of a set of labelled factor occurrences. -/
def factorVariables {n r m : ℕ} (E : FactorFamily n r m) (B : Finset (Fin m)) : Finset (Fin n) :=
  B.biUnion fun e => (E e).scope

/-- Actual primitive moment in ambient coordinates; zero exponents integrate out. -/
def primitive {n r m : ℕ} (E : FactorFamily n r m) (d : Fin m →₀ ℕ) : ℝ :=
  primitiveMoment n (fun e => ZeroFree.ell (E e)) d

/-- Multivariate exponential-moment series with the original integrals as coefficients. -/
def momentSeries {n r m : ℕ} (E : FactorFamily n r m) : MvPowerSeries (Fin m) ℝ :=
  fun d => primitive E d / (∏ e, ((d e).factorial : ℝ))

@[simp] theorem coeff_momentSeries {n r m : ℕ} (E : FactorFamily n r m)
    (d : Fin m →₀ ℕ) :
    MvPowerSeries.coeff d (momentSeries E) =
      primitive E d / (∏ e, ((d e).factorial : ℝ)) := rfl

@[simp] theorem constantCoeff_momentSeries {n r m : ℕ} (E : FactorFamily n r m) :
    MvPowerSeries.constantCoeff (momentSeries E) = 1 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_momentSeries]
  simp [primitive, primitiveMoment]

theorem factorVariables_mono {n r m : ℕ} (E : FactorFamily n r m)
    {B C : Finset (Fin m)} (hBC : B ⊆ C) : factorVariables E B ⊆ factorVariables E C := by
  intro v hv
  obtain ⟨e, he, hv⟩ := Finset.mem_biUnion.mp hv
  exact Finset.mem_biUnion.mpr ⟨e, hBC he, hv⟩

theorem primitive_integrand_depends {n r m : ℕ} (E : FactorFamily n r m)
    (d : Fin m →₀ ℕ) (x y : Fin n → ℝ)
    (hxy : ∀ i ∈ factorVariables E d.support, x i = y i) :
    (∏ e, ZeroFree.ell (E e) x ^ d e) = ∏ e, ZeroFree.ell (E e) y ^ d e := by
  apply Finset.prod_congr rfl
  intro e _
  by_cases he : d e = 0
  · simp [he]
  · congr 1
    apply ZeroFree.ell_dependsOn_scope
    intro v hv
    exact hxy v (Finset.mem_biUnion.mpr ⟨e, Finsupp.mem_support_iff.mpr he, hv⟩)

/-- The original primitive integrals multiply on disjoint variable blocks. -/
theorem primitive_add {n r m : ℕ} (E : FactorFamily n r m)
    (a b : Fin m →₀ ℕ)
    (hvars : Disjoint (factorVariables E a.support) (factorVariables E b.support)) :
    primitive E (a + b) = primitive E a * primitive E b := by
  unfold primitive primitiveMoment
  simp only [Finsupp.add_apply, pow_add, Finset.prod_mul_distrib]
  exact cubeIntegral_mul_of_depends _ _ hvars _ _
    (primitive_integrand_depends E a) (primitive_integrand_depends E b)

/-- The factorial denominator factors when exponent supports are disjoint. -/
theorem factorial_add {m : ℕ} (a b : Fin m →₀ ℕ) (hab : Disjoint a.support b.support) :
    (∏ e, (((a + b) e).factorial : ℝ)) =
      (∏ e, ((a e).factorial : ℝ)) * ∏ e, ((b e).factorial : ℝ) := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _
  by_cases ha : a e = 0
  · simp [ha]
  · have hb : b e = 0 := by
      by_contra hb
      exact Finset.disjoint_left.mp hab (Finsupp.mem_support_iff.mpr ha)
        (Finsupp.mem_support_iff.mpr hb)
    simp [hb]

/-- Coefficients of the actual multivariate moment series multiply for exponents
on disjoint coordinate groups. -/
theorem coeff_momentSeries_add {n r m : ℕ} (E : FactorFamily n r m)
    (a b : Fin m →₀ ℕ) (hab : Disjoint a.support b.support)
    (hvars : Disjoint (factorVariables E a.support) (factorVariables E b.support)) :
    MvPowerSeries.coeff (a + b) (momentSeries E) =
      MvPowerSeries.coeff a (momentSeries E) * MvPowerSeries.coeff b (momentSeries E) := by
  rw [coeff_momentSeries, coeff_momentSeries, coeff_momentSeries,
    primitive_add E a b hvars, factorial_add a b hab, div_mul_div_comm]

theorem split_exponents_unique {ι : Type*} [DecidableEq ι] (B C : Finset ι)
    (hBC : Disjoint B C) (d a b : ι →₀ ℕ) (hab : a + b = d)
    (ha : a.support ⊆ B) (hb : b.support ⊆ C) :
    a = d.filter (fun i => i ∈ B) ∧ b = d.filter (fun i => i ∉ B) := by
  constructor
  · ext i
    have hi := congrArg (fun f : ι →₀ ℕ => f i) hab
    simp only [Finsupp.add_apply] at hi
    by_cases h : i ∈ B
    · have hb₀ : b i = 0 := by
        by_contra hne
        exact Finset.disjoint_left.mp hBC h (hb (Finsupp.mem_support_iff.mpr hne))
      simp [Finsupp.filter_apply, h]
      omega
    · have ha₀ : a i = 0 := Finsupp.notMem_support_iff.mp (fun hm => h (ha hm))
      simp [Finsupp.filter_apply, h, ha₀]
  · ext i
    have hi := congrArg (fun f : ι →₀ ℕ => f i) hab
    simp only [Finsupp.add_apply] at hi
    by_cases h : i ∈ B
    · have hb₀ : b i = 0 := by
        by_contra hne
        exact Finset.disjoint_left.mp hBC h (hb (Finsupp.mem_support_iff.mpr hne))
      simp [Finsupp.filter_apply, h, hb₀]
    · have ha₀ : a i = 0 := Finsupp.notMem_support_iff.mp (fun hm => h (ha hm))
      simp [Finsupp.filter_apply, h]
      omega

/-- Independence of actual variable blocks gives multiplicativity of the
restricted multivariate exponential-moment series. -/
theorem momentSeries_restrict_mul {n r m : ℕ} (E : FactorFamily n r m)
    (B C : Finset (Fin m)) (hBC : Disjoint B C)
    (hvars : Disjoint (factorVariables E B) (factorVariables E C)) :
    Support.restrictSeries (B ∪ C) (momentSeries E) =
      Support.restrictSeries B (momentSeries E) * Support.restrictSeries C (momentSeries E) := by
  classical
  ext d
  rw [Support.coeff_restrictSeries, MvPowerSeries.coeff_mul]
  by_cases hd : d.support ⊆ B ∪ C
  · rw [if_pos hd]
    let a := d.filter (fun i => i ∈ B)
    let b := d.filter (fun i => i ∉ B)
    have hab : a + b = d := Finsupp.filter_pos_add_filter_neg d (fun i => i ∈ B)
    have ha : a.support ⊆ B := by
      intro i hi
      exact (Finset.mem_filter.mp hi).2
    have hb : b.support ⊆ C := by
      intro i hi
      have hi' := Finset.mem_filter.mp hi
      exact (Finset.mem_union.mp (hd hi'.1)).resolve_left hi'.2
    rw [Finset.sum_eq_single (a, b)]
    · rw [Support.coeff_restrictSeries, Support.coeff_restrictSeries, if_pos ha, if_pos hb]
      rw [← hab]
      exact coeff_momentSeries_add E a b
        (Finset.disjoint_of_subset_left ha (Finset.disjoint_of_subset_right hb hBC))
        (Finset.disjoint_of_subset_left (factorVariables_mono E ha)
          (Finset.disjoint_of_subset_right (factorVariables_mono E hb) hvars))
    · intro p hp hne
      rw [Support.coeff_restrictSeries, Support.coeff_restrictSeries]
      by_cases hp₁ : p.1.support ⊆ B
      · by_cases hp₂ : p.2.support ⊆ C
        · have heq := split_exponents_unique B C hBC d p.1 p.2
            (Finset.mem_antidiagonal.mp hp) hp₁ hp₂
          exact (hne (Prod.ext heq.1 heq.2)).elim
        · simp [hp₂]
      · simp [hp₁]
    · intro hnot
      exact (hnot (Finset.mem_antidiagonal.mpr hab)).elim
  · rw [if_neg hd]
    symm
    apply Finset.sum_eq_zero
    intro p hp
    rw [Support.coeff_restrictSeries, Support.coeff_restrictSeries]
    by_cases hp₁ : p.1.support ⊆ B
    · by_cases hp₂ : p.2.support ⊆ C
      · have hsub : d.support ⊆ B ∪ C := by
          intro i hi
          have hdi : d i ≠ 0 := Finsupp.mem_support_iff.mp hi
          have heq := congrArg (fun f : Fin m →₀ ℕ => f i) (Finset.mem_antidiagonal.mp hp)
          simp only [Finsupp.add_apply] at heq
          by_cases ha : p.1 i = 0
          · have hb : p.2 i ≠ 0 := by omega
            exact Finset.mem_union_right _ (hp₂ (Finsupp.mem_support_iff.mpr hb))
          · exact Finset.mem_union_left _ (hp₁ (Finsupp.mem_support_iff.mpr ha))
        exact (hd hsub).elim
      · simp [hp₂]
    · simp [hp₁]

theorem degree_eq_sum {ι : Type*} [Fintype ι] (d : ι →₀ ℕ) :
    d.degree = ∑ i, d i := by
  exact d.sum_fintype (fun _ n => n) (fun _ => rfl)

/-- All exponent vectors of a fixed total degree. -/
def degreeIndices (ι : Type*) [Fintype ι] (p : ℕ) : Finset (ι →₀ ℕ) := by
  classical
  exact Finset.finsuppAntidiag Finset.univ p

@[simp] theorem mem_degreeIndices {ι : Type*} [Fintype ι] (d : ι →₀ ℕ) (p : ℕ) :
    d ∈ degreeIndices ι p ↔ d.degree = p := by
  classical
  simp only [degreeIndices, Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true,
    degree_eq_sum]

/-- Specialize every variable to the same univariate indeterminate. -/
def diagonalHom (ι : Type*) [Fintype ι] :
    MvPowerSeries ι ℝ →ₐ[ℝ] PowerSeries ℝ :=
  MvPowerSeries.substAlgHom (a := fun _ : ι => (PowerSeries.X : PowerSeries ℝ))
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (by intro _; exact PowerSeries.constantCoeff_X))

theorem prod_X_pow_eq {ι : Type*} (d : ι →₀ ℕ) :
    d.prod (fun _ k => (PowerSeries.X : PowerSeries ℝ) ^ k) = PowerSeries.X ^ d.degree := by
  classical
  simp only [Finsupp.prod, Finsupp.degree, Finsupp.sum, Finset.prod_pow_eq_pow_sum]

/-- Coefficient formula for the actual formal substitution `w_e = z`. -/
theorem coeff_diagonalHom {ι : Type*} [Fintype ι] (F : MvPowerSeries ι ℝ) (p : ℕ) :
    PowerSeries.coeff p (diagonalHom ι F) =
      ∑ d ∈ degreeIndices ι p, MvPowerSeries.coeff d F := by
  classical
  rw [diagonalHom, MvPowerSeries.substAlgHom_apply]
  change MvPowerSeries.coeff (Finsupp.single () p)
    (MvPowerSeries.subst (fun _ : ι => (PowerSeries.X : PowerSeries ℝ)) F) = _
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (by intro _; exact PowerSeries.constantCoeff_X))]
  have hx (d : ι →₀ ℕ) :
      MvPowerSeries.coeff (Finsupp.single () p)
        (d.prod fun _ k => (PowerSeries.X : PowerSeries ℝ) ^ k) =
      if d.degree = p then 1 else 0 := by
    rw [prod_X_pow_eq]
    change PowerSeries.coeff p (PowerSeries.X ^ d.degree) = _
    simp [PowerSeries.coeff_X_pow, eq_comm]
  simp_rw [hx, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [finsum_eq_sum_of_support_subset _ (s := degreeIndices ι p)]
  · apply Finset.sum_congr rfl
    intro d hd
    rw [if_pos ((mem_degreeIndices d p).mp hd)]
  · intro d hd
    have hdeg : d.degree = p := by
      by_contra h
      exact hd (by simp [h])
    exact (mem_degreeIndices d p).mpr hdeg

/-- Multinomial expansion indexed by precisely the local exponent vectors. -/
theorem sum_pow_finsupp {ι : Type*} [DecidableEq ι] (B : Finset ι)
    (f : ι → ℝ) (p : ℕ) :
    (∑ e ∈ B, f e) ^ p = ∑ d ∈ Finset.finsuppAntidiag B p,
      (Nat.multinomial B d : ℝ) * ∏ e ∈ B, f e ^ d e := by
  rw [Finset.finsuppAntidiag, Finset.sum_map]
  change (∑ e ∈ B, f e) ^ p = ∑ d ∈ (Finset.piAntidiag B p).attach,
    (Nat.multinomial B d.val : ℝ) * ∏ e ∈ B, f e ^ d.val e
  exact (Finset.sum_pow_eq_sum_piAntidiag B f p).trans
    (Finset.sum_attach (Finset.piAntidiag B p)
      (fun d => (Nat.multinomial B d : ℝ) * ∏ e ∈ B, f e ^ d e)).symm

theorem primitive_eq_integral_prod {n r m : ℕ} (E : FactorFamily n r m)
    (B : Finset (Fin m)) (d : Fin m →₀ ℕ) (hd : d.support ⊆ B) :
    primitive E d = cubeIntegral (fun x => ∏ e ∈ B, ZeroFree.ell (E e) x ^ d e) := by
  unfold primitive primitiveMoment
  congr 1
  funext x
  rw [← d.prod_fintype (fun e k => ZeroFree.ell (E e) x ^ k) (fun _ => pow_zero _),
    d.prod_of_support_subset hd (fun e k => ZeroFree.ell (E e) x ^ k) (fun _ _ => pow_zero _)]

/-- The actual integral multinomial formula, before normalization by `p!`. -/
theorem rawMoment_multinomial {n r m : ℕ} (E : FactorFamily n r m)
    (B : Finset (Fin m)) {q K : ℝ}
    (hE : ∀ e ∈ B, (E e).RangeOk q) (hLip : ∀ e ∈ B, (E e).LipOk K) (p : ℕ) :
    cubeIntegral (fun x => ZeroFree.sumEll E B x ^ p) =
      ∑ d ∈ Finset.finsuppAntidiag B p, (Nat.multinomial B d : ℝ) * primitive E d := by
  have hInt : ∀ d ∈ Finset.finsuppAntidiag B p,
      IntegrableOn (fun x => (Nat.multinomial B d : ℝ) *
        ∏ e ∈ B, ZeroFree.ell (E e) x ^ d e) (cube n) := by
    intro d hd
    exact (continuousOn_const.mul (continuousOn_finset_prod B fun e he =>
      (ZeroFree.continuousOn_ell (E e) (hE e he) (hLip e he)).pow (d e))).integrableOn_compact
      (ZeroFree.isCompact_cube n)
  simp only [ZeroFree.sumEll, sum_pow_finsupp]
  rw [cubeIntegral_sum _ hInt]
  apply Finset.sum_congr rfl
  intro d hd
  rw [primitive_eq_integral_prod E B d (Finset.mem_finsuppAntidiag.mp hd).2]
  exact integral_const_mul _ _

/-- Equation (2.13), for the same actual moments as `MomentSeries.moment`. -/
theorem moment_eq_sum_primitive {n r m : ℕ} (E : FactorFamily n r m)
    (B : Finset (Fin m)) {q K : ℝ}
    (hE : ∀ e ∈ B, (E e).RangeOk q) (hLip : ∀ e ∈ B, (E e).LipOk K) (p : ℕ) :
    MomentSeries.moment E B p =
      ((∑ d ∈ Finset.finsuppAntidiag B p,
        primitive E d / d.prod (fun _ k => (k.factorial : ℝ))) : ℂ) := by
  have hraw := rawMoment_multinomial E B hE hLip p
  have hnorm : cubeIntegral (fun x => ZeroFree.sumEll E B x ^ p) / (p.factorial : ℝ) =
      ∑ d ∈ Finset.finsuppAntidiag B p,
        primitive E d / d.prod (fun _ k => (k.factorial : ℝ)) := by
    rw [hraw, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d hd
    have hmem := Finset.mem_finsuppAntidiag.mp hd
    have hprod : d.prod (fun _ k => (k.factorial : ℝ)) =
        ∏ e ∈ B, ((d e).factorial : ℝ) :=
      d.prod_of_support_subset hmem.2 _ (by intro _ _; simp)
    have hspec : d.prod (fun _ k => (k.factorial : ℝ)) * (Nat.multinomial B d : ℝ) =
        (p.factorial : ℝ) := by
      rw [hprod]
      exact_mod_cast (Nat.multinomial_spec B d).trans (congrArg Nat.factorial hmem.1)
    have hfac : (p.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero p
    have hden : d.prod (fun _ k => (k.factorial : ℝ)) ≠ 0 := by
      rw [hprod]
      exact Finset.prod_ne_zero_iff.mpr (fun e _ => by exact_mod_cast Nat.factorial_ne_zero (d e))
    apply (div_eq_div_iff hfac hden).mpr
    rw [← hspec]
    ring
  unfold MomentSeries.moment
  have hcoerce : (∫ x in cube n, (ZeroFree.sumEll E B x : ℂ) ^ p) =
      (cubeIntegral (fun x => ZeroFree.sumEll E B x ^ p) : ℂ) := by
    simp_rw [← Complex.ofReal_pow]
    exact integral_ofReal
  rw [hcoerce, ← Complex.ofReal_natCast, ← Complex.ofReal_div, hnorm]
  push_cast
  rfl

/-- A restricted homogeneous component uses exactly the local antidiagonal. -/
theorem degreeIndices_filter (m p : ℕ) (B : Finset (Fin m)) :
    (degreeIndices (Fin m) p).filter (fun d => d.support ⊆ B) = Finset.finsuppAntidiag B p := by
  ext d
  simp only [Finset.mem_filter, mem_degreeIndices, Finset.mem_finsuppAntidiag']
  rfl

/-- Diagonal substitution of the actual multivariate moment series gives the
actual univariate normalized integral moments. -/
theorem diagonal_momentSeries {n r m : ℕ} (E : FactorFamily n r m)
    (B : Finset (Fin m)) {q K : ℝ}
    (hE : ∀ e ∈ B, (E e).RangeOk q) (hLip : ∀ e ∈ B, (E e).LipOk K) (p : ℕ) :
    ((PowerSeries.coeff p (diagonalHom (Fin m)
      (Support.restrictSeries B (momentSeries E))) : ℝ) : ℂ) = MomentSeries.moment E B p := by
  rw [coeff_diagonalHom]
  simp only [Support.coeff_restrictSeries]
  rw [← Finset.sum_filter, degreeIndices_filter]
  rw [moment_eq_sum_primitive E B hE hLip p]
  push_cast
  apply Finset.sum_congr rfl
  intro d hd
  rw [coeff_momentSeries, d.prod_fintype (fun _ k => (k.factorial : ℝ)) (by intro _; simp)]
  push_cast
  rfl

end Paper08.MultiMoments
