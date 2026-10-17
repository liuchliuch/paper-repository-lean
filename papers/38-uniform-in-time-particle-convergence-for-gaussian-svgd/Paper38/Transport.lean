import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms

/-!
The transport object in this file is the infimum of the quadratic cost over
actual joint measures with the prescribed marginal measures. It is extended
valued, so neither existence of an optimal plan nor finite moments is needed
for the affine lifting argument. On probability measures with second moments
this is the usual squared quadratic Wasserstein distance.
-/

open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Paper38.Transport

noncomputable section

variable {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]

/-- A joint measure with its two prescribed marginals. -/
structure Coupling (μ ν : Measure E) where
  measure : Measure (E × E)
  fst_eq : measure.map Prod.fst = μ
  snd_eq : measure.map Prod.snd = ν

namespace Coupling

/-- Independent coupling; used only to certify that probability couplings exist. -/
def independent (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Coupling μ ν where
  measure := μ.prod ν
  fst_eq := by simp
  snd_eq := by simp

/-- Push both coordinates of a joint measure through the same measurable map. -/
def map {μ ν : Measure E} (π : Coupling μ ν) (f : E → F) (hf : Measurable f) :
    Coupling (μ.map f) (ν.map f) where
  measure := π.measure.map (fun p => (f p.1, f p.2))
  fst_eq := by
    rw [Measure.map_map measurable_fst (show Measurable (fun p : E × E => (f p.1, f p.2)) from
      (hf.comp measurable_fst).prodMk (hf.comp measurable_snd))]
    change π.measure.map (f ∘ Prod.fst) = μ.map f
    rw [← Measure.map_map hf measurable_fst, π.fst_eq]
  snd_eq := by
    rw [Measure.map_map measurable_snd (show Measurable (fun p : E × E => (f p.1, f p.2)) from
      (hf.comp measurable_fst).prodMk (hf.comp measurable_snd))]
    change π.measure.map (f ∘ Prod.snd) = ν.map f
    rw [← Measure.map_map hf measurable_snd, π.snd_eq]

/-- Synchronous coupling of two random variables on the same source space. -/
def synchronous {Ω : Type*} [MeasurableSpace Ω] (θ : Measure Ω)
    (f g : Ω → E) (hf : Measurable f) (hg : Measurable g) :
    Coupling (θ.map f) (θ.map g) where
  measure := θ.map (fun ω => (f ω, g ω))
  fst_eq := by
    rw [Measure.map_map measurable_fst (hf.prodMk hg)]
    rfl
  snd_eq := by
    rw [Measure.map_map measurable_snd (hf.prodMk hg)]
    rfl

end Coupling

variable [PseudoEMetricSpace E] [BorelSpace E] [SecondCountableTopology E]
variable [PseudoEMetricSpace F] [BorelSpace F] [SecondCountableTopology F]

/-- Extended quadratic transport cost of a joint measure. -/
noncomputable def quadraticCost (π : Measure (E × E)) : ℝ≥0∞ :=
  ∫⁻ p, edist p.1 p.2 ^ 2 ∂π

/-- The infimum of actual quadratic coupling costs. -/
noncomputable def w2sq (μ ν : Measure E) : ℝ≥0∞ :=
  ⨅ π : Coupling μ ν, quadraticCost π.measure

lemma w2sq_le_cost {μ ν : Measure E} (π : Coupling μ ν) :
    w2sq μ ν ≤ quadraticCost π.measure :=
  iInf_le _ π

lemma quadraticCost_map {μ ν : Measure E} (π : Coupling μ ν)
    (f : E → F) (hf : Measurable f) :
    quadraticCost (π.map f hf).measure =
      ∫⁻ p, edist (f p.1) (f p.2) ^ 2 ∂π.measure := by
  unfold quadraticCost Coupling.map
  rw [lintegral_map (by fun_prop) (by fun_prop)]

/-- A common-source coupling gives a cost upper bound, including index couplings. -/
theorem w2sq_map_map_le {Ω : Type*} [MeasurableSpace Ω] (θ : Measure Ω)
    (f g : Ω → E) (hf : Measurable f) (hg : Measurable g) :
    w2sq (θ.map f) (θ.map g) ≤ ∫⁻ ω, edist (f ω) (g ω) ^ 2 ∂θ := by
  calc
    w2sq (θ.map f) (θ.map g) ≤
        quadraticCost (Coupling.synchronous θ f g hf hg).measure :=
      w2sq_le_cost _
    _ = _ := by
      unfold quadraticCost Coupling.synchronous
      rw [lintegral_map (by fun_prop) (hf.prodMk hg)]

/-- Every pointwise quadratic distortion bound passes to coupling costs. -/
lemma quadraticCost_map_le {μ ν : Measure E} (π : Coupling μ ν)
    (f : E → F) (hf : Measurable f) (c : ℝ≥0∞)
    (h : ∀ x y, edist (f x) (f y) ^ 2 ≤ c * edist x y ^ 2) :
    quadraticCost (π.map f hf).measure ≤ c * quadraticCost π.measure := by
  rw [quadraticCost_map, quadraticCost, ← lintegral_const_mul c (by fun_prop)]
  exact lintegral_mono (fun p => h p.1 p.2)

/-- Pushforward upper bound for the genuine quadratic transport infimum. -/
theorem w2sq_map_le (μ ν : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : E → F) (hf : Measurable f) (c : ℝ≥0)
    (h : ∀ x y, edist (f x) (f y) ^ 2 ≤ (c : ℝ≥0∞) * edist x y ^ 2) :
    w2sq (μ.map f) (ν.map f) ≤ (c : ℝ≥0∞) * w2sq μ ν := by
  letI : Nonempty (Coupling μ ν) := ⟨Coupling.independent μ ν⟩
  change w2sq (μ.map f) (ν.map f) ≤ (c : ℝ≥0∞) *
    (⨅ π : Coupling μ ν, quadraticCost π.measure)
  rw [ENNReal.mul_iInf (by simp)]
  apply le_iInf
  intro π
  exact (w2sq_le_cost (π.map f hf)).trans (quadraticCost_map_le π f hf c h)

/-- Pullback lower bound. No minimizer or disintegration theorem is assumed. -/
theorem le_w2sq_map (μ ν : Measure E) (f : E ≃ᵐ F) (c : ℝ≥0∞)
    (h : ∀ x y, c * edist x y ^ 2 ≤ edist (f x) (f y) ^ 2) :
    c * w2sq μ ν ≤ w2sq (μ.map f) (ν.map f) := by
  apply le_iInf
  intro π
  let π' : Coupling μ ν :=
    { measure := (π.map f.symm f.symm.measurable).measure
      fst_eq := by
        rw [(π.map f.symm f.symm.measurable).fst_eq]
        exact MeasurableEquiv.map_symm_map f
      snd_eq := by
        rw [(π.map f.symm f.symm.measurable).snd_eq]
        exact MeasurableEquiv.map_symm_map f }
  calc
    c * w2sq μ ν ≤ c * quadraticCost π'.measure :=
      mul_le_mul_left' (w2sq_le_cost π') c
    _ = ∫⁻ p, c * edist (f.symm p.1) (f.symm p.2) ^ 2 ∂π.measure := by
      change c * quadraticCost (π.map f.symm f.symm.measurable).measure = _
      rw [quadraticCost_map, ← lintegral_const_mul c (by fun_prop)]
    _ ≤ quadraticCost π.measure := by
      apply lintegral_mono
      intro p
      simpa using h (f.symm p.1) (f.symm p.2)

/-- Two-sided affine lifting in its exact measure-theoretic generality.
The constants are the lower and upper squared distance distortion factors. -/
theorem two_sided_lifting (μ ν : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : E ≃ᵐ F) (a b : ℝ≥0)
    (hlower : ∀ x y, (a : ℝ≥0∞) * edist x y ^ 2 ≤ edist (f x) (f y) ^ 2)
    (hupper : ∀ x y, edist (f x) (f y) ^ 2 ≤ (b : ℝ≥0∞) * edist x y ^ 2) :
    (a : ℝ≥0∞) * w2sq μ ν ≤ w2sq (μ.map f) (ν.map f) ∧
    w2sq (μ.map f) (ν.map f) ≤ (b : ℝ≥0∞) * w2sq μ ν :=
  ⟨le_w2sq_map μ ν f a hlower, w2sq_map_le μ ν f f.measurable b hupper⟩

/-- Every coupling pays at least the squared distance of the second marginal
from a closed set supporting its first marginal. -/
theorem distance_to_support_lower (μ ν : Measure E) (S : Set E)
    (hμ : ∀ᵐ x ∂μ, x ∈ S) :
    (∫⁻ y, EMetric.infEdist y S ^ 2 ∂ν) ≤ w2sq μ ν := by
  apply le_iInf
  intro π
  have hfirst : ∀ᵐ p ∂π.measure, p.1 ∈ S := by
    apply ae_of_ae_map measurable_fst.aemeasurable
    rwa [π.fst_eq]
  calc
    (∫⁻ y, EMetric.infEdist y S ^ 2 ∂ν) =
        ∫⁻ p, EMetric.infEdist p.2 S ^ 2 ∂π.measure := by
      have hm := lintegral_map (μ := π.measure)
        (f := fun y : E => EMetric.infEdist y S ^ 2) (by fun_prop) measurable_snd
      simpa only [π.snd_eq] using hm
    _ ≤ quadraticCost π.measure := by
      apply lintegral_mono_ae
      filter_upwards [hfirst] with p hp
      have hi := EMetric.infEdist_le_edist_of_mem (x := p.2) (y := p.1) hp
      simpa only [edist_comm] using pow_le_pow_left' hi 2

/-- Positive full-law error follows from a closed supporting set omitted with
positive mass by the target. The proof uses a common positive integral lower
bound, rather than merely showing that each individual plan costs something. -/
theorem w2sq_pos_of_supported_closed (μ ν : Measure E) (S : Set E)
    (hS : IsClosed S) (hμ : ∀ᵐ x ∂μ, x ∈ S) (hν : ν Sᶜ ≠ 0) :
    0 < w2sq μ ν := by
  have hsupp : Sᶜ ⊆ Function.support (fun y => EMetric.infEdist y S ^ 2) := by
    intro y hy
    change EMetric.infEdist y S ^ 2 ≠ 0
    apply pow_ne_zero 2
    apply ne_of_gt
    exact EMetric.infEdist_pos_iff_notMem_closure.mpr (by simpa [hS.closure_eq] using hy)
  have hpos : 0 < ∫⁻ y, EMetric.infEdist y S ^ 2 ∂ν := by
    apply (lintegral_pos_iff_support (by fun_prop)).mpr
    exact (pos_iff_ne_zero.mpr hν).trans_le (measure_mono hsupp)
  exact hpos.trans_le (distance_to_support_lower μ ν S hμ)

section Empirical

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- Uniform counting law on the particle indices. -/
def indexLaw (ι : Type*) [Fintype ι] [MeasurableSpace ι] : Measure ι :=
  (Fintype.card ι : ℝ≥0∞)⁻¹ • Measure.count

/-- Empirical particle law: the pushforward of normalized counting measure. -/
def empirical (x : ι → E) : Measure E :=
  (indexLaw ι).map x

lemma empirical_eq_sum (x : ι → E) :
    empirical x = (Fintype.card ι : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (x i) := by
  rw [empirical, indexLaw, Measure.map_smul, Measure.count,
    Measure.map_sum (measurable_of_finite x).aemeasurable]
  simp only [Measure.map_dirac (measurable_of_finite x), Measure.sum_fintype]

instance indexLaw_isProbabilityMeasure [Nonempty ι] : IsProbabilityMeasure (indexLaw ι) where
  measure_univ := by
    have hc : (Fintype.card ι : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    simpa [indexLaw, Measure.count_apply] using
      ENNReal.inv_mul_cancel hc (by simp : (Fintype.card ι : ℝ≥0∞) ≠ ∞)

instance empirical_isProbabilityMeasure [Nonempty ι] (x : ι → E) :
    IsProbabilityMeasure (empirical x) :=
  Measure.isProbabilityMeasure_map (measurable_of_finite x).aemeasurable

/-- Coupling the same particle index proves the empirical quadratic bound. -/
theorem indexed_coupling_upper (x y : ι → E) :
    w2sq (empirical x) (empirical y) ≤
      (Fintype.card ι : ℝ≥0∞)⁻¹ * ∑ i, edist (x i) (y i) ^ 2 := by
  convert w2sq_map_map_le (indexLaw ι) x y
    (measurable_of_finite x) (measurable_of_finite y) using 1
  simp [indexLaw, lintegral_count, tsum_fintype]

/-- A finitely atomic empirical law stays at strictly positive quadratic
transport distance from every nonatomic probability target. -/
theorem empirical_w2sq_pos [T2Space E] (x : ι → E) (ν : Measure E)
    [IsProbabilityMeasure ν] [NoAtoms ν] : 0 < w2sq (empirical x) ν := by
  have hfin : (Set.range x).Finite := Set.finite_range x
  apply w2sq_pos_of_supported_closed (empirical x) ν (Set.range x) hfin.isClosed
  · exact ae_map_mem_range x hfin.measurableSet (indexLaw ι)
  · rw [prob_compl_eq_one_sub hfin.measurableSet, hfin.measure_zero ν]
    simp

end Empirical

section Affine

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]

/-- The actual invertible affine map used to lift the standardized cloud. -/
def affineEquiv (m : G) (B : G ≃L[ℝ] G) : G ≃ᵐ G :=
  (B.toHomeomorph.trans (Homeomorph.addLeft m)).toMeasurableEquiv

@[simp] lemma affineEquiv_apply (m : G) (B : G ≃L[ℝ] G) (x : G) :
    affineEquiv m B x = m + B x := rfl

@[simp] lemma affineEquiv_symm_apply (m : G) (B : G ≃L[ℝ] G) (x : G) :
    (affineEquiv m B).symm x = B.symm (x - m) := by
  simp [affineEquiv, Homeomorph.addLeft_symm, sub_eq_add_neg, add_comm]

/-- Affine lifting with any verified lower and upper spectral bounds on the
linear part. For a matrix B these factors may be chosen as the extreme
eigenvalues of B Bᵀ; no assertion about those eigenvalues is postulated here. -/
theorem affine_two_sided (μ ν : Measure G)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (m : G) (B : G ≃L[ℝ] G) (a b : ℝ≥0)
    (hlower : ∀ u, a * ‖u‖₊ ^ 2 ≤ ‖B u‖₊ ^ 2)
    (hupper : ∀ u, ‖B u‖₊ ^ 2 ≤ b * ‖u‖₊ ^ 2) :
    (a : ℝ≥0∞) * w2sq μ ν ≤
      w2sq (μ.map (affineEquiv m B)) (ν.map (affineEquiv m B)) ∧
    w2sq (μ.map (affineEquiv m B)) (ν.map (affineEquiv m B)) ≤
      (b : ℝ≥0∞) * w2sq μ ν := by
  apply two_sided_lifting μ ν (affineEquiv m B) a b
  · intro x y
    simpa only [affineEquiv_apply, edist_add_left, edist_nndist,
      nndist_eq_nnnorm_sub, add_sub_add_left_eq_sub, ← map_sub, ← ENNReal.coe_pow, ← ENNReal.coe_mul,
      ENNReal.coe_le_coe] using hlower (x - y)
  · intro x y
    simpa only [affineEquiv_apply, edist_add_left, edist_nndist,
      nndist_eq_nnnorm_sub, add_sub_add_left_eq_sub, ← map_sub, ← ENNReal.coe_pow, ← ENNReal.coe_mul,
      ENNReal.coe_le_coe] using hupper (x - y)

/-- The affine upper bound with the exact squared operator norm. -/
theorem affine_w2sq_le (μ ν : Measure G)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (m : G) (B : G ≃L[ℝ] G) :
    w2sq (μ.map (affineEquiv m B)) (ν.map (affineEquiv m B)) ≤
      (‖(B : G →L[ℝ] G)‖₊ : ℝ≥0∞) ^ 2 * w2sq μ ν := by
  have hu := w2sq_map_le μ ν (affineEquiv m B) (affineEquiv m B).measurable
    (‖(B : G →L[ℝ] G)‖₊ ^ 2) (by
      intro x y
      have hb := pow_le_pow_left' (B.lipschitz.edist_le_mul x y) 2
      simpa [mul_pow] using hb)
  simpa using hu

/-- The reverse operator-norm bound obtained by pulling back every image coupling. -/
theorem affine_w2sq_inverse_le (μ ν : Measure G)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (m : G) (B : G ≃L[ℝ] G) :
    w2sq μ ν ≤ (‖(B.symm : G →L[ℝ] G)‖₊ : ℝ≥0∞) ^ 2 *
      w2sq (μ.map (affineEquiv m B)) (ν.map (affineEquiv m B)) := by
  let f := affineEquiv m B
  have hi : ∀ x y, edist (f.symm x) (f.symm y) ^ 2 ≤
      (‖(B.symm : G →L[ℝ] G)‖₊ ^ 2 : ℝ≥0) * edist x y ^ 2 := by
    intro x y
    have hb := pow_le_pow_left' (B.symm.lipschitz.edist_le_mul (x - m) (y - m)) 2
    simpa [f, mul_pow] using hb
  letI : IsProbabilityMeasure (μ.map f) :=
    Measure.isProbabilityMeasure_map f.measurable.aemeasurable
  letI : IsProbabilityMeasure (ν.map f) :=
    Measure.isProbabilityMeasure_map f.measurable.aemeasurable
  have hu := w2sq_map_le (μ.map f) (ν.map f) f.symm f.symm.measurable
    (‖(B.symm : G →L[ℝ] G)‖₊ ^ 2) hi
  simpa [f, MeasurableEquiv.map_symm_map] using hu

end Affine

end

end Paper38.Transport
