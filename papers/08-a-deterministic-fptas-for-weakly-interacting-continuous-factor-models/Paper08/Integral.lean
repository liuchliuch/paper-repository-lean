import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import Paper08.Basic
import Paper08.FactorModel

/-!
# Measure-theoretic integral layer

Cube volume, Bochner integrals of local functions, the partition function (1.1),
primitive moments (2.13), integral range and error bounds, and Fubini
factorization on disjoint coordinate blocks (the analytic content of Lemma A.1).
The actual sampled dyadic functions are defined in `Paper08.Dyadic`.

All statements below are completely proved (no `sorry`, no extra axioms).
-/

noncomputable section

open scoped Real BigOperators ENNReal

namespace Paper08
namespace Integral

open MeasureTheory Measure

/-! ## The unit cube and its volume -/

/-- The unit cube `[0,1]^k` inside `Fin k → ℝ`, as a product of unit intervals.
This is the same pointwise predicate as `Paper08.euclCube`, on `Fin k → ℝ`. -/
def cube (k : ℕ) : Set (Fin k → ℝ) := Set.pi Set.univ fun _ => Set.Icc (0:ℝ) 1

lemma mem_cube {k : ℕ} {x : Fin k → ℝ} : x ∈ cube k ↔ ∀ i, 0 ≤ x i ∧ x i ≤ 1 := by
  change (∀ i, i ∈ (Set.univ : Set (Fin k)) → 0 ≤ x i ∧ x i ≤ 1) ↔ _
  simp

lemma cube_eq (k : ℕ) : cube k = {x | ∀ i : Fin k, 0 ≤ x i ∧ x i ≤ 1} := by
  ext x; exact mem_cube

lemma measurableSet_cube (k : ℕ) : MeasurableSet (cube k) := by
  refine MeasurableSet.pi (Set.countable_univ) fun i _ => ?_
  exact measurableSet_Icc

lemma volume_cube (k : ℕ) : volume (cube k) = 1 := by
  rw [cube, volume_pi_pi]
  simp [Real.volume_Icc]

lemma volume_real_cube (k : ℕ) : (volume (cube k)).toReal = 1 := by
  rw [volume_cube]; exact ENNReal.toReal_one

lemma volume_cube_lt_top (k : ℕ) : volume (cube k) < ∞ := by
  rw [volume_cube]; exact ENNReal.one_lt_top

/-! ## Integrals over the cube -/

/-- Integral of `f` over the unit cube `[0,1]^k` with respect to Lebesgue measure. -/
def cubeIntegral {k : ℕ} (f : (Fin k → ℝ) → ℝ) : ℝ :=
  ∫ x in cube k, f x

@[simp]
lemma cubeIntegral_const {k : ℕ} (c : ℝ) :
    cubeIntegral (fun _ : Fin k → ℝ => c) = c := by
  rw [cubeIntegral, setIntegral_const]
  simp [Measure.real, volume_cube]

lemma cubeIntegral_one {k : ℕ} :
    cubeIntegral (fun _ : Fin k → ℝ => (1:ℝ)) = 1 :=
  cubeIntegral_const 1

lemma cubeIntegral_add {k : ℕ} {f g : (Fin k → ℝ) → ℝ}
    (hf : IntegrableOn f (cube k)) (hg : IntegrableOn g (cube k)) :
    cubeIntegral (fun x => f x + g x) = cubeIntegral f + cubeIntegral g :=
  integral_add hf hg

lemma cubeIntegral_sum {k : ℕ} {ι : Type*} (s : Finset ι) {f : ι → (Fin k → ℝ) → ℝ}
    (hf : ∀ i ∈ s, IntegrableOn (f i) (cube k)) :
    cubeIntegral (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, cubeIntegral (f i) := by
  exact integral_finset_sum s hf
  -- `IntegrableOn f (cube k)` unfolds to `Integrable f (volume.restrict (cube k))`

lemma abs_cubeIntegral_le_of_abs_le {k : ℕ} {f : (Fin k → ℝ) → ℝ} {C : ℝ}
    (h : ∀ x ∈ cube k, |f x| ≤ C) : |cubeIntegral f| ≤ C := by
  have hnorm : ∀ x ∈ cube k, ‖f x‖ ≤ C := by
    intro x hx
    simpa [Real.norm_eq_abs] using h x hx
  have hle := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure (Fin k → ℝ)))
    (volume_cube_lt_top k) hnorm
  simp only [Measure.real, volume_cube, ENNReal.toReal_one, mul_one] at hle
  simpa [cubeIntegral, Real.norm_eq_abs] using hle

/-- General sup-norm bound `|∫ f| ≤ vol(cube) · ‖f‖_∞`, specialised to unit volume. -/
lemma abs_cubeIntegral_le_of_bound {k : ℕ} {f : (Fin k → ℝ) → ℝ}
    (hf : LocalFunc.BoundBy ⟨f⟩ C) : |cubeIntegral f| ≤ C :=
  abs_cubeIntegral_le_of_abs_le fun x hx => hf x (mem_cube.mp hx)

lemma abs_cubeIntegral_le {k : ℕ} {f : (Fin k → ℝ) → ℝ}
    (h : ∀ x ∈ cube k, |f x| ≤ C) : |cubeIntegral f| ≤ C :=
  abs_cubeIntegral_le_of_abs_le h

/-- Bounded measurable functions are integrable on the unit cube. -/
lemma integrableOn_cube_of_bound {k : ℕ} {f : (Fin k → ℝ) → ℝ} {C : ℝ}
    (hfm : Measurable f) (hf : ∀ x ∈ cube k, |f x| ≤ C) :
    IntegrableOn f (cube k) := by
  apply Measure.integrableOn_of_bounded (volume_cube_lt_top k).ne hfm.aestronglyMeasurable
  exact (ae_restrict_mem (measurableSet_cube k)).mono fun x hx => by
    simpa only [Real.norm_eq_abs] using hf x hx

/-- Integrating a pointwise lower bound over the unit-volume cube. -/
lemma le_cubeIntegral {k : ℕ} {f : (Fin k → ℝ) → ℝ} {C : ℝ}
    (hf : IntegrableOn f (cube k)) (h : ∀ x ∈ cube k, C ≤ f x) :
    C ≤ cubeIntegral f := by
  have hc : IntegrableOn (fun _ : Fin k → ℝ => C) (cube k) :=
    integrableOn_const (volume_cube_lt_top k).ne
  have hle := setIntegral_mono_on hc hf (measurableSet_cube k) h
  change cubeIntegral (fun _ => C) ≤ cubeIntegral f at hle
  simpa only [cubeIntegral_const] using hle

/-- Integrating a pointwise upper bound over the unit-volume cube. -/
lemma cubeIntegral_le {k : ℕ} {f : (Fin k → ℝ) → ℝ} {C : ℝ}
    (hf : IntegrableOn f (cube k)) (h : ∀ x ∈ cube k, f x ≤ C) :
    cubeIntegral f ≤ C := by
  have hc : IntegrableOn (fun _ : Fin k → ℝ => C) (cube k) :=
    integrableOn_const (volume_cube_lt_top k).ne
  have hle := setIntegral_mono_on hf hc (measurableSet_cube k) h
  change cubeIntegral f ≤ cubeIntegral (fun _ => C) at hle
  simpa only [cubeIntegral_const] using hle

/-- Supremum error of two integrable functions controls their integral error. -/
lemma abs_cubeIntegral_sub_le {k : ℕ} {f g : (Fin k → ℝ) → ℝ} {C : ℝ}
    (hf : IntegrableOn f (cube k)) (hg : IntegrableOn g (cube k))
    (h : ∀ x ∈ cube k, |f x - g x| ≤ C) :
    |cubeIntegral f - cubeIntegral g| ≤ C := by
  have hh := abs_cubeIntegral_le h
  simpa only [cubeIntegral, integral_sub hf hg] using hh

/-! ## Pullbacks of local functions -/

/-- Restrict an ambient point `x : Fin n → ℝ` to the coordinates of a scope. -/
def restrictTo {n : ℕ} (s : Finset (Fin n)) (x : Fin n → ℝ) : Fin s.card → ℝ :=
  fun i => x (s.orderEmbOfFin rfl i)

lemma restrictTo_mem_cube {n : ℕ} (s : Finset (Fin n)) {x : Fin n → ℝ}
    (hx : x ∈ cube n) : restrictTo s x ∈ cube s.card := by
  rw [mem_cube] at hx ⊢
  exact fun i => hx (s.orderEmbOfFin rfl i)

lemma measurable_restrictTo {n : ℕ} (s : Finset (Fin n)) : Measurable (restrictTo s) := by
  exact measurable_pi_lambda _ fun i => measurable_pi_apply (s.orderEmbOfFin rfl i)

/-- Pull a local function on the scope `s` back to an ambient function on `Fin n → ℝ`. -/
def pullback {n : ℕ} (s : Finset (Fin n)) (f : LocalFunc s.card) : (Fin n → ℝ) → ℝ :=
  fun x => f.toFun (restrictTo s x)

lemma measurable_pullback {n : ℕ} (s : Finset (Fin n)) (f : LocalFunc s.card)
    (hf : Measurable f.toFun) : Measurable (pullback s f) :=
  hf.comp (measurable_restrictTo s)

lemma pullback_bound {n : ℕ} {s : Finset (Fin n)} {f : LocalFunc s.card} {A : ℝ}
    (hf : f.BoundBy A) {x : Fin n → ℝ} (hx : x ∈ cube n) : |pullback s f x| ≤ A :=
  hf _ (mem_cube.mp (restrictTo_mem_cube s hx))

/-- Ambient representative of a labelled factor. -/
def Factor.ambient {n r : ℕ} (e : Factor n r) : (Fin n → ℝ) → ℝ :=
  pullback e.scope e.psi

lemma factor_ambient_apply {n r : ℕ} (e : Factor n r) (x : Fin n → ℝ) :
    Factor.ambient e x = e.psi.toFun (restrictTo e.scope x) := rfl

/-! ## Partition function and primitive moments -/

/-- Partition function `Z = ∫_{[0,1]^n} ∏_i ψ_i(x) dx` of (1.1), in an ambient
coordinate space `Fin n → ℝ`.  Local functions are already pulled back. -/
def partitionFunction (n : ℕ) {ι : Type*} [Fintype ι] (ψ : ι → (Fin n → ℝ) → ℝ) : ℝ :=
  cubeIntegral (fun x => ∏ i, ψ i x)

/-- Partition function of a labelled family of factors. -/
def partitionFunctionFactor {n r : ℕ} {ι : Type*} [Fintype ι] (E : ι → Factor n r) : ℝ :=
  partitionFunction n (fun i => Factor.ambient (E i))

/-- Primitive moment `I_α` of (2.13): integral of a product of powers of local
functions (typically log-factors `ℓ_e^{α_e}`) over the unit cube. -/
def primitiveMoment (n : ℕ) {ι : Type*} [Fintype ι]
    (ℓ : ι → (Fin n → ℝ) → ℝ) (α : ι → ℕ) : ℝ :=
  cubeIntegral (fun x => ∏ i, ℓ i x ^ α i)

lemma partitionFunction_zero {n : ℕ} {ι : Type*} [Fintype ι] :
    partitionFunction n (fun _ : ι => fun _ : Fin n → ℝ => (1:ℝ)) = 1 := by
  simp [partitionFunction]

lemma primitiveMoment_zero {n : ℕ} {ι : Type*} [Fintype ι] (ℓ : ι → (Fin n → ℝ) → ℝ) :
    primitiveMoment n ℓ (fun _ => 0) = 1 := by
  simp [primitiveMoment]

/-! ## Fubini factorization on disjoint blocks (Lemma A.1 core) -/

/-- Left `k` coordinates of a point of `Fin (k + l) → ℝ`. -/
def leftCoords (k l : ℕ) (x : Fin (k + l) → ℝ) : Fin k → ℝ :=
  fun i => x (Fin.castAdd l i)

/-- Right `l` coordinates of a point of `Fin (k + l) → ℝ`. -/
def rightCoords (k l : ℕ) (x : Fin (k + l) → ℝ) : Fin l → ℝ :=
  fun i => x (Fin.natAdd k i)

/-- Product of independent local functions on two cubes. -/
theorem setIntegral_prod_mul_cube {k l : ℕ}
    (f : (Fin k → ℝ) → ℝ) (g : (Fin l → ℝ) → ℝ) :
    ∫ z in (cube k ×ˢ cube l : Set ((Fin k → ℝ) × (Fin l → ℝ))),
        f z.1 * g z.2 ∂((volume : Measure (Fin k → ℝ)).prod (volume : Measure (Fin l → ℝ)))
      = (∫ x in cube k, f x) * ∫ y in cube l, g y :=
  setIntegral_prod_mul f g (cube k) (cube l)

/-- Two-block factorization on `Fin (k + l) → ℝ`: if the two local functions
occupy disjoint coordinate blocks, the integral of the product is the product
of the integrals.  This is the analytic content of `Z = ∏_C I_C` in Lemma A.1. -/
theorem cubeIntegral_split_two {k l : ℕ}
    (f : (Fin k → ℝ) → ℝ) (g : (Fin l → ℝ) → ℝ) :
    cubeIntegral (fun x : Fin (k + l) → ℝ => f (leftCoords k l x) * g (rightCoords k l x))
      = cubeIntegral f * cubeIntegral g := by
  -- Transport along the measure-preserving equivalence
  -- `Fin (k+l) → ℝ ≃ (Fin k → ℝ) × (Fin l → ℝ)`.
  let e : (Fin (k + l) → ℝ) ≃ᵐ ((Fin k → ℝ) × (Fin l → ℝ)) :=
    ((MeasurableEquiv.piCongrLeft (fun _ => ℝ)
        (finSumFinEquiv : Fin k ⊕ Fin l ≃ Fin (k + l))).symm).trans
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin k ⊕ Fin l => ℝ))
  have hsplit : ∀ x : Fin (k + l) → ℝ,
      e x = (leftCoords k l x, rightCoords k l x) := by
    intro x
    apply Prod.ext <;> ext i <;> rfl
  have hcube : e ⁻¹' (cube k ×ˢ cube l) = cube (k + l) := by
    ext x
    rw [Set.mem_preimage, hsplit, Set.mem_prod, mem_cube, mem_cube, mem_cube]
    constructor
    · intro h i
      exact Fin.addCases h.1 h.2 i
    · intro h
      exact ⟨fun i => h (Fin.castAdd l i), fun i => h (Fin.natAdd k i)⟩
  -- The actual factorization is `setIntegral_prod_mul_cube`; the remaining
  -- transport is the measure-preserving change of variables.
  have hmp : MeasurePreserving e (volume : Measure (Fin (k + l) → ℝ))
      ((volume : Measure (Fin k → ℝ)).prod volume) := by
    refine ⟨e.measurable, ?_⟩
    have h1 : MeasurePreserving
        (MeasurableEquiv.piCongrLeft (fun _ => ℝ)
          (finSumFinEquiv : Fin k ⊕ Fin l ≃ Fin (k + l))).symm
        (volume : Measure (Fin (k + l) → ℝ))
        (volume : Measure (Fin k ⊕ Fin l → ℝ)) := by
      have := volume_measurePreserving_piCongrLeft (fun _ => ℝ)
        (finSumFinEquiv : Fin k ⊕ Fin l ≃ Fin (k + l))
      exact this.symm
    have h2 : MeasurePreserving
        (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin k ⊕ Fin l => ℝ))
        (volume : Measure (Fin k ⊕ Fin l → ℝ))
        ((volume : Measure (Fin k → ℝ)).prod volume) :=
      volume_measurePreserving_sumPiEquivProdPi _
    exact (h1.trans h2).map_eq
  unfold cubeIntegral
  rw [← setIntegral_prod_mul_cube f g]
  have hrestricted := hmp.restrict_preimage ((measurableSet_cube k).prod (measurableSet_cube l))
  have heq := hrestricted.integral_comp e.measurableEmbedding (fun z => f z.1 * g z.2)
  rw [hcube] at heq
  simpa only [hsplit] using heq

/-- Lebesgue cube integration is invariant under a relabelling of coordinates. -/
theorem cubeIntegral_reindex {n : ℕ} (p : Equiv.Perm (Fin n)) (f : (Fin n → ℝ) → ℝ) :
    cubeIntegral (fun x => f (fun i => x (p i))) = cubeIntegral f := by
  let e : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) :=
    (MeasurableEquiv.piCongrLeft (fun _ => ℝ) p).symm
  have haction : ∀ x i, e x i = x (p i) := by intro x i; rfl
  have hc : e ⁻¹' cube n = cube n := by
    ext x
    rw [Set.mem_preimage, mem_cube, mem_cube]
    simp only [haction]
    constructor
    · intro hx i
      simpa only [p.apply_symm_apply] using hx (p.symm i)
    · exact fun hx i => hx (p i)
  have hmp : MeasurePreserving e volume volume :=
    (volume_measurePreserving_piCongrLeft (fun _ => ℝ) p).symm
  have hi := (hmp.restrict_preimage (measurableSet_cube n)).integral_comp e.measurableEmbedding f
  rw [hc] at hi
  exact hi

/-- Fubini for any two disjoint blocks obtained by relabelling all coordinates. -/
theorem cubeIntegral_split_perm {k l : ℕ} (p : Equiv.Perm (Fin (k + l)))
    (f : (Fin k → ℝ) → ℝ) (g : (Fin l → ℝ) → ℝ) :
    cubeIntegral (fun x => f (fun i => x (p (Fin.castAdd l i))) *
      g (fun i => x (p (Fin.natAdd k i)))) = cubeIntegral f * cubeIntegral g := by
  calc
    _ = cubeIntegral (fun x => f (leftCoords k l x) * g (rightCoords k l x)) :=
      cubeIntegral_reindex p _
    _ = _ := cubeIntegral_split_two f g

end Integral
end Paper08
