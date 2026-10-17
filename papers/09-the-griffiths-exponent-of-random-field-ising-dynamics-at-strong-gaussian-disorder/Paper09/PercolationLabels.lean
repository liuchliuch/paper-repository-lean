import Paper09.BadClusters
import Paper09.ProductCoordinates
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Finset BigOperators Classical MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section
set_option maxHeartbeats 1000000

namespace Paper09.Percolation

instance environmentLaw_isProbabilityMeasure (d : ℕ) (σ : ℝ) :
    IsProbabilityMeasure (RFIM.environmentLaw d σ) := by
  unfold RFIM.environmentLaw
  infer_instance

/-- The actual uniform probability measure on `[0,1]`. -/
def uniformLaw : Measure ℝ := volume.restrict (Set.Icc 0 1)

instance uniformLaw_isProbabilityMeasure : IsProbabilityMeasure uniformLaw := by
  constructor
  simp [uniformLaw]

/-- Independent uniform auxiliary variables on the entire integer lattice. -/
def noiseLaw (d : ℕ) : Measure (LatticeGeometry.Point d → ℝ) :=
  Measure.infinitePi (fun _ : LatticeGeometry.Point d => uniformLaw)

instance noiseLaw_isProbabilityMeasure (d : ℕ) : IsProbabilityMeasure (noiseLaw d) := by
  unfold noiseLaw
  infer_instance

/-- The exact joint law specified before (3.2): the Gaussian environment and
independent uniform auxiliary variables. -/
def jointLaw (d : ℕ) (σ : ℝ) :
    Measure ((LatticeGeometry.Point d → ℝ) × (LatticeGeometry.Point d → ℝ)) :=
  (RFIM.environmentLaw d σ).prod (noiseLaw d)

instance jointLaw_isProbabilityMeasure (d : ℕ) (σ : ℝ) :
    IsProbabilityMeasure (jointLaw d σ) := by
  unfold jointLaw RFIM.environmentLaw
  infer_instance

/-- The actual auxiliary site marks (3.2), with both weak fields and uniform
failures included. -/
def siteOpen {d : ℕ} (K ρ : ℝ) (h u : LatticeGeometry.Point d → ℝ)
    (x : LatticeGeometry.Point d) : Prop := |h x| ≤ K ∨ 1 - ρ < u x

theorem measurableSet_siteOpen {d : ℕ} (K ρ : ℝ) (x : LatticeGeometry.Point d) :
    MeasurableSet {a : (LatticeGeometry.Point d → ℝ) ×
      (LatticeGeometry.Point d → ℝ) | siteOpen K ρ a.1 a.2 x} := by
  apply MeasurableSet.union
  · exact measurableSet_le ((measurable_pi_apply x).comp measurable_fst).abs measurable_const
  · exact measurableSet_lt measurable_const ((measurable_pi_apply x).comp measurable_snd)

/-- The true conditional cluster probability, averaging only over uniforms
at a fixed, arbitrary infinite field. -/
def quenchedCluster {d : ℕ} (K ρ : ℝ) (h : LatticeGeometry.Point d → ℝ)
    (z : LatticeGeometry.Point d) (r : ℕ) : ℝ :=
  (noiseLaw d).real {u | clusterAtLeast (nnGraph d) (siteOpen K ρ h u) z r}

theorem measurableSet_joint_cluster {d : ℕ} (K ρ : ℝ)
    (z : LatticeGeometry.Point d) (r : ℕ) (hr : 0 < r) :
    MeasurableSet {a : (LatticeGeometry.Point d → ℝ) ×
      (LatticeGeometry.Point d → ℝ) |
      clusterAtLeast (nnGraph d) (siteOpen K ρ a.1 a.2) z r} := by
  exact measurableSet_clusterAtLeast (nnGraph d)
    (fun a : (LatticeGeometry.Point d → ℝ) × (LatticeGeometry.Point d → ℝ) =>
      siteOpen K ρ a.1 a.2) (measurableSet_siteOpen K ρ) z r hr

/-- Conditional probabilities are measurable functions of the disorder. -/
theorem measurable_quenchedCluster {d : ℕ} (K ρ : ℝ)
    (z : LatticeGeometry.Point d) (r : ℕ) (hr : 0 < r) :
    Measurable (fun h => quenchedCluster K ρ h z r) := by
  exact ENNReal.measurable_toReal.comp
    (measurable_measure_prodMk_left (ν := noiseLaw d)
      (measurableSet_joint_cluster K ρ z r hr))

/-- Coarse sites are indexed by `Z^d`; this is their actual physical center. -/
def coarseCenter {d : ℕ} (R : ℕ) (v : LatticeGeometry.Point d) :
    LatticeGeometry.Point d := fun j => (R : ℤ) * v j

/-- Good labels exactly as in (3.3), for an explicitly supplied initial radius.
In the paper this is instantiated with `r0 = ceil ((log R)^2)` and `s=R/8`. -/
def goodLabel {d : ℕ} (K ρ : ℝ) (R r0 s : ℕ)
    (h : LatticeGeometry.Point d → ℝ) (v : LatticeGeometry.Point d) : Prop :=
  ∀ z ∈ latticeCube (coarseCenter R v) R, ∀ r : ℕ, r0 ≤ r → r ≤ s →
    quenchedCluster K ρ h z r ≤ Real.exp (-(r : ℝ))

/-- The precise initial radius in the paper. -/
def initialRadius (R : ℕ) : ℕ := Nat.ceil ((Real.log (R : ℝ)) ^ 2)

/-- Cubes used by any test in a good label fit inside its `2R` field cube. -/
theorem label_test_cube_subset {d : ℕ} {v z : LatticeGeometry.Point d}
    {R r s : ℕ} (hz : z ∈ latticeCube (coarseCenter R v) R)
    (hrs : r ≤ s) (hsR : s ≤ R) :
    latticeCube z (r - 1) ⊆ latticeCube (coarseCenter R v) (2 * R) := by
  intro x hx
  apply mem_latticeCube.mpr
  intro j
  have hzj := mem_latticeCube.mp hz j
  have hxj := mem_latticeCube.mp hx j
  push_cast
  omega

/-- Averaging over the uniforms does not destroy the exact finite field
locality of the cluster event. -/
theorem quenchedCluster_eq_of_field_eq {d : ℕ} {K ρ : ℝ}
    {h h' : LatticeGeometry.Point d → ℝ} {z : LatticeGeometry.Point d} {r : ℕ}
    (hr : 0 < r) (heq : ∀ x ∈ latticeCube z (r - 1), h x = h' x) :
    quenchedCluster K ρ h z r = quenchedCluster K ρ h' z r := by
  unfold quenchedCluster
  congr 1
  ext u
  exact clusterAtLeast_cube_local hr (fun x hx => by simp [siteOpen, heq x hx])

/-- Exact `Q_(2R)` dependence of the quenched labels used in Lemma 3.2. -/
theorem goodLabel_field_local {d : ℕ} {K ρ : ℝ} {R r0 s : ℕ}
    {h h' : LatticeGeometry.Point d → ℝ} {v : LatticeGeometry.Point d}
    (hr0 : 0 < r0) (hsR : s ≤ R)
    (heq : ∀ x ∈ latticeCube (coarseCenter R v) (2 * R), h x = h' x) :
    goodLabel K ρ R r0 s h v ↔ goodLabel K ρ R r0 s h' v := by
  have hprob : ∀ z ∈ latticeCube (coarseCenter R v) R, ∀ r,
      r0 ≤ r → r ≤ s → quenchedCluster K ρ h z r = quenchedCluster K ρ h' z r := by
    intro z hz r hr hrs
    apply quenchedCluster_eq_of_field_eq (by omega)
    intro x hx
    exact heq x (label_test_cube_subset hz hrs hsR hx)
  unfold goodLabel
  constructor
  · intro hg z hz r hr hrs
    rw [← hprob z hz r hr hrs]
    exact hg z hz r hr hrs
  · intro hg z hz r hr hrs
    rw [hprob z hz r hr hrs]
    exact hg z hz r hr hrs

/-- Actual good-label measurability follows from finite location/radius tests. -/
theorem measurableSet_goodLabel {d : ℕ} (K ρ : ℝ) (R r0 s : ℕ)
    (v : LatticeGeometry.Point d) (hr0 : 0 < r0) :
    MeasurableSet {h | goodLabel K ρ R r0 s h v} := by
  have heq : {h | goodLabel K ρ R r0 s h v} =
      ⋂ z ∈ latticeCube (coarseCenter R v) R, ⋂ r ∈ Finset.Icc r0 s,
        {h | quenchedCluster K ρ h z r ≤ Real.exp (-(r : ℝ))} := by
    ext h
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_Icc, goodLabel]
    constructor
    · intro hg z hz r hr
      exact hg z hz r hr.1 hr.2
    · intro hg z hz r hr hrs
      exact hg z hz r ⟨hr, hrs⟩
  rw [heq]
  apply Finset.measurableSet_biInter
  intro z hz
  apply Finset.measurableSet_biInter
  intro r hr
  exact measurableSet_le (measurable_quenchedCluster K ρ z r
    (by have := (Finset.mem_Icc.mp hr).1; omega)) measurable_const

/-- Extend a finite field by zero; locality will make the outside choice irrelevant. -/
def extendField {d : ℕ} (A : Finset (LatticeGeometry.Point d))
    (ξ : ↥A → ℝ) : LatticeGeometry.Point d → ℝ :=
  fun x => if hx : x ∈ A then ξ ⟨x, hx⟩ else 0

theorem measurable_extendField {d : ℕ} (A : Finset (LatticeGeometry.Point d)) :
    Measurable (extendField A) := by
  apply measurable_pi_lambda
  intro x
  by_cases hx : x ∈ A
  · simpa [extendField, hx] using (measurable_pi_apply (⟨x, hx⟩ : ↥A))
  · simp only [extendField, dif_neg hx]
    exact measurable_const

/-- A good label as a measurable event of its finite field support. -/
def localGoodLabel {d : ℕ} (K ρ : ℝ) (R r0 s : ℕ) (v : LatticeGeometry.Point d) :
    Set (↥(latticeCube (coarseCenter R v) (2 * R)) → ℝ) :=
  {ξ | goodLabel K ρ R r0 s
    (extendField (latticeCube (coarseCenter R v) (2 * R)) ξ) v}

theorem measurableSet_localGoodLabel {d : ℕ} (K ρ : ℝ) (R r0 s : ℕ)
    (v : LatticeGeometry.Point d) (hr0 : 0 < r0) :
    MeasurableSet (localGoodLabel K ρ R r0 s v) :=
  (measurableSet_goodLabel K ρ R r0 s v hr0).preimage (measurable_extendField _)

/-- The actual quenched label factors exactly through its finite support map. -/
theorem goodLabel_iff_localGoodLabel {d : ℕ} (K ρ : ℝ) (R r0 s : ℕ)
    (v : LatticeGeometry.Point d) (hr0 : 0 < r0) (hsR : s ≤ R)
    (h : LatticeGeometry.Point d → ℝ) :
    goodLabel K ρ R r0 s h v ↔
      (latticeCube (coarseCenter R v) (2 * R)).restrict h ∈
        localGoodLabel K ρ R r0 s v := by
  apply goodLabel_field_local hr0 hsR
  intro x hx
  simp [extendField, hx, Finset.restrict]

/-- The `5^d` coordinate residue classes from Lemma 3.2. -/
def residue5 {d : ℕ} (v : LatticeGeometry.Point d) : Fin d → Fin 5 :=
  fun j => ⟨(v j % 5).toNat, by omega⟩

theorem residue5_eq_mod {d : ℕ} {v w : LatticeGeometry.Point d}
    (heq : residue5 v = residue5 w) (j : Fin d) : v j % 5 = w j % 5 := by
  have h := congrArg (fun f : Fin d → Fin 5 => (f j).val) heq
  dsimp [residue5] at h
  omega

/-- Distinct same-color coarse centers have disjoint complete field supports.
This proves the geometry behind actual label independence. -/
theorem residue5_cubes_disjoint {d : ℕ} (R : ℕ) (hR : 0 < R)
    {v w : LatticeGeometry.Point d} (hne : v ≠ w) (hc : residue5 v = residue5 w) :
    Disjoint (latticeCube (coarseCenter R v) (2 * R) : Set (LatticeGeometry.Point d))
      (latticeCube (coarseCenter R w) (2 * R) : Set (LatticeGeometry.Point d)) := by
  apply Set.disjoint_left.mpr
  intro x hxv hxw
  apply hne
  funext j
  have hv := mem_latticeCube.mp hxv j
  have hw := mem_latticeCube.mp hxw j
  have hmod := residue5_eq_mod hc j
  have hR' : (0 : ℤ) < R := by exact_mod_cast hR
  have hup : (R : ℤ) * (v j - w j) ≤ R * 4 := by
    dsimp [coarseCenter] at hv hw
    push_cast at hv hw
    nlinarith
  have hlo : (R : ℤ) * (w j - v j) ≤ R * 4 := by
    dsimp [coarseCenter] at hv hw
    push_cast at hv hw
    nlinarith
  have hdiff1 := (mul_le_mul_left hR').mp hup
  have hdiff2 := (mul_le_mul_left hR').mp hlo
  omega

/-- Marginal probability of a bad coarse label under the actual infinite
Gaussian environment equals its finite-support Gaussian probability. -/
theorem badLabel_probability_finite {d : ℕ} (σ K ρ : ℝ) (R r0 s : ℕ)
    (v : LatticeGeometry.Point d) (hr0 : 0 < r0) (hsR : s ≤ R) :
    RFIM.environmentLaw d σ {h | ¬goodLabel K ρ R r0 s h v} =
      (Measure.pi (fun _ : ↥(latticeCube (coarseCenter R v) (2 * R)) => Gaussian.law σ))
        (localGoodLabel K ρ R r0 s v)ᶜ := by
  let A := latticeCube (coarseCenter R v) (2 * R)
  have hmap := ProductCoordinates.infinitePi_map_injective
    (fun _ : LatticeGeometry.Point d => Gaussian.law σ)
    (fun x : ↥A => x.val) Subtype.val_injective
  have hset : {h | ¬goodLabel K ρ R r0 s h v} =
      (fun h (x : ↥A) => h x.val) ⁻¹' (localGoodLabel K ρ R r0 s v)ᶜ := by
    ext h
    exact not_congr (goodLabel_iff_localGoodLabel K ρ R r0 s v hr0 hsR h)
  rw [hset, ← Measure.map_apply (by fun_prop)
    (measurableSet_localGoodLabel K ρ R r0 s v hr0).compl]
  exact congrArg (fun μ => μ (localGoodLabel K ρ R r0 s v)ᶜ) hmap

/-- The same-color quenched labels have an exact product probability under
the actual infinite Gaussian environment. Independence is derived from disjoint
finite field supports, rather than supplied as a hypothesis. -/
theorem sameColor_bad_probability {d : ℕ} (σ K ρ : ℝ) (R r0 s : ℕ)
    (hR : 0 < R) (hr0 : 0 < r0) (hsR : s ≤ R)
    (S : Finset (LatticeGeometry.Point d)) (c : Fin d → Fin 5)
    (hcolor : ∀ v ∈ S, residue5 v = c) :
    (RFIM.environmentLaw d σ).real {h | ∀ v ∈ S, ¬goodLabel K ρ R r0 s h v} =
      ∏ v ∈ S, (RFIM.environmentLaw d σ).real {h | ¬goodLabel K ρ R r0 s h v} := by
  classical
  let B (i : ↥S) := latticeCube (coarseCenter R i.val) (2 * R)
  let F (i : ↥S) := ↥(B i)
  let f : Sigma F → LatticeGeometry.Point d := fun p => p.2.val
  have hf : Function.Injective f := by
    rintro ⟨i, x⟩ ⟨j, y⟩ hxy
    dsimp [f] at hxy
    have hij : i = j := by
      apply Subtype.ext
      by_contra hne
      have hdis := residue5_cubes_disjoint R hR hne
        ((hcolor i.val i.property).trans (hcolor j.val j.property).symm)
      exact Set.disjoint_left.mp hdis x.property (hxy.symm ▸ y.property)
    cases hij
    have h : x = y := Subtype.ext hxy
    cases h
    rfl
  let A (i : ↥S) : Set (F i → ℝ) := (localGoodLabel K ρ R r0 s i.val)ᶜ
  have hA (i : ↥S) : MeasurableSet (A i) :=
    (measurableSet_localGoodLabel K ρ R r0 s i.val hr0).compl
  have hmap := ProductCoordinates.infinitePi_map_groups
    (fun _ : LatticeGeometry.Point d => Gaussian.law σ) f hf
  have hset : {h | ∀ v ∈ S, ¬goodLabel K ρ R r0 s h v} =
      (fun h (i : ↥S) (x : F i) => h x.val) ⁻¹' Set.univ.pi A := by
    ext h
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const]
    constructor
    · intro hh i
      exact (not_congr (goodLabel_iff_localGoodLabel K ρ R r0 s i.val hr0 hsR h)).mp
        (hh i.val i.property)
    · intro hh v hv
      exact (not_congr (goodLabel_iff_localGoodLabel K ρ R r0 s v hr0 hsR h)).mpr
        (hh ⟨v, hv⟩)
  have hprob : RFIM.environmentLaw d σ {h | ∀ v ∈ S, ¬goodLabel K ρ R r0 s h v} =
      ∏ i : ↥S, RFIM.environmentLaw d σ {h | ¬goodLabel K ρ R r0 s h i.val} := by
    rw [hset, ← Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hA)]
    change (Measure.map (fun h i x => h (f ⟨i,x⟩))
      (Measure.infinitePi (fun _ : LatticeGeometry.Point d => Gaussian.law σ)))
        (Set.univ.pi A) = _
    rw [hmap, Measure.pi_pi]
    apply Finset.prod_congr rfl
    intro i _
    exact (badLabel_probability_finite σ K ρ R r0 s i.val hr0 hsR).symm
  have hreal := congrArg ENNReal.toReal hprob
  simp only [ENNReal.toReal_prod] at hreal
  exact hreal.trans (Finset.prod_coe_sort S (fun v =>
    (RFIM.environmentLaw d σ).real {h | ¬goodLabel K ρ R r0 s h v}))

/-- Every finite set of coarse sites obeys the source `q^(ell/5^d)` bound.
The only probability input is a one-site bad-label bound under the actual
Gaussian law; joint independence is proved above from the residue geometry. -/
theorem all_bad_probability_bound {d : ℕ} (σ K ρ : ℝ) (R r0 s : ℕ)
    (hR : 0 < R) (hr0 : 0 < r0) (hsR : s ≤ R)
    (S : Finset (LatticeGeometry.Point d)) (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hmarg : ∀ v ∈ S,
      (RFIM.environmentLaw d σ).real {h | ¬goodLabel K ρ R r0 s h v} ≤ q) :
    (RFIM.environmentLaw d σ).real {h | ∀ v ∈ S, ¬goodLabel K ρ R r0 s h v} ≤
      q ^ ((S.card : ℝ) / (5 : ℝ) ^ d) := by
  classical
  let C := Fin d → Fin 5
  have hC : (Fintype.card C : ℝ) = (5 : ℝ) ^ d := by simp [C]
  obtain ⟨c, _, hc⟩ :=
    Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
      (s := S) (t := (univ : Finset C)) (f := residue5)
      (b := (S.card : ℝ) / (5 : ℝ) ^ d)
      (fun _ _ => mem_univ _) univ_nonempty (by
        simp only [card_univ, nsmul_eq_mul, hC]
        field_simp
        exact le_rfl)
  let T := S.filter (fun v => residue5 v = c)
  have hT : ∀ v ∈ T, residue5 v = c := fun v hv => (mem_filter.mp hv).2
  calc
    (RFIM.environmentLaw d σ).real {h | ∀ v ∈ S, ¬goodLabel K ρ R r0 s h v}
        ≤ (RFIM.environmentLaw d σ).real {h | ∀ v ∈ T, ¬goodLabel K ρ R r0 s h v} :=
      measureReal_mono (fun h hh v hv => hh v (mem_filter.mp hv).1)
    _ = ∏ v ∈ T, (RFIM.environmentLaw d σ).real {h | ¬goodLabel K ρ R r0 s h v} :=
      sameColor_bad_probability σ K ρ R r0 s hR hr0 hsR T c hT
    _ ≤ ∏ _v ∈ T, q := prod_le_prod (fun _ _ => ENNReal.toReal_nonneg)
      (fun v hv => hmarg v (mem_filter.mp hv).1)
    _ = q ^ T.card := prod_const q
    _ ≤ q ^ ((S.card : ℝ) / (5 : ℝ) ^ d) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge' hq hq1 (by positivity) hc

/-- A measurable Boolean version of a single actual site mark. -/
def markBool (K ρ : ℝ) (a : ℝ × ℝ) : Bool := decide (|a.1| ≤ K ∨ 1 - ρ < a.2)

theorem measurable_markBool (K ρ : ℝ) : Measurable (markBool K ρ) := by
  apply measurable_to_bool
  have hs : (markBool K ρ) ⁻¹' {true} = {a : ℝ × ℝ | |a.1| ≤ K ∨ 1 - ρ < a.2} := by
    ext a
    simp [markBool]
  rw [hs]
  exact (measurableSet_le measurable_fst.abs measurable_const).union
    (measurableSet_lt measurable_const measurable_snd)

/-- The one-site annealed mark distribution, built from the actual Gaussian
and uniform laws. -/
def oneSiteMarkLaw (σ K ρ : ℝ) : Measure Bool :=
  ((Gaussian.law σ).prod uniformLaw).map (markBool K ρ)

instance oneSiteMarkLaw_isProbabilityMeasure (σ K ρ : ℝ) :
    IsProbabilityMeasure (oneSiteMarkLaw σ K ρ) := by
  unfold oneSiteMarkLaw
  exact Measure.isProbabilityMeasure_map (measurable_markBool K ρ).aemeasurable

/-- The exact finite joint distribution of marks at distinct lattice sites. -/
theorem joint_marks_finite {d : ℕ} {I : Type*} [Fintype I]
    (σ K ρ : ℝ) (f : I → LatticeGeometry.Point d) (hf : Function.Injective f) :
    (jointLaw d σ).map (fun a i => markBool K ρ (a.1 (f i), a.2 (f i))) =
      Measure.pi (fun _ : I => oneSiteMarkLaw σ K ρ) := by
  have hpair := ProductCoordinates.product_infinitePi_map_pairs
    (fun _ : LatticeGeometry.Point d => Gaussian.law σ)
    (fun _ : LatticeGeometry.Point d => uniformLaw) f hf
  have hmark := Measure.pi_map_pi (μ := fun _ : I => (Gaussian.law σ).prod uniformLaw)
    (f := fun _ => markBool K ρ) (fun _ => (measurable_markBool K ρ).aemeasurable)
  have hh : Measurable (fun x : I → ℝ × ℝ => fun i => markBool K ρ (x i)) := by
    apply measurable_pi_lambda
    intro i
    exact (measurable_markBool K ρ).comp (measurable_pi_apply i)
  rw [← hpair, Measure.map_map hh (by fun_prop)] at hmark
  exact hmark

/-- The complete Boolean mark field is an iid site field under the exact
Gaussian-environment / independent-uniform joint law. -/
theorem joint_marks_iid {d : ℕ} (σ K ρ : ℝ) :
    (jointLaw d σ).map (fun a x => markBool K ρ (a.1 x, a.2 x)) =
      Measure.infinitePi (fun _ : LatticeGeometry.Point d => oneSiteMarkLaw σ K ρ) := by
  apply Measure.eq_infinitePi
  intro S t ht
  have hm : Measurable (fun a : (LatticeGeometry.Point d → ℝ) ×
      (LatticeGeometry.Point d → ℝ) => fun x => markBool K ρ (a.1 x, a.2 x)) := by
    apply measurable_pi_lambda
    intro x
    exact (measurable_markBool K ρ).comp
      (((measurable_pi_apply x).comp measurable_fst).prodMk
        ((measurable_pi_apply x).comp measurable_snd))
  rw [Measure.map_apply hm ((measurableSet_pi S.countable_toSet).mpr (Or.inl ht))]
  have hpre : (fun a : (LatticeGeometry.Point d → ℝ) × (LatticeGeometry.Point d → ℝ) =>
      fun x => markBool K ρ (a.1 x, a.2 x)) ⁻¹' Set.pi (S : Set _) t =
      (fun a : (LatticeGeometry.Point d → ℝ) × (LatticeGeometry.Point d → ℝ) =>
        fun (x : ↥S) => markBool K ρ (a.1 x.val, a.2 x.val)) ⁻¹'
        Set.univ.pi (fun x : ↥S => t x.val) := by
    ext a
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const]
    exact ⟨fun h x => h x.val x.property, fun h x hx => h ⟨x, hx⟩⟩
  rw [hpre, ← Measure.map_apply (by
      apply measurable_pi_lambda
      intro x
      exact (measurable_markBool K ρ).comp
        (((measurable_pi_apply x.val).comp measurable_fst).prodMk
          ((measurable_pi_apply x.val).comp measurable_snd)))
    (MeasurableSet.univ_pi (fun x : ↥S => ht x.val x.property)),
    joint_marks_finite σ K ρ Subtype.val Subtype.val_injective, Measure.pi_pi]
  exact Finset.prod_coe_sort S (fun x => oneSiteMarkLaw σ K ρ (t x))

/-- The uniform failure event has exactly the specified probability. -/
theorem uniformLaw_tail (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    uniformLaw (Set.Ioi (1 - ρ)) = ENNReal.ofReal ρ := by
  rw [uniformLaw, Measure.restrict_apply measurableSet_Ioi]
  have hs : Set.Ioi (1 - ρ) ∩ Set.Icc (0 : ℝ) 1 = Set.Ioc (1 - ρ) 1 := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
    constructor
    · rintro ⟨h, _, hle⟩
      exact ⟨h, hle⟩
    · rintro ⟨h, hle⟩
      exact ⟨h, by linarith, hle⟩
  rw [hs, Real.volume_Ioc]
  congr 1
  ring

/-- Annealed opening parameter `pK+(1-pK)rho`, computed from the actual laws. -/
theorem oneSiteMarkLaw_true (σ K ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    (oneSiteMarkLaw σ K ρ).real {true} =
      (Gaussian.law σ).real {x | |x| ≤ K} +
        (1 - (Gaussian.law σ).real {x | |x| ≤ K}) * ρ := by
  let W : Set ℝ := {x | |x| ≤ K}
  have hW : MeasurableSet W := measurableSet_le measurable_abs measurable_const
  have hpre : (markBool K ρ) ⁻¹' {true} =
      (W ×ˢ Set.univ) ∪ (Wᶜ ×ˢ Set.Ioi (1 - ρ)) := by
    ext a
    simp only [Set.mem_preimage, Set.mem_singleton_iff, markBool, decide_eq_true_eq,
      Set.mem_union, Set.mem_prod, Set.mem_univ, and_true, Set.mem_compl_iff, Set.mem_Ioi, W]
    tauto
  have hdis : Disjoint (W ×ˢ (Set.univ : Set ℝ)) (Wᶜ ×ˢ Set.Ioi (1 - ρ)) := by
    exact Set.disjoint_left.mpr (fun _ h₁ h₂ => h₂.1 h₁.1)
  unfold Measure.real oneSiteMarkLaw
  rw [Measure.map_apply (measurable_markBool K ρ) (MeasurableSet.singleton true), hpre,
    measure_union hdis (hW.compl.prod measurableSet_Ioi), Measure.prod_prod,
    Measure.prod_prod, measure_univ, mul_one, uniformLaw_tail ρ hρ hρ1,
    ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hρ]
  rw [← measureReal_def, ← measureReal_def, measureReal_compl hW]
  simp

/-- Fubini's identity for the actual quenched cluster probability. -/
theorem quenchedCluster_average {d : ℕ} (σ K ρ : ℝ)
    (z : LatticeGeometry.Point d) (r : ℕ) (hr : 0 < r) :
    (∫ h, quenchedCluster K ρ h z r ∂RFIM.environmentLaw d σ) =
      (jointLaw d σ).real {a | clusterAtLeast (nnGraph d) (siteOpen K ρ a.1 a.2) z r} := by
  have hs := measurableSet_joint_cluster K ρ z r hr
  unfold quenchedCluster Measure.real jointLaw
  rw [Measure.prod_apply hs]
  exact integral_toReal (measurable_measure_prodMk_left hs).aemeasurable
    (Filter.Eventually.of_forall (fun h => measure_lt_top (noiseLaw d) _))

/-- Markov's step in (3.4), applied to the actual quenched probability. -/
theorem quenchedCluster_bad_probability {d : ℕ} (σ K ρ : ℝ)
    (z : LatticeGeometry.Point d) (r : ℕ) (hr : 0 < r) :
    (RFIM.environmentLaw d σ).real {h | Real.exp (-(r : ℝ)) < quenchedCluster K ρ h z r} ≤
      Real.exp (r : ℝ) * (jointLaw d σ).real
        {a | clusterAtLeast (nnGraph d) (siteOpen K ρ a.1 a.2) z r} := by
  have hi : Integrable (fun h => quenchedCluster K ρ h z r) (RFIM.environmentLaw d σ) :=
    Measure.integrable_measure_prodMk_left (measurableSet_joint_cluster K ρ z r hr)
      (by finiteness)
  have hm := mul_meas_ge_le_integral_of_nonneg
    (μ := RFIM.environmentLaw d σ)
    (f := fun h => quenchedCluster K ρ h z r)
    (Filter.Eventually.of_forall (fun _ => ENNReal.toReal_nonneg)) hi (Real.exp (-(r : ℝ)))
  rw [quenchedCluster_average σ K ρ z r hr] at hm
  have hsub : (RFIM.environmentLaw d σ).real
      {h | Real.exp (-(r : ℝ)) < quenchedCluster K ρ h z r} ≤
      (RFIM.environmentLaw d σ).real
      {h | Real.exp (-(r : ℝ)) ≤ quenchedCluster K ρ h z r} :=
    measureReal_mono (by
      intro h hh
      change Real.exp (-(r : ℝ)) < quenchedCluster K ρ h z r at hh
      exact hh.le)
  have hp := mul_le_mul_of_nonneg_left hsub (Real.exp_nonneg (-(r : ℝ)))
  have hdiv : (RFIM.environmentLaw d σ).real
      {h | Real.exp (-(r : ℝ)) < quenchedCluster K ρ h z r} ≤
      (jointLaw d σ).real {a | clusterAtLeast (nnGraph d) (siteOpen K ρ a.1 a.2) z r} /
        Real.exp (-(r : ℝ)) :=
    (le_div_iff₀ (Real.exp_pos (-(r : ℝ)))).mpr (by
    simpa only [mul_comm] using hp.trans hm)
  simpa only [Real.exp_neg, div_inv_eq_mul, mul_comm] using hdiv

/-- The real-valued Bernoulli opening parameter of the actual annealed marks. -/
def markParameter (σ K ρ : ℝ) : ℝ := (oneSiteMarkLaw σ K ρ).real {true}

theorem markParameter_nonneg (σ K ρ : ℝ) : 0 ≤ markParameter σ K ρ :=
  ENNReal.toReal_nonneg

theorem markParameter_le_one (σ K ρ : ℝ) : markParameter σ K ρ ≤ 1 := by
  unfold markParameter
  calc
    (oneSiteMarkLaw σ K ρ).real {true} ≤ (oneSiteMarkLaw σ K ρ).real Set.univ :=
      measureReal_mono (Set.subset_univ _)
    _ = 1 := measureReal_univ_eq_one

/-- Exact finite all-open probabilities of the actual Gaussian/uniform marks.
This supplies the independence-derived input for the sharp cluster enumeration. -/
theorem joint_all_open_probability {d : ℕ} (σ K ρ : ℝ)
    (S : Finset (LatticeGeometry.Point d)) :
    (jointLaw d σ).real {a | ∀ x ∈ S, siteOpen K ρ a.1 a.2 x} =
      markParameter σ K ρ ^ S.card := by
  classical
  have hpre : {a : (LatticeGeometry.Point d → ℝ) × (LatticeGeometry.Point d → ℝ) |
      ∀ x ∈ S, siteOpen K ρ a.1 a.2 x} =
      (fun a : (LatticeGeometry.Point d → ℝ) × (LatticeGeometry.Point d → ℝ) =>
        fun x : ↥S => markBool K ρ (a.1 x.val, a.2 x.val)) ⁻¹'
          Set.univ.pi (fun _ : ↥S => ({true} : Set Bool)) := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
      forall_const, Set.mem_singleton_iff, markBool, decide_eq_true_eq, siteOpen]
    exact ⟨fun h x => h x.val x.property, fun h x hx => h ⟨x, hx⟩⟩
  unfold Measure.real
  rw [hpre, ← Measure.map_apply (by
      apply measurable_pi_lambda
      intro x
      exact (measurable_markBool K ρ).comp
        (((measurable_pi_apply x.val).comp measurable_fst).prodMk
          ((measurable_pi_apply x.val).comp measurable_snd)))
    (MeasurableSet.univ_pi (fun _ => MeasurableSet.singleton true)),
    joint_marks_finite σ K ρ Subtype.val Subtype.val_injective, Measure.pi_pi,
    ENNReal.toReal_prod]
  simp only [markParameter, measureReal_def, prod_const, card_univ, Fintype.card_coe]

end Paper09.Percolation
