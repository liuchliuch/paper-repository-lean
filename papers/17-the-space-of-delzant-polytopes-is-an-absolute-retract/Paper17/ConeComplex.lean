import Paper17.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Algebra.BigOperators.Option

/-!
# Finite simplicial cone complexes on shared rays

The intersection axiom is equality of actual positive spans. It is the
geometric fan condition, not an assumed resolution or refinement certificate.
Shared global ray indices make simultaneous stellar subdivisions compatible
across distinct original maximal cones.
-/
noncomputable section
open scoped BigOperators
namespace Paper17
section
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
variable [AddCommGroup E] [Module ℝ E]

/-- Actual positive span of a finite collection of globally indexed rays. -/
def raySpan (v : ι → E) (s : Finset ι) : Set E :=
  {x | ∃ c : ι → ℝ, (∀ i, 0 ≤ c i) ∧ (∀ i, i ∉ s → c i = 0) ∧
    x = ∑ i, c i • v i}

theorem raySpan_zero (v : ι → E) (s : Finset ι) : (0 : E) ∈ raySpan v s := by
  exact ⟨0, by simp, by simp, by simp⟩

theorem raySpan_mono (v : ι → E) {s t : Finset ι} (hst : s ⊆ t) :
    raySpan v s ⊆ raySpan v t := by
  rintro x ⟨c, hc, hs, hx⟩
  exact ⟨c, hc, fun i hi => hs i (fun his => hi (hst his)), hx⟩

theorem sum_supported_eq_subtype (v : ι → E) (s : Finset ι) (c : ι → ℝ)
    (hc : ∀ i, i ∉ s → c i = 0) :
    ∑ i, c i • v i = ∑ i : ↑s, c i.val • v i.val := by
  calc (∑ i, c i • v i) = ∑ i ∈ s, c i • v i :=
        (Finset.sum_subset (Finset.subset_univ s) (fun i _ hi => by rw [hc i hi]; simp)).symm
    _ = ∑ i : ↑s, c i.val • v i.val := (Finset.sum_coe_sort s (fun i => c i • v i)).symm

/-- Unique coordinates on a linearly independent cone, expressed in the
shared ambient index set by extending coefficients by zero. -/
theorem supported_coefficients_unique (v : ι → E) (s : Finset ι)
    (h : LinearIndependent ℝ (fun i : ↑s => v i.val))
    {c d : ι → ℝ} (hc : ∀ i, i ∉ s → c i = 0) (hd : ∀ i, i ∉ s → d i = 0)
    (heq : ∑ i, c i • v i = ∑ i, d i • v i) : c = d := by
  have hsub : (fun i : ↑s => c i.val) = (fun i : ↑s => d i.val) := by
    apply h.fintypeLinearCombination_injective
    change (∑ i : ↑s, c i.val • v i.val) = ∑ i : ↑s, d i.val • v i.val
    rwa [← sum_supported_eq_subtype v s c hc, ← sum_supported_eq_subtype v s d hd]
  funext i
  by_cases hi : i ∈ s
  · exact congrFun hsub ⟨i, hi⟩
  · rw [hc i hi, hd i hi]

/-- A finite maximal-cone presentation of a geometric simplicial cone complex. -/
structure SimplicialConeComplex (v : ι → E) where
  facets : Finset (Finset ι)
  independent : ∀ s ∈ facets, LinearIndependent ℝ (fun i : ↑s => v i.val)
  intersection : ∀ s ∈ facets, ∀ t ∈ facets,
    raySpan v s ∩ raySpan v t = raySpan v (s ∩ t)

/-- Positive coordinates in two cones of a genuine complex agree globally.
This is the compatibility fact needed for a simultaneous subdivision. -/
theorem SimplicialConeComplex.positive_coordinates_unique {v : ι → E}
    (K : SimplicialConeComplex v) {s t : Finset ι} (hs : s ∈ K.facets) (ht : t ∈ K.facets)
    {c d : ι → ℝ} (hc0 : ∀ i, 0 ≤ c i) (hd0 : ∀ i, 0 ≤ d i)
    (hc : ∀ i, i ∉ s → c i = 0) (hd : ∀ i, i ∉ t → d i = 0)
    (heq : ∑ i, c i • v i = ∑ i, d i • v i) : c = d := by
  have hx : (∑ i, c i • v i) ∈ raySpan v s ∩ raySpan v t :=
    ⟨⟨c, hc0, hc, rfl⟩, ⟨d, hd0, hd, heq⟩⟩
  rw [K.intersection s hs t ht] at hx
  obtain ⟨a, ha0, ha, hxa⟩ := hx
  have has : ∀ i, i ∉ s → a i = 0 := fun i hi =>
    ha i (fun him => hi (Finset.mem_inter.mp him).1)
  have hat : ∀ i, i ∉ t → a i = 0 := fun i hi =>
    ha i (fun him => hi (Finset.mem_inter.mp him).2)
  have hca := supported_coefficients_unique v s (K.independent s hs) hc has hxa
  have hda := supported_coefficients_unique v t (K.independent t ht) hd hat (heq.symm.trans hxa)
  exact hca.trans hda.symm

/-- The ray family after adjoining one new ray with a fresh index. -/
def starRays (v : ι → E) (w : E) : Option ι → E
  | none => w
  | some i => v i

/-- The new maximal simplex replaces one vertex by the new ray. -/
def starFacet (s : Finset ι) (k : ι) : Finset (Option ι) :=
  insert none ((s.erase k).image some)

@[simp] theorem mem_starFacet_none (s : Finset ι) (k : ι) :
    none ∈ starFacet s k := Finset.mem_insert_self _ _

@[simp] theorem mem_starFacet_some (s : Finset ι) (k i : ι) :
    some i ∈ starFacet s k ↔ i ∈ s ∧ i ≠ k := by
  simp [starFacet, and_comm]

/-- Expanding the new-ray coefficient in the original global rays. -/
def expandStarCoefficients (b : ι → ℝ) (c : Option ι → ℝ) : ι → ℝ :=
  fun i => c (some i) + c none * b i

theorem star_synthesis_eq (v : ι → E) (w : E) (b : ι → ℝ)
    (hw : w = ∑ i, b i • v i) (c : Option ι → ℝ) :
    ∑ i, c i • starRays v w i = ∑ i, expandStarCoefficients b c i • v i := by
  rw [Fintype.sum_option]
  simp only [starRays, hw, Finset.smul_sum, smul_smul, expandStarCoefficients,
    add_smul, Finset.sum_add_distrib]
  exact add_comm _ _

/-- Positive stellar coefficients remain positive after expansion. -/
theorem expandStarCoefficients_nonneg (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i)
    (c : Option ι → ℝ) (hc : ∀ i, 0 ≤ c i) :
    ∀ i, 0 ≤ expandStarCoefficients b c i :=
  fun i => add_nonneg (hc _) (mul_nonneg (hc none) (hb i))

/-- A coefficient supported on a new facet expands inside its original facet. -/
theorem expandStarCoefficients_supported {s I : Finset ι} {k : ι} (hIs : I ⊆ s)
    (b : ι → ℝ) (hb : ∀ i, i ∉ I → b i = 0)
    (c : Option ι → ℝ) (hc : ∀ i, i ∉ starFacet s k → c i = 0) :
    ∀ i, i ∉ s → expandStarCoefficients b c i = 0 := by
  intro i hi
  have hc' : c (some i) = 0 := hc _ (by simp [hi])
  have hb' : b i = 0 := hb i (fun h => hi (hIs h))
  simp [expandStarCoefficients, hc', hb']

/-- An unaffected facet is kept; an affected facet omits one generator from
its chosen face and adjoins the new global ray. -/
def starCellGenerators (s : Finset ι) : Option ι → Finset (Option ι)
  | none => s.image some
  | some k => starFacet s k

def starCellValid (I s : Finset ι) : Option ι → Prop
  | none => ¬ I ⊆ s
  | some k => I ⊆ s ∧ k ∈ I

theorem starCell_expansion_supported {I s : Finset ι} {q : Option ι}
    (hvalid : starCellValid I s q)
    (b : ι → ℝ) (hb : ∀ i, i ∉ I → b i = 0)
    (c : Option ι → ℝ)
    (hc : ∀ i, i ∉ starCellGenerators s q → c i = 0) :
    ∀ i, i ∉ s → expandStarCoefficients b c i = 0 := by
  cases q with
  | none =>
    have hc0 : c none = 0 := hc none (by simp [starCellGenerators])
    intro i hi
    have hci : c (some i) = 0 := hc _ (by simp [starCellGenerators, hi])
    simp [expandStarCoefficients, hc0, hci]
  | some k =>
    exact expandStarCoefficients_supported hvalid.1 b hb c hc

/-- Original shared-ray coordinates force the new-ray coordinates to agree
also across distinct original cones in a simultaneous stellar subdivision. -/
theorem SimplicialConeComplex.star_positive_coordinates_unique {v : ι → E}
    (K : SimplicialConeComplex v) (I : Finset ι) (w : E) (b : ι → ℝ)
    (hb0 : ∀ i, 0 ≤ b i) (hbs : ∀ i, i ∉ I → b i = 0)
    (hbp : ∀ i ∈ I, 0 < b i) (hw : w = ∑ i, b i • v i)
    {s t : Finset ι} (hs : s ∈ K.facets) (ht : t ∈ K.facets)
    {q r : Option ι} (hq : starCellValid I s q) (hr : starCellValid I t r)
    {c d : Option ι → ℝ} (hc0 : ∀ i, 0 ≤ c i) (hd0 : ∀ i, 0 ≤ d i)
    (hc : ∀ i, i ∉ starCellGenerators s q → c i = 0)
    (hd : ∀ i, i ∉ starCellGenerators t r → d i = 0)
    (heq : ∑ i, c i • starRays v w i = ∑ i, d i • starRays v w i) : c = d := by
  have he : expandStarCoefficients b c = expandStarCoefficients b d := by
    apply K.positive_coordinates_unique hs ht
      (expandStarCoefficients_nonneg b hb0 c hc0)
      (expandStarCoefficients_nonneg b hb0 d hd0)
      (starCell_expansion_supported hq b hbs c hc)
      (starCell_expansion_supported hr b hbs d hd)
    rwa [← star_synthesis_eq v w b hw c, ← star_synthesis_eq v w b hw d]
  have hnone : c none = d none := by
    cases q with
    | none =>
      have hcn : c none = 0 := hc none (by simp [starCellGenerators])
      cases r with
      | none =>
        have hdn : d none = 0 := hd none (by simp [starCellGenerators])
        rw [hcn, hdn]
      | some l =>
        obtain ⟨i, hiI, his⟩ := Finset.not_subset.mp hq
        have hci : c (some i) = 0 := hc _ (by simp [starCellGenerators, his])
        have heq' := congrFun he i
        dsimp [expandStarCoefficients] at heq'
        rw [hcn, hci] at heq'
        have hm : d none * b i = 0 := by nlinarith [hd0 (some i), mul_nonneg (hd0 none) (hb0 i)]
        have hdn : d none = 0 := (mul_eq_zero.mp hm).resolve_right (hbp i hiI).ne'
        rw [hcn, hdn]
    | some k =>
      cases r with
      | none =>
        have hdn : d none = 0 := hd none (by simp [starCellGenerators])
        obtain ⟨i, hiI, hit⟩ := Finset.not_subset.mp hr
        have hdi : d (some i) = 0 := hd _ (by simp [starCellGenerators, hit])
        have heq' := congrFun he i
        dsimp [expandStarCoefficients] at heq'
        rw [hdn, hdi] at heq'
        have hm : c none * b i = 0 := by nlinarith [hc0 (some i), mul_nonneg (hc0 none) (hb0 i)]
        have hcn : c none = 0 := (mul_eq_zero.mp hm).resolve_right (hbp i hiI).ne'
        rw [hcn, hdn]
      | some l =>
        have hck : c (some k) = 0 := hc _ (by simp [starCellGenerators])
        have hdl : d (some l) = 0 := hd _ (by simp [starCellGenerators])
        have hek := congrFun he k
        have hel := congrFun he l
        dsimp [expandStarCoefficients] at hek hel
        rw [hck] at hek
        rw [hdl] at hel
        apply le_antisymm
        · apply (mul_le_mul_right (hbp l hr.2)).mp
          linarith [hc0 (some l)]
        · apply (mul_le_mul_right (hbp k hq.2)).mp
          linarith [hd0 (some k)]
  funext i
  cases i with
  | none => exact hnone
  | some i =>
    have heq' := congrFun he i
    dsimp [expandStarCoefficients] at heq'
    rw [hnone] at heq'
    exact add_right_cancel heq'

/-- Simultaneous stellar pieces from any two original cones meet in precisely
the positive span of their common new rays. -/
theorem SimplicialConeComplex.star_intersection {v : ι → E}
    (K : SimplicialConeComplex v) (I : Finset ι) (w : E) (b : ι → ℝ)
    (hb0 : ∀ i, 0 ≤ b i) (hbs : ∀ i, i ∉ I → b i = 0)
    (hbp : ∀ i ∈ I, 0 < b i) (hw : w = ∑ i, b i • v i)
    {s t : Finset ι} (hs : s ∈ K.facets) (ht : t ∈ K.facets)
    {q r : Option ι} (hq : starCellValid I s q) (hr : starCellValid I t r) :
    raySpan (starRays v w) (starCellGenerators s q) ∩
      raySpan (starRays v w) (starCellGenerators t r) =
    raySpan (starRays v w) (starCellGenerators s q ∩ starCellGenerators t r) := by
  apply Set.Subset.antisymm
  · rintro x ⟨⟨c, hc0, hc, hxc⟩, ⟨d, hd0, hd, hxd⟩⟩
    have hcd := K.star_positive_coordinates_unique I w b hb0 hbs hbp hw hs ht hq hr
      hc0 hd0 hc hd (hxc.symm.trans hxd)
    subst d
    refine ⟨c, hc0, ?_, hxc⟩
    intro i hi
    by_cases his : i ∈ starCellGenerators s q
    · exact hd i (fun hit => hi (Finset.mem_inter.mpr ⟨his, hit⟩))
    · exact hc i his
  · intro x hx
    exact ⟨raySpan_mono _ Finset.inter_subset_left hx,
      raySpan_mono _ Finset.inter_subset_right hx⟩

/-- Stellar replacement preserves linear independence on each original cell. -/
theorem starCell_supported_coordinates_unique (v : ι → E) (I s : Finset ι)
    (hs : LinearIndependent ℝ (fun i : ↑s => v i.val)) (w : E) (b : ι → ℝ)
    (hbs : ∀ i, i ∉ I → b i = 0) (hbp : ∀ i ∈ I, 0 < b i)
    (hw : w = ∑ i, b i • v i) {q : Option ι} (hq : starCellValid I s q)
    {c d : Option ι → ℝ}
    (hc : ∀ i, i ∉ starCellGenerators s q → c i = 0)
    (hd : ∀ i, i ∉ starCellGenerators s q → d i = 0)
    (heq : ∑ i, c i • starRays v w i = ∑ i, d i • starRays v w i) : c = d := by
  have he : expandStarCoefficients b c = expandStarCoefficients b d := by
    apply supported_coefficients_unique v s hs
      (starCell_expansion_supported hq b hbs c hc)
      (starCell_expansion_supported hq b hbs d hd)
    rwa [← star_synthesis_eq v w b hw c, ← star_synthesis_eq v w b hw d]
  have hnone : c none = d none := by
    cases q with
    | none =>
      rw [hc none (by simp [starCellGenerators]), hd none (by simp [starCellGenerators])]
    | some k =>
      have hck : c (some k) = 0 := hc _ (by simp [starCellGenerators])
      have hdk : d (some k) = 0 := hd _ (by simp [starCellGenerators])
      have hk := congrFun he k
      dsimp [expandStarCoefficients] at hk
      rw [hck, hdk, zero_add, zero_add] at hk
      exact mul_right_cancel₀ (hbp k hq.2).ne' hk
  funext i
  cases i with
  | none => exact hnone
  | some i =>
    have hi := congrFun he i
    dsimp [expandStarCoefficients] at hi
    rw [hnone] at hi
    exact add_right_cancel hi

/-- The actual new ray vectors are linearly independent on each new facet. -/
theorem starCell_independent (v : ι → E) (I s : Finset ι)
    (hs : LinearIndependent ℝ (fun i : ↑s => v i.val)) (w : E) (b : ι → ℝ)
    (hbs : ∀ i, i ∉ I → b i = 0) (hbp : ∀ i ∈ I, 0 < b i)
    (hw : w = ∑ i, b i • v i) {q : Option ι} (hq : starCellValid I s q) :
    LinearIndependent ℝ (fun i : ↑(starCellGenerators s q) => starRays v w i.val) := by
  classical
  apply linearIndependent_iff_injective_fintypeLinearCombination.mpr
  intro c d heq
  let U := starCellGenerators s q
  let C : Option ι → ℝ := fun i => if hi : i ∈ U then c ⟨i, hi⟩ else 0
  let D : Option ι → ℝ := fun i => if hi : i ∈ U then d ⟨i, hi⟩ else 0
  have hC : ∀ i, i ∉ U → C i = 0 := fun i hi => dif_neg hi
  have hD : ∀ i, i ∉ U → D i = 0 := fun i hi => dif_neg hi
  have hcombC : ∑ i, C i • starRays v w i = ∑ i : ↑U, c i • starRays v w i.val := by
    rw [sum_supported_eq_subtype _ U C hC]
    apply Finset.sum_congr rfl
    intro i _
    simp only [C, dif_pos i.property, Subtype.coe_eta]
  have hcombD : ∑ i, D i • starRays v w i = ∑ i : ↑U, d i • starRays v w i.val := by
    rw [sum_supported_eq_subtype _ U D hD]
    apply Finset.sum_congr rfl
    intro i _
    simp only [D, dif_pos i.property, Subtype.coe_eta]
  have hCD := starCell_supported_coordinates_unique v I s hs w b hbs hbp hw hq hC hD
    (hcombC.trans (heq.trans hcombD.symm))
  funext i
  have hi := congrFun hCD i.val
  simpa only [C, D, dif_pos (show i.val ∈ U from i.property), Subtype.coe_eta] using hi

/-- The finite collection of all simultaneously changed and unchanged cells. -/
def SimplicialConeComplex.starFacets {v : ι → E} (K : SimplicialConeComplex v)
    (I : Finset ι) : Finset (Finset (Option ι)) := by
  classical
  exact ((K.facets.product (Finset.univ : Finset (Option ι))).filter
    (fun p : Finset ι × Option ι => starCellValid I p.1 p.2)).image
    (fun p : Finset ι × Option ι => starCellGenerators p.1 p.2)

theorem SimplicialConeComplex.mem_starFacets {v : ι → E} (K : SimplicialConeComplex v)
    (I : Finset ι) (s : Finset (Option ι)) :
    s ∈ K.starFacets I ↔ ∃ t ∈ K.facets, ∃ q, starCellValid I t q ∧ starCellGenerators t q = s := by
  classical
  unfold SimplicialConeComplex.starFacets
  constructor
  · intro h
    obtain ⟨⟨t, q⟩, hmem, heq⟩ := Finset.mem_image.mp h
    obtain ⟨ht, hq⟩ := Finset.mem_filter.mp hmem
    exact ⟨t, (Finset.mem_product.mp ht).1, q, hq, heq⟩
  · rintro ⟨t, ht, q, hq, heq⟩
    exact Finset.mem_image.mpr ⟨(t, q),
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ht, Finset.mem_univ _⟩, hq⟩, heq⟩

/-- Simultaneous stellar subdivision gives another genuine geometric
simplicial cone complex; no global resolution property is assumed. -/
def SimplicialConeComplex.stellarSubdivision {v : ι → E} (K : SimplicialConeComplex v)
    (I : Finset ι) (w : E) (b : ι → ℝ)
    (hb0 : ∀ i, 0 ≤ b i) (hbs : ∀ i, i ∉ I → b i = 0)
    (hbp : ∀ i ∈ I, 0 < b i) (hw : w = ∑ i, b i • v i) :
    SimplicialConeComplex (starRays v w) where
  facets := K.starFacets I
  independent := by
    intro s hs
    obtain ⟨t, ht, q, hq, rfl⟩ := (K.mem_starFacets I s).mp hs
    exact starCell_independent v I t (K.independent t ht) w b hbs hbp hw hq
  intersection := by
    intro s hs t ht
    obtain ⟨s₀, hs₀, q, hq, rfl⟩ := (K.mem_starFacets I s).mp hs
    obtain ⟨t₀, ht₀, r, hr, rfl⟩ := (K.mem_starFacets I t).mp ht
    exact K.star_intersection I w b hb0 hbs hbp hw hs₀ ht₀ hq hr

/-- Every new geometric cone is contained in its actual original cone. -/
theorem starCell_refines (v : ι → E) (I s : Finset ι) (w : E) (b : ι → ℝ)
    (hb0 : ∀ i, 0 ≤ b i) (hbs : ∀ i, i ∉ I → b i = 0)
    (hw : w = ∑ i, b i • v i) {q : Option ι} (hq : starCellValid I s q) :
    raySpan (starRays v w) (starCellGenerators s q) ⊆ raySpan v s := by
  rintro x ⟨c, hc0, hc, hx⟩
  exact ⟨expandStarCoefficients b c, expandStarCoefficients_nonneg b hb0 c hc0,
    starCell_expansion_supported hq b hbs c hc, hx.trans (star_synthesis_eq v w b hw c)⟩

/-- The simultaneous star covers every old cone, including unchanged cones.
The minimum-ratio argument is performed on the shared face, not independently
chosen incompatible subdivisions. -/
theorem starCell_cover (v : ι → E) (I s : Finset ι) (hI : I.Nonempty)
    (w : E) (b : ι → ℝ) (hb0 : ∀ i, 0 ≤ b i)
    (hbs : ∀ i, i ∉ I → b i = 0) (hbp : ∀ i ∈ I, 0 < b i)
    (hw : w = ∑ i, b i • v i) :
    raySpan v s ⊆ ⋃ q : {q // starCellValid I s q},
      raySpan (starRays v w) (starCellGenerators s q.val) := by
  classical
  rintro x ⟨c, hc0, hc, hx⟩
  by_cases hIs : I ⊆ s
  · obtain ⟨k, hk, hmin⟩ := Finset.exists_min_image I (fun i => c i / b i) hI
    let a := c k / b k
    have ha : 0 ≤ a := div_nonneg (hc0 k) (hb0 k)
    have hres : ∀ i, 0 ≤ c i - a * b i := by
      intro i
      by_cases hi : i ∈ I
      · exact sub_nonneg.mpr ((le_div_iff₀ (hbp i hi)).mp (hmin i hi))
      · simp [hbs i hi, hc0 i]
    let d : Option ι → ℝ := fun i => match i with
      | none => a
      | some i => c i - a * b i
    apply Set.mem_iUnion.mpr
    refine ⟨⟨some k, hIs, hk⟩, d, ?_, ?_, ?_⟩
    · intro i
      cases i with
      | none => exact ha
      | some i => exact hres i
    · intro i hi
      cases i with
      | none => exact False.elim (hi (mem_starFacet_none s k))
      | some i =>
        by_cases hik : i = k
        · subst i
          dsimp [d, a]
          rw [div_mul_cancel₀ _ (hbp k hk).ne', sub_self]
        · have his : i ∉ s := fun his => hi ((mem_starFacet_some s k i).mpr ⟨his, hik⟩)
          have hiI : i ∉ I := fun hiI => his (hIs hiI)
          simp [d, hc i his, hbs i hiI]
    · rw [star_synthesis_eq v w b hw]
      rw [hx]
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      dsimp [expandStarCoefficients, d]
      ring
  · let d : Option ι → ℝ := fun i => match i with
      | none => 0
      | some i => c i
    apply Set.mem_iUnion.mpr
    refine ⟨⟨none, hIs⟩, d, ?_, ?_, ?_⟩
    · intro i
      cases i with
      | none => exact le_refl 0
      | some i => exact hc0 i
    · intro i hi
      cases i with
      | none => rfl
      | some i =>
        exact hc i (fun his => hi (Finset.mem_image.mpr ⟨i, his, rfl⟩))
    · rw [Fintype.sum_option]
      simpa only [d, starRays, zero_smul, zero_add] using hx

/-- The union of all geometric cones is preserved exactly by simultaneous
stellar subdivision. Completeness is therefore preserved. -/
theorem SimplicialConeComplex.stellarSubdivision_support {v : ι → E}
    (K : SimplicialConeComplex v) (I : Finset ι) (hI : I.Nonempty) (w : E) (b : ι → ℝ)
    (hb0 : ∀ i, 0 ≤ b i) (hbs : ∀ i, i ∉ I → b i = 0)
    (hbp : ∀ i ∈ I, 0 < b i) (hw : w = ∑ i, b i • v i) :
    (⋃ s ∈ K.starFacets I, raySpan (starRays v w) s) = ⋃ t ∈ K.facets, raySpan v t := by
  apply Set.Subset.antisymm
  · rintro x hx
    obtain ⟨s, hs, hx⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨t, ht, q, hq, rfl⟩ := (K.mem_starFacets I s).mp hs
    exact Set.mem_iUnion₂.mpr ⟨t, ht, starCell_refines v I t w b hb0 hbs hw hq hx⟩
  · rintro x hx
    obtain ⟨t, ht, hx⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp (starCell_cover v I t hI w b hb0 hbs hbp hw hx)
    exact Set.mem_iUnion₂.mpr ⟨starCellGenerators t q.val,
      (K.mem_starFacets I _).mpr ⟨t, ht, q.val, q.property, rfl⟩, hq⟩

/-- The number of generators of each old maximal cone is preserved. -/
theorem starCell_card (I s : Finset ι) {q : Option ι} (hq : starCellValid I s q) :
    (starCellGenerators s q).card = s.card := by
  cases q with
  | none => simp [starCellGenerators, Finset.card_image_of_injective, Option.some_injective]
  | some k =>
    have hks : k ∈ s := hq.1 hq.2
    have hn : none ∉ (s.erase k).image some := by simp
    rw [starCellGenerators, starFacet, Finset.card_insert_of_notMem hn,
      Finset.card_image_of_injective _ (Option.some_injective ι)]
    exact Finset.card_erase_add_one hks

end
end Paper17
