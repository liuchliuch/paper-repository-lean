import Paper17.GlobalResolutionStep

/-!
# Terminating smooth resolution of integral simplicial cone complexes

The finite index type is bundled so recursive stellar subdivision can adjoin
new actual integral rays. No refinement or resolution conclusion is a field.
The algorithm terminates by the proved strict natural-number weight descent.
-/
noncomputable section
open scoped BigOperators
universe u
namespace Paper17

/-- Finite integral rays with a genuine geometric simplicial cone complex,
all maximal cones having the ambient dimension. -/
structure IntegralConeComplex (n : ℕ) where
  index : Type u
  [indexFintype : Fintype index]
  [indexDecidableEq : DecidableEq index]
  rays : index → Fin n → ℤ
  complex : SimplicialConeComplex (realRays rays)
  fullCard : ∀ s ∈ complex.facets, s.card = n

attribute [instance] IntegralConeComplex.indexFintype IntegralConeComplex.indexDecidableEq

namespace IntegralConeComplex
variable {n : ℕ}

/-- Actual geometric union of the maximal cones. -/
def support (K : IntegralConeComplex.{u} n) : Set (V n) :=
  ⋃ s ∈ K.complex.facets, raySpan (realRays K.rays) s

/-- The integral measure whose strict decrease was proved globally. -/
def weight (K : IntegralConeComplex.{u} n) : ℕ :=
  ∑ s ∈ K.complex.facets, (n + 1) ^ coneMultiplicity K.rays s

/-- Geometric refinement between the actual maximal-cone carriers. -/
def Refines (L K : IntegralConeComplex.{u} n) : Prop :=
  ∀ s ∈ L.complex.facets, ∃ t ∈ K.complex.facets,
    raySpan (realRays L.rays) s ⊆ raySpan (realRays K.rays) t

theorem refines_refl (K : IntegralConeComplex.{u} n) : K.Refines K :=
  fun s hs => ⟨s, hs, Set.Subset.rfl⟩

theorem Refines.trans {L K J : IntegralConeComplex.{u} n}
    (hLK : L.Refines K) (hKJ : K.Refines J) : L.Refines J := by
  intro s hs
  obtain ⟨t, ht, hst⟩ := hLK s hs
  obtain ⟨r, hr, htr⟩ := hKJ t ht
  exact ⟨r, hr, hst.trans htr⟩

/-- The global star, retaining genuine intersection and independence data. -/
def stellarSubdivision (K : IntegralConeComplex.{u} n) (I : Finset K.index)
    (w : Fin n → ℤ) (b : K.index → ℝ)
    (hb0 : ∀ i, 0 ≤ b i) (hbs : ∀ i, i ∉ I → b i = 0)
    (hbp : ∀ i ∈ I, 0 < b i)
    (hw : (fun j => (w j : ℝ)) = ∑ i, b i • realRays K.rays i) :
    IntegralConeComplex.{u} n where
  index := Option K.index
  rays := starRays K.rays w
  complex := {
    facets := K.complex.starFacets I
    independent := by
      intro s hs
      rw [realRays_starRays]
      exact (K.complex.stellarSubdivision I _ b hb0 hbs hbp hw).independent s hs
    intersection := by
      intro s hs t ht
      rw [realRays_starRays]
      exact (K.complex.stellarSubdivision I _ b hb0 hbs hbp hw).intersection s hs t ht }
  fullCard := starFacets_full_card K.rays K.complex K.fullCard I

theorem stellarSubdivision_support (K : IntegralConeComplex.{u} n)
    (I : Finset K.index) (hI : I.Nonempty) (w : Fin n → ℤ) (b : K.index → ℝ)
    (hb0 : ∀ i, 0 ≤ b i) (hbs : ∀ i, i ∉ I → b i = 0)
    (hbp : ∀ i ∈ I, 0 < b i)
    (hw : (fun j => (w j : ℝ)) = ∑ i, b i • realRays K.rays i) :
    (K.stellarSubdivision I w b hb0 hbs hbp hw).support = K.support := by
  change (⋃ s ∈ K.complex.starFacets I, raySpan (realRays (starRays K.rays w)) s) = _
  rw [realRays_starRays]
  exact K.complex.stellarSubdivision_support I hI _ b hb0 hbs hbp hw

theorem stellarSubdivision_refines (K : IntegralConeComplex.{u} n)
    (I : Finset K.index) (w : Fin n → ℤ) (b : K.index → ℝ)
    (hb0 : ∀ i, 0 ≤ b i) (hbs : ∀ i, i ∉ I → b i = 0)
    (hbp : ∀ i ∈ I, 0 < b i)
    (hw : (fun j => (w j : ℝ)) = ∑ i, b i • realRays K.rays i) :
    (K.stellarSubdivision I w b hb0 hbs hbp hw).Refines K := by
  intro s hs
  obtain ⟨t, ht, q, hq, rfl⟩ := (K.complex.mem_starFacets I s).mp hs
  refine ⟨t, ht, ?_⟩
  change raySpan (realRays (starRays K.rays w)) _ ⊆ _
  rw [realRays_starRays]
  exact starCell_refines _ I t _ b hb0 hbs hw hq

/-- Admissible lattice data for one stellar step. These fields specify the
actual new ray and its coordinates; no refinement or termination conclusion
is assumed. -/
structure StellarData (K : IntegralConeComplex.{u} n) where
  face : Finset K.index
  face_nonempty : face.Nonempty
  face_in : ∃ s ∈ K.complex.facets, face ⊆ s
  ray : Fin n → ℤ
  ray_ne_zero : ray ≠ 0
  coefficients : K.index → ℝ
  nonneg : ∀ i, 0 ≤ coefficients i
  supported : ∀ i, i ∉ face → coefficients i = 0
  positive : ∀ i ∈ face, 0 < coefficients i
  lt_one : ∀ i ∈ face, coefficients i < 1
  ray_eq : (fun j => (ray j : ℝ)) = ∑ i, coefficients i • realRays K.rays i

def StellarData.result {K : IntegralConeComplex.{u} n} (D : StellarData K) :
    IntegralConeComplex.{u} n :=
  K.stellarSubdivision D.face D.ray D.coefficients D.nonneg D.supported D.positive D.ray_eq

theorem StellarData.support_eq {K : IntegralConeComplex.{u} n} (D : StellarData K) :
    D.result.support = K.support :=
  stellarSubdivision_support K D.face D.face_nonempty D.ray D.coefficients
    D.nonneg D.supported D.positive D.ray_eq

theorem StellarData.result_refines {K : IntegralConeComplex.{u} n} (D : StellarData K) :
    D.result.Refines K :=
  stellarSubdivision_refines K D.face D.ray D.coefficients D.nonneg D.supported D.positive D.ray_eq

theorem StellarData.weight_lt {K : IntegralConeComplex.{u} n} (D : StellarData K) :
    D.result.weight < K.weight :=
  stellar_integral_weight_lt K.rays K.complex K.fullCard D.face D.face_nonempty D.face_in
    D.ray D.coefficients D.nonneg D.supported D.positive D.lt_one D.ray_eq

theorem stellarData_nonempty (K : IntegralConeComplex.{u} n)
    (hsingular : ∃ s ∈ K.complex.facets, 1 < coneMultiplicity K.rays s) :
    Nonempty (StellarData K) := by
  obtain ⟨I, w, b, hI, hface, hw0, hb0, hbs, hb, hw, _⟩ :=
    exists_global_stellar_lattice_step K.rays K.complex K.fullCard hsingular
  exact ⟨{
    face := I
    face_nonempty := hI
    face_in := hface
    ray := w
    ray_ne_zero := hw0
    coefficients := b
    nonneg := hb0
    supported := hbs
    positive := fun i hi => (hb i hi).1
    lt_one := fun i hi => (hb i hi).2
    ray_eq := hw }⟩

/-- Any actually proved one-step invariant is retained by the terminating
resolution. In particular this provides the recursion interface for a later
geometric proof of projectivity preservation; projectivity is not assumed or
claimed by this theorem. -/
theorem exists_smooth_refinement_preserving (P : IntegralConeComplex.{u} n → Prop)
    (hstep : ∀ K, ∀ D : StellarData K, P K → P D.result)
    (K : IntegralConeComplex.{u} n) (hPK : P K) :
    ∃ L : IntegralConeComplex.{u} n,
      (∀ s ∈ L.complex.facets, coneMultiplicity L.rays s = 1) ∧
      L.support = K.support ∧ L.Refines K ∧ P L := by
  classical
  suffices ∀ N : ℕ, ∀ K : IntegralConeComplex.{u} n, K.weight = N → P K →
      ∃ L : IntegralConeComplex.{u} n,
        (∀ s ∈ L.complex.facets, coneMultiplicity L.rays s = 1) ∧
        L.support = K.support ∧ L.Refines K ∧ P L from this _ K rfl hPK
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro K hN hPK
    by_cases hsmooth : ∀ s ∈ K.complex.facets, coneMultiplicity K.rays s = 1
    · exact ⟨K, hsmooth, rfl, refines_refl K, hPK⟩
    · have hsing : ∃ s ∈ K.complex.facets, 1 < coneMultiplicity K.rays s := by
        push_neg at hsmooth
        obtain ⟨s, hs, hne⟩ := hsmooth
        have hp := coneMultiplicity_pos K.rays s (K.fullCard s hs) (K.complex.independent s hs)
        exact ⟨s, hs, by omega⟩
      let D := Classical.choice (stellarData_nonempty K hsing)
      have hweight : D.result.weight < N := D.weight_lt.trans_eq hN
      obtain ⟨L, hsmoothL, hsupport, hrefine, hPL⟩ :=
        ih D.result.weight hweight D.result rfl (hstep K D hPK)
      exact ⟨L, hsmoothL, hsupport.trans D.support_eq, hrefine.trans D.result_refines, hPL⟩

/-- Full smooth simplicial resolution. The output is again an actual cone
complex on integral rays, preserves the union, and geometrically refines the
input. Compatibility is retained by the structure's proved intersection field. -/
theorem exists_smooth_refinement (K : IntegralConeComplex.{u} n) :
    ∃ L : IntegralConeComplex.{u} n,
      (∀ s ∈ L.complex.facets, coneMultiplicity L.rays s = 1) ∧
      L.support = K.support ∧ L.Refines K := by
  let P : IntegralConeComplex.{u} n → Prop := fun L => L.support = K.support ∧ L.Refines K
  have hstep : ∀ J, ∀ D : StellarData J, P J → P D.result := by
    intro J D hJ
    exact ⟨D.support_eq.trans hJ.1, D.result_refines.trans hJ.2⟩
  obtain ⟨L, hm, hs, hr, _⟩ := exists_smooth_refinement_preserving P hstep K ⟨rfl, refines_refl K⟩
  exact ⟨L, hm, hs, hr⟩

end IntegralConeComplex
end Paper17
