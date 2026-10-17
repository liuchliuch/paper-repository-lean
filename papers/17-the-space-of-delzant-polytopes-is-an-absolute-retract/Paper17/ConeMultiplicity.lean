import Paper17.ConeComplex
import Paper17.StellarCompatibility
import Mathlib.Data.Fintype.EquivFin

/-!
# Integral multiplicity of maximal cones

Multiplicity is computed from the actual integral generators. Enumeration is
irrelevant because row permutations preserve the absolute determinant.
-/
noncomputable section
open scoped BigOperators
namespace Paper17
section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- Real geometric vectors underlying the integral rays. -/
def realRays (v : ι → Fin n → ℤ) : ι → V n := fun i j => (v i j : ℝ)

/-- Enumerate a maximal cone by the ambient coordinate index type. -/
def cellEnumeration (s : Finset ι) (hs : s.card = n) : Fin n ≃ ↑s :=
  (finCongr hs.symm).trans s.equivFin.symm

/-- The actual integral generator matrix of one maximal cone. -/
def cellMatrix (v : ι → Fin n → ℤ) (s : Finset ι) (hs : s.card = n) :
    Matrix (Fin n) (Fin n) ℤ := fun i j => v (cellEnumeration s hs i).val j

/-- Row reordering cannot change the multiplicity. -/
theorem matrix_natAbs_det_of_rows_equiv
    (A B : Matrix (Fin n) (Fin n) ℤ) (e : Equiv.Perm (Fin n))
    (h : ∀ i, A i = B (e i)) : A.det.natAbs = B.det.natAbs := by
  have heq : A = B.submatrix e (Equiv.refl _) := by
    ext i j
    exact congrFun (h i) j
  rw [heq]
  have hh := Matrix.abs_det_submatrix_equiv_equiv e (Equiv.refl _) B
  have hnat := congrArg Int.natAbs hh
  simpa only [Int.natAbs_abs] using hnat

/-- Linear independence of actual ray vectors forces a nonzero integral
maximal-cone determinant. -/
theorem cellMatrix_det_ne_zero (v : ι → Fin n → ℤ) (s : Finset ι) (hs : s.card = n)
    (hi : LinearIndependent ℝ (fun i : ↑s => realRays v i.val)) :
    (cellMatrix v s hs).det ≠ 0 := by
  let B := (cellMatrix v s hs).map (fun z => (z : ℝ))
  have hrows : LinearIndependent ℝ (fun i : Fin n => B i) := by
    exact hi.comp (cellEnumeration s hs) (cellEnumeration s hs).injective
  have hu : IsUnit B := Matrix.vecMul_injective_iff_isUnit.mp
    (Matrix.vecMul_injective_iff.mpr hrows)
  have hdet : B.det ≠ 0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det B).mp hu)
  rw [show B.det = ((cellMatrix v s hs).det : ℝ) from (Int.cast_det _).symm] at hdet
  exact_mod_cast hdet

/-- Exact equality between indexed positive spans and the integral matrix
cones already used for stellar determinant descent. -/
theorem raySpan_eq_latticeCone (v : ι → Fin n → ℤ) (s : Finset ι) (hs : s.card = n) :
    raySpan (realRays v) s = latticeCone (cellMatrix v s hs) := by
  classical
  let e := cellEnumeration s hs
  ext x
  constructor
  · rintro ⟨d, hd, hds, hx⟩
    refine ⟨fun i => d (e i).val, fun i => hd _, ?_⟩
    have hsum : (∑ i, d i • realRays v i) = ∑ i : Fin n, d (e i).val • realRays v (e i).val := by
      rw [sum_supported_eq_subtype _ s d hds]
      exact (Fintype.sum_equiv e _ _ (fun i => rfl)).symm
    rw [hsum] at hx
    intro j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, realRays, cellMatrix, e]
      using congrFun hx j
  · rintro ⟨c, hc, hx⟩
    let d : ι → ℝ := fun i => if hi : i ∈ s then c (e.symm ⟨i, hi⟩) else 0
    have hd : ∀ i, 0 ≤ d i := by
      intro i
      dsimp [d]
      split_ifs
      · exact hc _
      · exact le_refl 0
    have hds : ∀ i, i ∉ s → d i = 0 := fun i hi => dif_neg hi
    refine ⟨d, hd, hds, ?_⟩
    have hsum : (∑ i, d i • realRays v i) = ∑ i : Fin n, c i • realRays v (e i).val := by
      rw [sum_supported_eq_subtype _ s d hds]
      apply (Fintype.sum_equiv e _ _ ?_).symm
      intro i
      simp [d, (e i).property]
    rw [hsum]
    ext j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, realRays, cellMatrix, e] using hx j

/-- Unimodular indexed maximal cones satisfy the genuine smooth-cone predicate. -/
theorem indexed_cone_isSmooth (v : ι → Fin n → ℤ) (s : Finset ι) (hs : s.card = n)
    (hm : (cellMatrix v s hs).det.natAbs = 1) :
    Fan.IsSmoothCone (latticeConeObject (cellMatrix v s hs)) :=
  latticeConeObject_isSmooth _ hm

/-- Total multiplicity function; only cardinality `n` cells occur in a complete
maximal-cone presentation. -/
def coneMultiplicity (v : ι → Fin n → ℤ) (s : Finset ι) : ℕ :=
  if hs : s.card = n then (cellMatrix v s hs).det.natAbs else 0

@[simp] theorem coneMultiplicity_of_card (v : ι → Fin n → ℤ) (s : Finset ι) (hs : s.card = n) :
    coneMultiplicity v s = (cellMatrix v s hs).det.natAbs := dif_pos hs

theorem coneMultiplicity_pos (v : ι → Fin n → ℤ) (s : Finset ι) (hs : s.card = n)
    (hi : LinearIndependent ℝ (fun i : ↑s => realRays v i.val)) :
    0 < coneMultiplicity v s := by
  rw [coneMultiplicity_of_card v s hs]
  exact Int.natAbs_pos.mpr (cellMatrix_det_ne_zero v s hs hi)

/-- The matrix synthesizes exactly the shared-ray combination for supported
coefficients, including signed coefficients. -/
theorem cellSynthesis_eq_global (v : ι → Fin n → ℤ) (s : Finset ι) (hs : s.card = n)
    (b : ι → ℝ) (hb : ∀ i, i ∉ s → b i = 0) :
    latticeSynthesis (cellMatrix v s hs) (fun i => b (cellEnumeration s hs i).val) =
      ∑ i, b i • realRays v i := by
  rw [sum_supported_eq_subtype _ s b hb]
  have hsum := Fintype.sum_equiv (cellEnumeration s hs)
    (fun i => b (cellEnumeration s hs i).val • realRays v (cellEnumeration s hs i).val)
    (fun i : ↑s => b i.val • realRays v i.val) (fun i => rfl)
  rw [← hsum]
  ext j
  simp only [latticeSynthesis_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, cellMatrix, realRays]

/-- Multiplicity is invariant under relabeling the actual ray vectors. -/
theorem cellMatrix_natAbs_relabel {κ : Type*} [Fintype κ] [DecidableEq κ]
    (v : ι → Fin n → ℤ) (v' : κ → Fin n → ℤ)
    (s : Finset ι) (t : Finset κ) (hs : s.card = n) (ht : t.card = n)
    (e : ↑s ≃ ↑t) (hv : ∀ i, v' (e i).val = v i.val) :
    (cellMatrix v s hs).det.natAbs = (cellMatrix v' t ht).det.natAbs := by
  let p : Equiv.Perm (Fin n) :=
    ((cellEnumeration s hs).trans e).trans (cellEnumeration t ht).symm
  apply matrix_natAbs_det_of_rows_equiv _ _ p
  intro i
  have he : cellEnumeration t ht (p i) = e (cellEnumeration s hs i) := by simp [p]
  funext j
  change v (cellEnumeration s hs i).val j = v' (cellEnumeration t ht (p i)).val j
  rw [he]
  exact congrFun (hv (cellEnumeration s hs i)).symm j

/-- The original generators and the generators after replacing one row by the
new ray are in explicit bijection. -/
def starFacetEquiv (s : Finset ι) (k : ι) (hk : k ∈ s) : ↑s ≃ ↑(starFacet s k) := by
  classical
  let f : ↑s → ↑(starFacet s k) := fun i =>
    if hi : i.val = k then ⟨none, mem_starFacet_none s k⟩
    else ⟨some i.val, (mem_starFacet_some s k i.val).mpr ⟨i.property, hi⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j hij
    apply Subtype.ext
    have h := congrArg Subtype.val hij
    by_cases hi : i.val = k
    · by_cases hj : j.val = k
      · exact hi.trans hj.symm
      · simp only [f, dif_pos hi, dif_neg hj] at h
        contradiction
    · by_cases hj : j.val = k
      · simp only [f, dif_neg hi, dif_pos hj] at h
        contradiction
      · simpa only [f, dif_neg hi, dif_neg hj, Option.some.injEq] using h
  · intro j
    cases hj : j.val with
    | none =>
      refine ⟨⟨k, hk⟩, Subtype.ext ?_⟩
      simpa only [f, dif_pos rfl] using hj.symm
    | some i =>
      have hi := (mem_starFacet_some s k i).mp (hj ▸ j.property)
      refine ⟨⟨i, hi.1⟩, Subtype.ext ?_⟩
      simpa only [f, dif_neg hi.2] using hj.symm

/-- The stellar generator matrix is the genuine row replacement, up to a row
permutation. This connects global shared-ray subdivision to determinant descent. -/
theorem starFacet_matrix_natAbs (v : ι → Fin n → ℤ) (s : Finset ι) (hs : s.card = n)
    (k : ι) (hk : k ∈ s) (w : Fin n → ℤ)
    (ht : (starFacet s k).card = n) :
    (cellMatrix (starRays v w) (starFacet s k) ht).det.natAbs =
      ((cellMatrix v s hs).updateRow ((cellEnumeration s hs).symm ⟨k, hk⟩) w).det.natAbs := by
  let e := cellEnumeration s hs
  let f := starFacetEquiv s k hk
  let p : Equiv.Perm (Fin n) := ((cellEnumeration (starFacet s k) ht).trans f.symm).trans e.symm
  apply matrix_natAbs_det_of_rows_equiv _ _ p
  intro i
  have hi : cellEnumeration (starFacet s k) ht i = f (e (p i)) := by simp [p]
  change starRays v w (cellEnumeration (starFacet s k) ht i).val = _
  rw [hi]
  by_cases hp : (e (p i)).val = k
  · have hpi : p i = e.symm ⟨k, hk⟩ := by
      apply e.injective
      apply Subtype.ext
      simpa only [Equiv.apply_symm_apply] using hp
    simp [f, starFacetEquiv, hp, starRays, hpi, Matrix.updateRow, Matrix.of, e]
    change w = (Function.update (cellMatrix v s hs) ((cellEnumeration s hs).symm ⟨k, hk⟩) w)
      ((cellEnumeration s hs).symm ⟨k, hk⟩)
    rw [Function.update_self]
  · have hpi : p i ≠ e.symm ⟨k, hk⟩ := by
      intro heq
      apply hp
      rw [heq, Equiv.apply_symm_apply]
    simp [f, starFacetEquiv, hp, starRays, Matrix.updateRow, Matrix.of, hpi, cellMatrix, e]
    change v (cellEnumeration s hs (p i)).val =
      (Function.update (cellMatrix v s hs) ((cellEnumeration s hs).symm ⟨k, hk⟩) w) (p i)
    rw [Function.update_of_ne hpi]
    rfl

/-- Every affected maximal cone has strictly smaller actual integral
multiplicity after inserting the shared parallelepiped ray. -/
theorem star_coneMultiplicity_lt (v : ι → Fin n → ℤ) (s : Finset ι) (hs : s.card = n)
    (hi : LinearIndependent ℝ (fun i : ↑s => realRays v i.val))
    (I : Finset ι) (hIs : I ⊆ s) (k : ι) (hk : k ∈ I)
    (w : Fin n → ℤ) (b : ι → ℝ)
    (hbs : ∀ i, i ∉ I → b i = 0) (hbp : ∀ i ∈ I, 0 < b i)
    (hb1 : ∀ i ∈ I, b i < 1)
    (hw : (fun j => (w j : ℝ)) = ∑ i, b i • realRays v i) :
    coneMultiplicity (starRays v w) (starFacet s k) < coneMultiplicity v s := by
  have hks : k ∈ s := hIs hk
  have ht : (starFacet s k).card = n := (starCell_card I s (q := some k) ⟨hIs, hk⟩).trans hs
  let e := cellEnumeration s hs
  let a : Fin n := e.symm ⟨k, hks⟩
  let c : V n := fun i => b (e i).val
  have hbs' : ∀ i, i ∉ s → b i = 0 := fun i hin => hbs i (fun hii => hin (hIs hii))
  have hcoord : ∀ j, (w j : ℝ) = ∑ i, c i * (cellMatrix v s hs i j : ℝ) := by
    intro j
    have heq := (cellSynthesis_eq_global v s hs b hbs').trans hw.symm
    exact congrFun heq.symm j
  rw [coneMultiplicity_of_card _ _ ht, starFacet_matrix_natAbs v s hs k hks w ht,
    coneMultiplicity_of_card v s hs]
  exact (multiplicity_strictly_decreases (cellMatrix v s hs) w c hcoord
    (cellMatrix_det_ne_zero v s hs hi) a
    (by simpa only [c, a, Equiv.apply_symm_apply] using hbp k hk)
    (by simpa only [c, a, Equiv.apply_symm_apply] using hb1 k hk)).2

/-- The unchanged cells merely acquire the old-ray index `some`. -/
def someFacetEquiv (s : Finset ι) : ↑s ≃ ↑(s.image some) := by
  classical
  apply Equiv.ofBijective (fun i : ↑s => ⟨some i.val, Finset.mem_image.mpr ⟨i.val, i.property, rfl⟩⟩)
  constructor
  · intro i j hij
    apply Subtype.ext
    exact Option.some.inj (congrArg Subtype.val hij)
  · intro j
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp j.property
    exact ⟨⟨i, hi⟩, Subtype.ext heq⟩

theorem coneMultiplicity_some_image (v : ι → Fin n → ℤ) (s : Finset ι) (hs : s.card = n)
    (w : Fin n → ℤ) :
    coneMultiplicity (starRays v w) (s.image some) = coneMultiplicity v s := by
  have ht : (s.image some).card = n :=
    (Finset.card_image_of_injective s (Option.some_injective ι)).trans hs
  rw [coneMultiplicity_of_card _ _ ht, coneMultiplicity_of_card v s hs]
  exact (cellMatrix_natAbs_relabel v (starRays v w) s (s.image some) hs ht
    (someFacetEquiv s) (fun i => rfl)).symm

@[simp] theorem realRays_starRays (v : ι → Fin n → ℤ) (w : Fin n → ℤ) :
    realRays (starRays v w) = starRays (realRays v) (fun j => (w j : ℝ)) := by
  funext i j
  cases i <;> rfl

end
end Paper17
