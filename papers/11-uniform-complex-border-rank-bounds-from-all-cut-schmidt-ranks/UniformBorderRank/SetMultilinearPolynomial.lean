import UniformBorderRank.Flattening
import Mathlib.Algebra.MvPolynomial.PDeriv

/-! The actual set-multilinear polynomial of a coefficient tensor, with
coefficient-extraction and formal partial-derivative identities. -/
noncomputable section
namespace UniformBorderRank
open Finset

abbrev GroupVar {N : ℕ} (d : Fin N → ℕ) := Σ i : Fin N, Fin (d i)
abbrev CutIndex {N : ℕ} (d : Fin N → ℕ) (C : Finset (Fin N)) := ∀ i ∈ C, Fin (d i)

/-- The exponent chooses one variable from each of the indicated site groups. -/
def groupExponent {N : ℕ} {d : Fin N → ℕ} (C : Finset (Fin N)) (u : CutIndex d C) :
    GroupVar d →₀ ℕ := by
  classical
  exact ∑ i : C, Finsupp.single ⟨i.val, u i.val i.property⟩ 1

lemma groupExponent_apply {N : ℕ} {d : Fin N → ℕ} (C : Finset (Fin N))
    (u : CutIndex d C) (i : Fin N) (a : Fin (d i)) :
    groupExponent C u ⟨i,a⟩ = if hi : i ∈ C then (if u i hi = a then 1 else 0) else 0 := by
  classical
  unfold groupExponent
  rw [Finsupp.finset_sum_apply]
  by_cases hi : i ∈ C
  · rw [dif_pos hi, sum_eq_single (⟨i,hi⟩ : C)]
    · simp [Finsupp.single_apply]
    · intro j _ hj
      have hji : j.val ≠ i := fun h => hj (Subtype.ext h)
      have hs : (⟨j.val, u j.val j.property⟩ : GroupVar d) ≠ ⟨i,a⟩ :=
        fun h => hji (congrArg Sigma.fst h)
      simp [Finsupp.single_apply, hs]
    · simp
  · rw [dif_neg hi]
    apply sum_eq_zero
    intro j _
    have hji : j.val ≠ i := fun h => hi (h ▸ j.property)
    have hs : (⟨j.val, u j.val j.property⟩ : GroupVar d) ≠ ⟨i,a⟩ :=
      fun h => hji (congrArg Sigma.fst h)
    simp [Finsupp.single_apply, hs]

/-- Both the retained group mask and its coordinate assignment are recovered
from the exponent. Thus distinct masks have disjoint monomial supports. -/
theorem groupExponent_joint_injective {N : ℕ} {d : Fin N → ℕ} :
    Function.Injective (fun p : Σ C : Finset (Fin N), CutIndex d C => groupExponent p.1 p.2) := by
  classical
  rintro ⟨C,u⟩ ⟨D,v⟩ h
  have hCD : C = D := by
    apply Finset.ext
    intro i
    constructor
    · intro hi
      by_contra hn
      have hv := congrArg (fun e : GroupVar d →₀ ℕ => e ⟨i,u i hi⟩) h
      simp [groupExponent_apply, hi, hn] at hv
    · intro hi
      by_contra hn
      have hv := congrArg (fun e : GroupVar d →₀ ℕ => e ⟨i,v i hi⟩) h
      simp [groupExponent_apply, hi, hn] at hv
  subst D
  have huv : u = v := by
    funext i hi
    have hv := congrArg (fun e : GroupVar d →₀ ℕ => e ⟨i,u i hi⟩) h
    by_contra hn
    simp [groupExponent_apply, hi, Ne.symm hn] at hv
  subst v
  rfl

lemma groupExponent_injective {N : ℕ} {d : Fin N → ℕ} (C : Finset (Fin N)) :
    Function.Injective (groupExponent (d := d) C) := by
  intro u v h
  have hs : (⟨C,u⟩ : Σ D : Finset (Fin N), CutIndex d D) = ⟨C,v⟩ :=
    groupExponent_joint_injective (d := d) h
  exact eq_of_heq (Sigma.mk.inj_iff.mp hs).2

/-- Embed actual coefficient arrays in the polynomial ring, linearly. -/
def groupPolynomial {N : ℕ} {d : Fin N → ℕ} (C : Finset (Fin N)) :
    (CutIndex d C → ℂ) →ₗ[ℂ] MvPolynomial (GroupVar d) ℂ := by
  classical
  exact {
    toFun := fun f => ∑ u, MvPolynomial.monomial (groupExponent C u) (f u)
    map_add' := by intro f g; simp [map_add, sum_add_distrib]
    map_smul' := by intro c f; simp [MvPolynomial.smul_monomial, smul_sum] }

lemma groupPolynomial_apply {N : ℕ} {d : Fin N → ℕ} (C : Finset (Fin N))
    (f : CutIndex d C → ℂ) :
    groupPolynomial C f = ∑ u, MvPolynomial.monomial (groupExponent C u) (f u) := by
  classical
  rfl

/-- Coefficients in the matching mask exactly recover the original array. -/
theorem groupPolynomial_coeff {N : ℕ} {d : Fin N → ℕ} (C : Finset (Fin N))
    (f : CutIndex d C → ℂ) (u : CutIndex d C) :
    MvPolynomial.coeff (groupExponent C u) (groupPolynomial C f) = f u := by
  classical
  rw [groupPolynomial_apply]
  calc
    _ = ∑ v : CutIndex d C, MvPolynomial.coeff (groupExponent C u)
        (MvPolynomial.monomial (groupExponent C v) (f v)) :=
      MvPolynomial.coeff_sum univ (fun v : CutIndex d C =>
        MvPolynomial.monomial (groupExponent C v) (f v)) (groupExponent C u)
    _ = f u := by simp [MvPolynomial.coeff_monomial, (groupExponent_injective C).eq_iff]

/-- A different group mask contributes no coefficient to this mask. -/
theorem groupPolynomial_coeff_of_ne {N : ℕ} {d : Fin N → ℕ}
    (C D : Finset (Fin N)) (hCD : C ≠ D)
    (f : CutIndex d C → ℂ) (v : CutIndex d D) :
    MvPolynomial.coeff (groupExponent D v) (groupPolynomial C f) = 0 := by
  classical
  rw [groupPolynomial_apply]
  calc
    _ = ∑ u : CutIndex d C, MvPolynomial.coeff (groupExponent D v)
        (MvPolynomial.monomial (groupExponent C u) (f u)) :=
      MvPolynomial.coeff_sum univ (fun u : CutIndex d C =>
        MvPolynomial.monomial (groupExponent C u) (f u)) (groupExponent D v)
    _ = 0 := by
      apply sum_eq_zero
      intro u _
      have hn : groupExponent D v ≠ groupExponent C u := by
        intro h
        have he : (⟨D,v⟩ : Σ E : Finset (Fin N), CutIndex d E) = ⟨C,u⟩ :=
          groupExponent_joint_injective (d := d) h
        exact hCD (congrArg Sigma.fst he).symm
      simp [MvPolynomial.coeff_monomial, hn, Ne.symm hn]

lemma groupPolynomial_injective {N : ℕ} {d : Fin N → ℕ} (C : Finset (Fin N)) :
    Function.Injective (groupPolynomial (d := d) C) := by
  intro f g h
  funext u
  have he := congrArg (MvPolynomial.coeff (groupExponent C u)) h
  simpa only [groupPolynomial_coeff] using he

/-- Transport the coefficient mask together with its proof-indexed coordinates. -/
lemma groupPolynomial_reindex_mask {N : ℕ} {d : Fin N → ℕ}
    (C D : Finset (Fin N)) (h : C = D) (f : CutIndex d C → ℂ) :
    groupPolynomial C f = groupPolynomial D (fun v => f (fun i hi => v i (h ▸ hi))) := by
  subst D
  rfl

/-- Insert a specified coordinate at the site erased by a formal derivative. -/
def insertCutCoordinate {N : ℕ} {d : Fin N → ℕ} (C : Finset (Fin N))
    (i : Fin N) (hi : i ∈ C) (a : Fin (d i)) (v : CutIndex d (C.erase i)) : CutIndex d C :=
  fun j hj => if hji : j = i then Fin.cast (congrArg d hji).symm a
    else v j (mem_erase.mpr ⟨hji,hj⟩)

@[simp] lemma insertCutCoordinate_self {N : ℕ} {d : Fin N → ℕ} (C : Finset (Fin N))
    (i : Fin N) (hi : i ∈ C) (a : Fin (d i)) (v : CutIndex d (C.erase i)) :
    insertCutCoordinate C i hi a v i hi = a := by simp [insertCutCoordinate]

@[simp] lemma restrict_insertCutCoordinate {N : ℕ} {d : Fin N → ℕ} (C : Finset (Fin N))
    (i : Fin N) (hi : i ∈ C) (a : Fin (d i)) (v : CutIndex d (C.erase i)) :
    (fun j hj => insertCutCoordinate C i hi a v j (mem_of_mem_erase hj)) = v := by
  funext j hj
  simp [insertCutCoordinate, (mem_erase.mp hj).1]

/-- Splitting a retained coordinate into its value at one site and all the
other site coordinates is an actual finite-coordinate equivalence. -/
def cutCoordinateEquiv {N : ℕ} {d : Fin N → ℕ} (C : Finset (Fin N))
    (i : Fin N) (hi : i ∈ C) : CutIndex d C ≃ Fin (d i) × CutIndex d (C.erase i) where
  toFun u := (u i hi, fun j hj => u j (mem_of_mem_erase hj))
  invFun p := insertCutCoordinate C i hi p.1 p.2
  left_inv u := by
    funext j hj
    by_cases hji : j = i
    · subst j; simp [insertCutCoordinate]
    · simp [insertCutCoordinate, hji]
  right_inv p := by
    apply Prod.ext
    · exact insertCutCoordinate_self C i hi p.1 p.2
    · exact restrict_insertCutCoordinate C i hi p.1 p.2

/-- Differentiation removes exactly the selected site's exponent, without
altering the exponents chosen in any other site group. -/
lemma groupExponent_sub_single {N : ℕ} {d : Fin N → ℕ} (C : Finset (Fin N))
    (u : CutIndex d C) (i : Fin N) (hi : i ∈ C) :
    groupExponent C u - Finsupp.single (⟨i,u i hi⟩ : GroupVar d) 1 =
      groupExponent (C.erase i) (fun j hj => u j (mem_of_mem_erase hj)) := by
  classical
  ext v
  obtain ⟨j,a⟩ := v
  rw [Finsupp.tsub_apply, groupExponent_apply, groupExponent_apply]
  by_cases hji : j = i
  · subst j
    simp [hi, Finsupp.single_apply]
  · have hs : (⟨i,u i hi⟩ : GroupVar d) ≠ ⟨j,a⟩ :=
      fun h => hji (congrArg Sigma.fst h).symm
    by_cases hj : j ∈ C
    · have he : j ∈ C.erase i := mem_erase.mpr ⟨hji,hj⟩
      simp [hj, he, Finsupp.single_apply, hs]
    · have he : j ∉ C.erase i := fun h => hj (mem_of_mem_erase h)
      simp [hj, he, Finsupp.single_apply, hs]

lemma pderiv_groupMonomial_of_not_mem {N : ℕ} {d : Fin N → ℕ}
    (C : Finset (Fin N)) (u : CutIndex d C) (i : Fin N) (hi : i ∉ C)
    (a : Fin (d i)) (z : ℂ) :
    MvPolynomial.pderiv (⟨i,a⟩ : GroupVar d) (MvPolynomial.monomial (groupExponent C u) z) = 0 := by
  classical
  simp [MvPolynomial.pderiv_monomial, groupExponent_apply, hi]

lemma pderiv_groupMonomial_of_mem {N : ℕ} {d : Fin N → ℕ}
    (C : Finset (Fin N)) (u : CutIndex d C) (i : Fin N) (hi : i ∈ C)
    (a : Fin (d i)) (z : ℂ) :
    MvPolynomial.pderiv (⟨i,a⟩ : GroupVar d) (MvPolynomial.monomial (groupExponent C u) z) =
      if u i hi = a then
        MvPolynomial.monomial (groupExponent (C.erase i) (fun j hj => u j (mem_of_mem_erase hj))) z
      else 0 := by
  classical
  by_cases h : u i hi = a
  · subst a
    simp only [MvPolynomial.pderiv_monomial, groupExponent_apply, dif_pos hi, ite_true,
      Nat.cast_one, mul_one, groupExponent_sub_single]
  · simp [MvPolynomial.pderiv_monomial, groupExponent_apply, hi, h]

/-- A formal derivative in a group absent from the mask is actually zero. -/
theorem pderiv_groupPolynomial_of_not_mem {N : ℕ} {d : Fin N → ℕ}
    (C : Finset (Fin N)) (f : CutIndex d C → ℂ) (i : Fin N) (hi : i ∉ C)
    (a : Fin (d i)) :
    MvPolynomial.pderiv (⟨i,a⟩ : GroupVar d) (groupPolynomial C f) = 0 := by
  classical
  rw [groupPolynomial_apply, map_sum]
  simp_rw [pderiv_groupMonomial_of_not_mem C _ i hi a]
  simp

/-- A formal derivative in a retained group is the actual sliced coefficient
array embedded on the erased mask. This is a statement about mathlib's
`MvPolynomial.pderiv`, rather than a surrogate differentiation operation. -/
theorem pderiv_groupPolynomial_of_mem {N : ℕ} {d : Fin N → ℕ}
    (C : Finset (Fin N)) (f : CutIndex d C → ℂ) (i : Fin N) (hi : i ∈ C)
    (a : Fin (d i)) :
    MvPolynomial.pderiv (⟨i,a⟩ : GroupVar d) (groupPolynomial C f) =
      groupPolynomial (C.erase i) (fun v => f (insertCutCoordinate C i hi a v)) := by
  classical
  rw [groupPolynomial_apply, groupPolynomial_apply, map_sum,
    ← (cutCoordinateEquiv (d := d) C i hi).symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  change (∑ a', ∑ v, MvPolynomial.pderiv (⟨i,a⟩ : GroupVar d)
    (MvPolynomial.monomial (groupExponent C (insertCutCoordinate C i hi a' v))
      (f (insertCutCoordinate C i hi a' v)))) = _
  simp_rw [pderiv_groupMonomial_of_mem C _ i hi a, insertCutCoordinate_self,
    restrict_insertCutCoordinate]
  rw [sum_comm]
  simp

/-- Full coordinate tuples and proof-indexed full-cut tuples are equivalent. -/
def fullCutIndexEquiv {N : ℕ} (d : Fin N → ℕ) :
    (∀ i, Fin (d i)) ≃ CutIndex d univ where
  toFun u i _ := u i
  invFun u i := u i (mem_univ i)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The actual set-multilinear polynomial `f_T`, as an explicit sum of its
original tensor coefficients times one variable in each site group. -/
def tensorPolynomial {N : ℕ} (d : Fin N → ℕ) (T : Coeffs d) : MvPolynomial (GroupVar d) ℂ :=
  ∑ u : (∀ i, Fin (d i)),
    MvPolynomial.monomial (groupExponent univ (fun i _ => u i)) (T u)

lemma tensorPolynomial_eq_groupPolynomial {N : ℕ} (d : Fin N → ℕ) (T : Coeffs d) :
    tensorPolynomial d T = groupPolynomial univ (fun u => T (fun i => u i (mem_univ i))) := by
  classical
  rw [groupPolynomial_apply, ← (fullCutIndexEquiv d).sum_comp]
  rfl

lemma tensorPolynomial_coeff {N : ℕ} (d : Fin N → ℕ) (T : Coeffs d) (u : ∀ i, Fin (d i)) :
    MvPolynomial.coeff (groupExponent univ (fun i _ => u i)) (tensorPolynomial d T) = T u := by
  rw [tensorPolynomial_eq_groupPolynomial, groupPolynomial_coeff]

/-- Freeze the differentiated groups at an actual flattening row. -/
def cutPolynomial {N : ℕ} {d : Fin N → ℕ} (T : Coeffs d)
    (S : Finset (Fin N)) (a : CutIndex d S) : MvPolynomial (GroupVar d) ℂ :=
  groupPolynomial Sᶜ (flatCoeff d T S a)

/-- Extend an actual cut row by prescribing the newly differentiated site. -/
def insertCutRow {N : ℕ} {d : Fin N → ℕ} (S : Finset (Fin N)) (i : Fin N)
    (a : CutIndex d S) (x : Fin (d i)) : CutIndex d (insert i S) :=
  fun j hj => if hji : j = i then Fin.cast (congrArg d hji).symm x
    else a j ((mem_insert.mp hj).resolve_left hji)

/-- Repeated differentiation in an already frozen site group vanishes. -/
theorem pderiv_cutPolynomial_of_mem {N : ℕ} {d : Fin N → ℕ} (T : Coeffs d)
    (S : Finset (Fin N)) (a : CutIndex d S) (i : Fin N) (hi : i ∈ S)
    (x : Fin (d i)) :
    MvPolynomial.pderiv (⟨i,x⟩ : GroupVar d) (cutPolynomial T S a) = 0 := by
  exact pderiv_groupPolynomial_of_not_mem Sᶜ (flatCoeff d T S a) i
    (fun h => (mem_compl.mp h) hi) x

/-- Actual partial derivatives of flattening rows are exactly the rows of
the enlarged original cut, with the corresponding new coordinate inserted. -/
theorem pderiv_cutPolynomial_of_not_mem {N : ℕ} {d : Fin N → ℕ} (T : Coeffs d)
    (S : Finset (Fin N)) (a : CutIndex d S) (i : Fin N) (hi : i ∉ S)
    (x : Fin (d i)) :
    MvPolynomial.pderiv (⟨i,x⟩ : GroupVar d) (cutPolynomial T S a) =
      cutPolynomial T (insert i S) (insertCutRow S i a x) := by
  classical
  unfold cutPolynomial
  rw [pderiv_groupPolynomial_of_mem Sᶜ (flatCoeff d T S a) i (mem_compl.mpr hi) x]
  rw [groupPolynomial_reindex_mask (Sᶜ.erase i) (insert i S)ᶜ
    (Finset.compl_insert (s := S) (a := i)).symm]
  congr 1
  funext v
  unfold flatCoeff
  congr 1
  funext j
  by_cases hji : j = i
  · subst j
    simp [hi, insertCutCoordinate, insertCutRow]
  · by_cases hj : j ∈ S
    · simp [hj, insertCutCoordinate, insertCutRow, hji]
    · simp [hj, insertCutCoordinate, insertCutRow, hji]

/-- The empty derivative cut is the actual original polynomial. -/
theorem cutPolynomial_empty {N : ℕ} {d : Fin N → ℕ} (T : Coeffs d)
    (a : CutIndex d ∅) : cutPolynomial T ∅ a = tensorPolynomial d T := by
  classical
  rw [tensorPolynomial_eq_groupPolynomial]
  unfold cutPolynomial
  rw [groupPolynomial_reindex_mask ((∅ : Finset (Fin N))ᶜ) univ Finset.compl_empty]
  congr 1

/-- Monomials for a group mask are precisely products of one variable in
each indicated group. -/
lemma groupMonomial_eq_product {N : ℕ} {d : Fin N → ℕ} (C : Finset (Fin N))
    (u : CutIndex d C) (z : ℂ) :
    MvPolynomial.monomial (groupExponent C u) z =
      MvPolynomial.C z * ∏ i : C, MvPolynomial.X (⟨i.val,u i.val i.property⟩ : GroupVar d) := by
  classical
  unfold groupExponent
  rw [MvPolynomial.monomial_sum_index]
  rfl

/-- The explicit polynomial `f_T` from the source paper: the tensor
coefficient multiplies a product of one variable from each original site. -/
theorem tensorPolynomial_eq_sum_product {N : ℕ} (d : Fin N → ℕ) (T : Coeffs d) :
    tensorPolynomial d T = ∑ u : (∀ i, Fin (d i)),
      MvPolynomial.C (T u) * ∏ i : Fin N, MvPolynomial.X (⟨i,u i⟩ : GroupVar d) := by
  classical
  unfold tensorPolynomial
  apply sum_congr rfl
  intro u _
  rw [groupMonomial_eq_product]
  congr 1
  simpa using
    (Finset.prod_subtype (univ : Finset (Fin N)) (by simp)
      (fun i => MvPolynomial.X (⟨i,u i⟩ : GroupVar d))).symm

end UniformBorderRank
