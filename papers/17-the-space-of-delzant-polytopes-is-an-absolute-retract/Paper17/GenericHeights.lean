import Paper17.HalfspaceVertices
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite

/-!
# Arbitrarily small outward generic supporting-height perturbations

A nontrivial relation among `n+1` normals gives a nonzero degeneracy polynomial
along the explicit curve `h_i + t^(code i)`. Finitely many bad real roots are
avoided inside an actual positive interval. Thus all offsets are positive and
small, and no more than `n` hyperplanes can be simultaneously active.
-/
noncomputable section
open scoped BigOperators
namespace Paper17
section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

theorem exists_nontrivial_normal_relation (a : ι → V n) (s : Finset ι) (hs : n < s.card) :
    ∃ c : ↑s → ℝ, c ≠ 0 ∧ ∑ i, c i • a i.val = 0 := by
  classical
  have hnot : ¬ LinearIndependent ℝ (fun i : ↑s => a i.val) := by
    intro hi
    have hh := hi.fintype_card_le_finrank
    have hle : s.card ≤ n := by
      simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, Fintype.card_coe] using hh
    omega
  rw [linearIndependent_iff_injective_fintypeLinearCombination] at hnot
  obtain ⟨c, d, heq, hne⟩ := Function.not_injective_iff.mp hnot
  refine ⟨c - d, sub_ne_zero.mpr hne, ?_⟩
  change (∑ i, (c i - d i) • a i.val) = 0
  simp only [sub_smul, Finset.sum_sub_distrib]
  exact sub_eq_zero.mpr heq

/-- Every overdetermined set of normals has a genuine nonzero polynomial
whose roots include all degeneracies along the proposed perturbation curve. -/
theorem exists_degeneracy_polynomial (a : ι → V n) (h : ι → ℝ)
    (code : ι → ℕ) (hcode : Function.Injective code) (hpos : ∀ i, 0 < code i)
    (s : Finset ι) (hs : n < s.card) :
    ∃ p : Polynomial ℝ, p ≠ 0 ∧ ∀ t : ℝ, ∀ x : V n,
      (∀ i ∈ s, dot (a i) x = h i + t ^ code i) → p.eval t = 0 := by
  classical
  obtain ⟨c, hc0, hrel⟩ := exists_nontrivial_normal_relation a s hs
  obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
    by_contra! hn
    apply hc0
    funext j
    exact hn j
  let p : Polynomial ℝ := Polynomial.C (∑ i : ↑s, c i * h i.val) +
    ∑ i : ↑s, Polynomial.monomial (code i.val) (c i)
  have hcodeS : Function.Injective (fun i : ↑s => code i.val) := hcode.comp Subtype.val_injective
  have hcoeff : p.coeff (code j.val) = c j := by
    simp only [p, Polynomial.coeff_add, Polynomial.finset_sum_coeff,
      Polynomial.coeff_C_ne_zero (hpos j.val).ne', Polynomial.coeff_monomial, zero_add]
    simp only [hcodeS.eq_iff]
    simp
  have hp0 : p ≠ 0 := by
    intro hz
    have hz' := congrArg (fun q : Polynomial ℝ => q.coeff (code j.val)) hz
    dsimp only at hz'
    rw [hcoeff, Polynomial.coeff_zero] at hz'
    exact hj hz'
  refine ⟨p, hp0, ?_⟩
  intro t x hx
  have heval : p.eval t = ∑ i : ↑s, c i * (h i.val + t ^ code i.val) := by
    simp only [p, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_finset_sum,
      Polynomial.eval_monomial, mul_add, Finset.sum_add_distrib]
  rw [heval]
  have hdot : (∑ i : ↑s, c i * dot (a i.val) x) = 0 := by
    rw [← dot_fintype_sum_smul, hrel]
    simp [dot]
  calc (∑ i : ↑s, c i * (h i.val + t ^ code i.val)) = ∑ i : ↑s, c i * dot (a i.val) x := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hx i.val i.property]
    _ = 0 := hdot

/-- Arbitrarily small strictly outward height changes can be chosen in
actual general position; no density or nondegeneracy certificate is assumed. -/
theorem exists_outward_generic_heights (a : ι → V n) (h : ι → ℝ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ h' : ι → ℝ, (∀ i, h i < h' i ∧ h' i < h i + δ) ∧ GeneralPositionHeights a h' := by
  classical
  let e := Fintype.equivFin ι
  let code : ι → ℕ := fun i => (e i).val + 1
  have hcode : Function.Injective code := by
    intro i j hij
    apply e.injective
    apply Fin.ext
    dsimp [code] at hij
    omega
  have hcodepos : ∀ i, 0 < code i := by intro i; dsimp [code]; omega
  let S := (Finset.univ : Finset ι).powerset.filter (fun s => s.card = n + 1)
  have hex : ∀ s : ↑S, ∃ p : Polynomial ℝ, p ≠ 0 ∧ ∀ t : ℝ, ∀ x : V n,
      (∀ i ∈ s.val, dot (a i) x = h i + t ^ code i) → p.eval t = 0 := by
    intro s
    have hs := (Finset.mem_filter.mp s.property).2
    exact exists_degeneracy_polynomial a h code hcode hcodepos s.val (by omega)
  choose p hp0 hpeval using hex
  let bad : Finset ℝ := Finset.univ.biUnion (fun s : ↑S => (p s).roots.toFinset)
  obtain ⟨t, ht, htbad⟩ := (Set.Ioo_infinite (lt_min hδ zero_lt_one)).exists_notMem_finite bad.finite_toSet
  have htpos : 0 < t := ht.1
  have htδ : t < δ := ht.2.trans_le (min_le_left _ _)
  have ht1 : t < 1 := ht.2.trans_le (min_le_right _ _)
  have havoid : ∀ s : ↑S, (p s).eval t ≠ 0 := by
    intro s hzero
    apply htbad
    exact Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _,
      Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (hp0 s)).mpr hzero)⟩
  let h' : ι → ℝ := fun i => h i + t ^ code i
  refine ⟨h', ?_, ?_⟩
  · intro i
    have hp : 0 < t ^ code i := pow_pos htpos _
    have hle : t ^ code i ≤ t := pow_le_of_le_one htpos.le ht1.le (hcodepos i).ne'
    exact ⟨by dsimp [h']; linarith, by dsimp [h']; linarith⟩
  · intro x _
    by_contra hn
    have hcard : n + 1 ≤ (activeConstraints a h' x).card := by omega
    obtain ⟨s, hs, hsn⟩ := Finset.exists_subset_card_eq hcard
    have hsS : s ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hsn⟩
    apply havoid ⟨s, hsS⟩
    apply hpeval ⟨s, hsS⟩ t x
    intro i hi
    exact (mem_activeConstraints a h' x i).mp (hs hi)

end
end Paper17
