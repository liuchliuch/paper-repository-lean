import Paper28.SphericalSimplexPatch
import Paper28.NormalizedAffineMaps

/-! A unit vector in a finite nonnegative spherical cone is in its actual
normalized standard-simplex parameterization. This bridges closed carrier
cells and the source geodesic simplex objects without a cone-membership input. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
open scoped Classical
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem normalized_nonnegative_sum_mem_sphericalSimplexPatch {k : ℕ}
    (q : Fin (k+1) → H) (a : Fin (k+1) → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hUnit : ‖sphericalNormalize (∑ i, a i • q i)‖ = 1) :
    sphericalNormalize (∑ i, a i • q i) ∈ sphericalSimplexPatch q := by
  have hPos : ∃ i, 0 < a i := by
    by_contra hn
    push_neg at hn
    have hZero : ∀ i, a i = 0 := fun i => le_antisymm (hn i) (ha i)
    have hSum : (∑ i, a i • q i) = 0 := by simp only [hZero,zero_smul,Finset.sum_const_zero]
    simp [hSum,sphericalNormalize] at hUnit
  let S : ℝ := ∑ i, a i
  have hS : 0 < S := Finset.sum_pos' (fun i _ => ha i) (by
    obtain ⟨i,hi⟩ := hPos
    exact ⟨i,Finset.mem_univ _,hi⟩)
  let t : stdSimplex ℝ (Fin (k+1)) := ⟨fun i => S⁻¹*a i,fun i => mul_nonneg (inv_nonneg.mpr hS.le) (ha i),by
    rw [← Finset.mul_sum]
    exact inv_mul_cancel₀ (ne_of_gt hS)⟩
  have ht : sphericalBarycentricVector q t = S⁻¹ • (∑ i, a i • q i) := by
    change (∑ i, (S⁻¹*a i) • q i) = _
    rw [Finset.smul_sum]
    simp only [smul_smul]
  refine ⟨t,?_⟩
  change sphericalNormalize (sphericalBarycentricVector q t) = _
  rw [ht,sphericalNormalize_pos_smul _ (inv_pos.mpr hS)]

variable {α : Type*} [DecidableEq α]

theorem nonempty_finset_indexing (C : Finset α) (hC : C.Nonempty) :
    ∃ k : ℕ, ∃ σ : Fin (k+1) → α, Function.Injective σ ∧ Finset.univ.image σ = C := by
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (Finset.card_pos.mpr hC))
  let e : Fin (k+1) ≃ C := Fintype.equivOfCardEq (by simpa only [Fintype.card_fin,Fintype.card_coe] using hk.symm)
  let σ : Fin (k+1) → α := fun i => (e i).val
  refine ⟨k,σ,?_,?_⟩
  · intro i j he
    exact e.injective (Subtype.ext he)
  · apply Finset.ext
    intro F
    constructor
    · intro hF
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hF
      exact hi ▸ (e i).property
    · intro hF
      exact Finset.mem_image.mpr ⟨e.symm ⟨F,hF⟩,Finset.mem_univ _,congrArg Subtype.val (e.apply_symm_apply ⟨F,hF⟩)⟩

end Paper28
