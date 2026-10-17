import Paper18.Category.PointedMinimal

noncomputable section

open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits

namespace Paper18.Category.AppendixBPointed

/-- Every actual object of the center is supported only in degrees zero
and `(2,0)`, as follows from its actual transparent simple constituents. -/
theorem bCenter_fiber_isZero (X : BCenter) (a : Paper18.PointedA)
    (ha0 : a ≠ 0) (haf : a ≠ Paper18.f) : IsZero (X.obj.obj a) := by
  by_cases ha : (2 : ℕ) • a.2 = 0
  · apply (IsZero.iff_id_eq_zero (X.obj.obj a)).mpr
    apply FGModuleCat.hom_ext
    ext v
    change v = 0
    by_contra hv
    let d : evenSecond := ⟨a, ha⟩
    let f : bSimple d ⟶ X.obj := PointedVec.fromSimple a X.obj.obj v
    have hf : f ≠ 0 := PointedVec.fromSimple_ne_zero a X.obj.obj v hv
    let i : BLabel := ⟨a, (simple_mem_B_iff a).mpr ha⟩
    have hp : 0 < bSkeleton.multiplicity X.obj i :=
      Module.finrank_pos_iff_exists_ne_zero.mpr ⟨f, hf⟩
    have hs := centralizer_retract (bSkeleton.retractOfMultiplicityPos X.obj i hp) X.property
    have ht : bSimple d ∈ mugerCenter := hs
    rcases (bSimple_transparent_iff d).mp ht with ht | ht
    · exact ha0 ht
    · exact haf ht
  · exact (mem_B_iff_fiber_isZero X.obj.obj).mp X.obj.property a ha

lemma centralizes_of_tensor_fiber_zero (X Y : Vec)
    (h : ∀ i j : Paper18.PointedA, Paper18.monodromy i j ≠ 1 → IsZero (X i ⊗ Y j)) :
    Centralizes X Y := by
  apply GradedObject.hom_ext
  intro k
  apply GradedObject.Monoidal.tensorObj_ext
  intro i j hij
  change GradedObject.Monoidal.ιTensorObj X Y i j k hij ≫
      ((β_ X Y).hom k ≫ (β_ Y X).hom k) =
    GradedObject.Monoidal.ιTensorObj X Y i j k hij ≫ 𝟙 _
  by_cases hm : Paper18.monodromy i j = 1
  · rw [inclusion_monodromy, hm, one_smul, Category.comp_id]
  · exact (h i j hm).eq_of_src _ _

lemma centerSupport_centralizes_simple (X : Vec)
    (h : ∀ a : Paper18.PointedA, a ≠ 0 → a ≠ Paper18.f → IsZero (X a))
    (b : evenSecond) : Centralizes X (PointedVec.simpleObject Paper18.PointedA b) := by
  apply centralizes_of_tensor_fiber_zero
  intro i j hm
  by_cases hj : j = b.val
  · subst j
    by_cases hi : i = 0 ∨ i = Paper18.f
    · exact False.elim (hm (((even_annihilator i).mpr hi) b))
    · push_neg at hi
      exact (tensorRight ((PointedVec.simpleObject Paper18.PointedA b) b)).map_isZero
        (h i hi.1 hi.2)
  · exact (tensorLeft (X i)).map_isZero
      (PointedVec.simpleFiber_isZero Paper18.PointedA b.val j hj)

/-- Package any actual graded vector space supported in degrees zero and
`(2,0)` as an actual object of the Müger center. The underlying graded
vector space is unchanged. -/
def ofCenterSupport (X : Vec)
    (h : ∀ a : Paper18.PointedA, a ≠ 0 → a ≠ Paper18.f → IsZero (X a)) : BCenter := by
  have hB : X ∈ centralizer centralizerSet := by
    apply (mem_B_iff_fiber_isZero X).mpr
    intro a ha
    apply h a
    · intro ha0
      exact ha (by simp [ha0])
    · intro haf
      exact ha (by simp [haf, Paper18.f])
  let Y : B := ⟨X, hB⟩
  refine ⟨Y, ?_⟩
  apply (mem_mugerCenter_iff_simples bSkeleton Y).mpr
  intro i
  apply (centralizes_map_iff BInclusion Y (bSkeleton.simpleObject i)).mp
  exact centerSupport_centralizes_simple X h (bLabelEquivEven i)

@[simp] lemma ofCenterSupport_obj (X : Vec)
    (h : ∀ a : Paper18.PointedA, a ≠ 0 → a ≠ Paper18.f → IsZero (X a)) :
    (ofCenterSupport X h).obj.obj = X := rfl

end Paper18.Category.AppendixBPointed
