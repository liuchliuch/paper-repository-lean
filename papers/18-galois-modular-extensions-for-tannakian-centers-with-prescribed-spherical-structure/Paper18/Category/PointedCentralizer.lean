import Paper18.Category.PointedAppendixB
import Paper18.Category.PointedTensorCharacters
import Paper18.Category.CentralizerFusion

noncomputable section

open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits

namespace Paper18.Category.AppendixBPointed

lemma fourthRoot_eq_one_iff (a : ZMod 4) : fourthRoot a = 1 ↔ a = 0 := by
  rw [fourthRoot_apply, Paper18.Complex.I_pow_eq_one_iff]
  constructor
  · intro h
    exact (ZMod.val_eq_zero a).mp (Nat.eq_zero_of_dvd_of_lt h (ZMod.val_lt a))
  · intro h
    simp [h]

lemma monodromy_eq_fourthRoot (a b : Paper18.PointedA) :
    Paper18.monodromy a b = fourthRoot (a.1 * b.2 + b.1 * a.2) := by
  rw [← braidingScalar_monodromy, fourthRoot.map_add_eq_mul]
  rfl

lemma monodromy_f_iff (a : Paper18.PointedA) :
    Paper18.monodromy a Paper18.f = 1 ↔ (2 : ℕ) • a.2 = 0 := by
  rw [monodromy_eq_fourthRoot, fourthRoot_eq_one_iff]
  simp [Paper18.f, nsmul_eq_mul]

/-- The actual distinguished homogeneous object used to form the
centralizer, with degree `(2,0)`. -/
def distinguished : Vec := PointedVec.simpleObject Paper18.PointedA Paper18.f

def centralizerSet : Set Vec := {distinguished}

/-- The actual braided full fusion subcategory centralizing the
distinguished object. -/
abbrev B := CentralizerCategory centralizerSet

abbrev BInclusion : B ⥤ Vec := centralizerInclusion centralizerSet

instance bFiniteDimensionalHom (X Y : B) : FiniteDimensional ℂ (X ⟶ Y) :=
  inferInstanceAs (FiniteDimensional ℂ (X.obj ⟶ Y.obj))

instance bHasKernels : HasKernels B :=
  (PointedVec.skeleton Paper18.PointedA).fullSubcategoryHasKernels
    (centralizerProperty centralizerSet)

instance bRightRigid : RightRigidCategory B :=
  (PointedVec.skeleton Paper18.PointedA).fullSubcategoryRightRigid
    (centralizerProperty centralizerSet)

instance bSimpleUnit : Simple (𝟙_ B) :=
  (PointedVec.skeleton Paper18.PointedA).fullSubcategorySimpleUnit
    (centralizerProperty centralizerSet)

abbrev bSkeleton :=
  (PointedVec.skeleton Paper18.PointedA).centralizerSkeleton centralizerSet

/-- The simple labels of the actual centralizer are exactly the degrees
with even second coordinate. -/
lemma simple_mem_B_iff (a : Paper18.PointedA) :
    PointedVec.simpleObject Paper18.PointedA a ∈ centralizer centralizerSet ↔
      (2 : ℕ) • a.2 = 0 := by
  change (∀ Y ∈ ({distinguished} : Set Vec),
    Centralizes (PointedVec.simpleObject Paper18.PointedA a) Y) ↔ _
  simp only [Set.mem_singleton_iff, forall_eq]
  exact (centralizes_simple_iff a Paper18.f).trans (monodromy_f_iff a)

/-- The actual centralizer consists precisely of the graded vector spaces
whose odd-second-coordinate homogeneous components vanish. -/
theorem mem_B_iff_fiber_isZero (X : Vec) :
    X ∈ centralizer centralizerSet ↔
      ∀ a : Paper18.PointedA, (2 : ℕ) • a.2 ≠ 0 → IsZero (X a) := by
  constructor
  · intro hX a ha
    apply (IsZero.iff_id_eq_zero (X a)).mpr
    apply FGModuleCat.hom_ext
    ext v
    change v = 0
    by_contra hv
    let f := PointedVec.fromSimple a X v
    have hf : f ≠ 0 := PointedVec.fromSimple_ne_zero a X v hv
    have hp : 0 < (PointedVec.skeleton Paper18.PointedA).multiplicity X a :=
      Module.finrank_pos_iff_exists_ne_zero.mpr ⟨f, hf⟩
    have hs := centralizer_retract
      ((PointedVec.skeleton Paper18.PointedA).retractOfMultiplicityPos X a hp) hX
    exact ha ((simple_mem_B_iff a).mp hs)
  · intro hX Y hY
    have hY' : Y = distinguished := hY
    subst Y
    apply GradedObject.hom_ext
    intro k
    apply GradedObject.Monoidal.tensorObj_ext
    intro a b hab
    change GradedObject.Monoidal.ιTensorObj X distinguished a b k hab ≫
        ((β_ X distinguished).hom k ≫ (β_ distinguished X).hom k) =
      GradedObject.Monoidal.ιTensorObj X distinguished a b k hab ≫ 𝟙 _
    by_cases hb : b = Paper18.f
    · subst b
      by_cases ha : (2 : ℕ) • a.2 = 0
      · rw [inclusion_monodromy, (monodromy_f_iff a).mpr ha, one_smul, Category.comp_id]
      · exact ((tensorRight (distinguished Paper18.f)).map_isZero (hX a ha)).eq_of_src _ _
    · exact ((tensorLeft (X a)).map_isZero
        (PointedVec.simpleFiber_isZero _ Paper18.f b hb)).eq_of_src _ _

/-- A canonical actual homogeneous object of the centralizer for each
even-second-coordinate degree. -/
def bSimple (a : evenSecond) : B :=
  ⟨PointedVec.simpleObject Paper18.PointedA a, (simple_mem_B_iff a).mpr a.property⟩

def bLabelEquivEven :
    {a : Paper18.PointedA // PointedVec.simpleObject Paper18.PointedA a ∈
      centralizer centralizerSet} ≃ evenSecond where
  toFun i := ⟨i.val, (simple_mem_B_iff i.val).mp i.property⟩
  invFun a := ⟨a.val, (simple_mem_B_iff a.val).mpr a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance bSimple_simple (a : evenSecond) : Simple (bSimple a) := by
  letI := PointedVec.simple_simpleObject (A := Paper18.PointedA) a.val
  exact (PointedVec.skeleton Paper18.PointedA).simple_in_fullSubcategory
    (centralizerProperty centralizerSet) _ _

lemma even_annihilator (a : Paper18.PointedA) :
    (∀ b : evenSecond, Paper18.monodromy a b = 1) ↔ a = 0 ∨ a = Paper18.f := by
  constructor
  · intro h
    have h10 := h ⟨(1, 0), by change (2 : ℕ) • (0 : ZMod 4) = 0; simp⟩
    have h02 := h ⟨(0, 2), by change (2 : ℕ) • (2 : ZMod 4) = 0; decide⟩
    rw [monodromy_eq_fourthRoot, fourthRoot_eq_one_iff] at h10 h02
    rcases a with ⟨x, y⟩
    have hy : y = 0 := by simpa using h10
    have hx : (2 : ZMod 4) * x = 0 := by simpa [mul_comm] using h02
    have hxm : (2 * x.val) % 4 = 0 := by
      have hv := congrArg ZMod.val hx
      simpa only [ZMod.val_mul, Paper18.ZMod.val_two_four, ZMod.val_zero] using hv
    have hxv : x.val = 0 ∨ x.val = 2 := by
      have hlt := ZMod.val_lt x
      omega
    have hx' : x = 0 ∨ x = 2 := by
      rcases hxv with hv | hv
      · exact Or.inl ((ZMod.val_eq_zero x).mp hv)
      · exact Or.inr (ZMod.val_injective 4 (hv.trans Paper18.ZMod.val_two_four.symm))
    rcases hx' with rfl | rfl
    · exact Or.inl (Prod.ext rfl hy)
    · exact Or.inr (Prod.ext rfl hy)
  · rintro (rfl | rfl) b
    · simp [monodromy_eq_fourthRoot]
    · rw [monodromy_eq_fourthRoot]
      have hb' : (2 : ℕ) • b.val.2 = 0 := b.property
      have hb : (2 : ZMod 4) * b.val.2 = 0 := by
        simpa only [nsmul_eq_mul, Nat.cast_ofNat] using hb'
      simp [Paper18.f, hb]

/-- The only transparent homogeneous simples of the actual centralizer
have degree zero or the distinguished degree `(2,0)`. -/
lemma bSimple_transparent_iff (a : evenSecond) :
    bSimple a ∈ mugerCenter ↔ a.val = 0 ∨ a.val = Paper18.f := by
  rw [← even_annihilator]
  constructor
  · intro h b
    have hc := h (bSimple b) (Set.mem_univ _)
    have ha := (centralizes_map_iff BInclusion (bSimple a) (bSimple b)).mpr hc
    exact centralizes_simple_implies_monodromy a b ha
  · intro h
    apply (mem_mugerCenter_iff_simples bSkeleton (bSimple a)).mpr
    intro i
    let b : evenSecond := ⟨i.val, (simple_mem_B_iff i.val).mp i.property⟩
    apply (centralizes_map_iff BInclusion (bSimple a) (bSkeleton.simpleObject i)).mp
    exact centralizes_simple_of_monodromy a b (h b)

end Paper18.Category.AppendixBPointed
