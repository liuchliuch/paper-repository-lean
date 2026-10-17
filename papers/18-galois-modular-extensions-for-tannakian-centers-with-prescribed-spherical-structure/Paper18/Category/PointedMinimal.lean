import Paper18.Category.PointedCentralizer
import Paper18.Category.PointedCanonicalTwist

noncomputable section

open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators

namespace Paper18.Category.AppendixBPointed

lemma ambient_fpdim_simple (a : Paper18.PointedA) :
    (PointedVec.skeleton Paper18.PointedA).fusionBasis.fpdim a = 1 := by
  have h := (PointedVec.pivotalStructure Paper18.PointedA).rightDim_simple_eq_fpdim
    (PointedVec.skeleton Paper18.PointedA)
    (PointedVec.pivotalStructure_positive Paper18.PointedA) a
  change (PointedVec.pivotalStructure Paper18.PointedA).rightDim
    (PointedVec.simpleObject Paper18.PointedA a) = _ at h
  rw [PointedVec.pivotalStructure_rightDim_simple] at h
  have hr := congrArg Complex.re h
  simpa using hr.symm

lemma b_fpdim_simple (i : {a : Paper18.PointedA //
    PointedVec.simpleObject Paper18.PointedA a ∈ centralizer centralizerSet}) :
    bSkeleton.fusionBasis.fpdim i = 1 := by
  have h := bSkeleton.fpdim_map (PointedVec.skeleton Paper18.PointedA)
    BInclusion (bSkeleton.simpleObject i)
  change (PointedVec.skeleton Paper18.PointedA).fpdim
      ((PointedVec.skeleton Paper18.PointedA).simpleObject i.val) =
    bSkeleton.fpdim (bSkeleton.simpleObject i) at h
  rw [bSkeleton.fpdim_simple, FiniteSemisimpleSkeleton.fpdim_simple,
    ambient_fpdim_simple] at h
  exact h.symm

theorem ambient_totalFPdim :
    (PointedVec.skeleton Paper18.PointedA).fusionBasis.totalFPdim = 16 := by
  simp [Paper18.FusionBasis.totalFPdim, ambient_fpdim_simple,
    Paper18.PointedA, Fintype.card_prod]

lemma two_torsion_four (b : ZMod 4) (hb : (2 : ℕ) • b = 0) : b = 0 ∨ b = 2 := by
  have hb' : (2 : ZMod 4) * b = 0 := by
    simpa only [nsmul_eq_mul, Nat.cast_ofNat] using hb
  have hmod : (2 * b.val) % 4 = 0 := by
    have h := congrArg ZMod.val hb'
    simpa only [ZMod.val_mul, Paper18.ZMod.val_two_four, ZMod.val_zero] using h
  have hv : b.val = 0 ∨ b.val = 2 := by
    have hlt := ZMod.val_lt b
    omega
  rcases hv with hv | hv
  · exact Or.inl ((ZMod.val_eq_zero b).mp hv)
  · exact Or.inr (ZMod.val_injective 4 (hv.trans Paper18.ZMod.val_two_four.symm))

def evenSecondEquiv : evenSecond ≃ ZMod 4 × Bool where
  toFun a := (a.val.1, if a.val.2 = 0 then false else true)
  invFun p := ⟨(p.1, if p.2 then 2 else 0), by
    change (2 : ℕ) • (if p.2 then (2 : ZMod 4) else 0) = 0
    cases p.2 <;> decide⟩
  left_inv a := by
    apply Subtype.ext
    dsimp
    have ha : a.val.2 = 0 ∨ a.val.2 = 2 := two_torsion_four _ a.property
    rcases ha with ha | ha
    · simp [ha]
      exact Prod.ext rfl ha.symm
    · simp [ha, show (2 : ZMod 4) ≠ 0 by decide]
      exact Prod.ext rfl ha.symm
  right_inv p := by
    rcases p with ⟨x, b⟩
    cases b <;> simp [show (2 : ZMod 4) ≠ 0 by decide]

lemma evenSecond_card : Fintype.card evenSecond = 8 := by
  rw [Fintype.card_congr evenSecondEquiv, Fintype.card_prod]
  norm_num

theorem b_totalFPdim : bSkeleton.fusionBasis.totalFPdim = 8 := by
  simp only [Paper18.FusionBasis.totalFPdim, b_fpdim_simple, one_pow,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  change (Fintype.card {a : Paper18.PointedA //
    PointedVec.simpleObject Paper18.PointedA a ∈ centralizer centralizerSet} : ℝ) = 8
  rw [Fintype.card_congr bLabelEquivEven, evenSecond_card]
  norm_num

/-- The actual Müger center of the centralizer category. -/
abbrev BCenter := CentralizerCategory (Set.univ : Set B)

instance bCenterFiniteDimensionalHom (X Y : BCenter) : FiniteDimensional ℂ (X ⟶ Y) :=
  inferInstanceAs (FiniteDimensional ℂ (X.obj ⟶ Y.obj))

instance bCenterHasKernels : HasKernels BCenter :=
  bSkeleton.fullSubcategoryHasKernels (centralizerProperty (Set.univ : Set B))

instance bCenterRightRigid : RightRigidCategory BCenter :=
  bSkeleton.fullSubcategoryRightRigid (centralizerProperty (Set.univ : Set B))

instance bCenterSimpleUnit : Simple (𝟙_ BCenter) :=
  bSkeleton.fullSubcategorySimpleUnit (centralizerProperty (Set.univ : Set B))

abbrev bCenterSkeleton := bSkeleton.centralizerSkeleton (Set.univ : Set B)

abbrev BLabel := {a : Paper18.PointedA //
  PointedVec.simpleObject Paper18.PointedA a ∈ centralizer centralizerSet}

abbrev BCenterLabel := {i : BLabel // bSkeleton.simpleObject i ∈ mugerCenter}

lemma bCenterLabel_zero_or_f (i : BCenterLabel) : i.val.val = 0 ∨ i.val.val = Paper18.f :=
  (bSimple_transparent_iff (bLabelEquivEven i.val)).mp i.property

def bCenterLabelZero : BCenterLabel :=
  ⟨⟨0, (simple_mem_B_iff 0).mpr (by simp)⟩,
    (bSimple_transparent_iff ⟨0, by change (2 : ℕ) • (0 : ZMod 4) = 0; simp⟩).mpr
      (Or.inl rfl)⟩

def bCenterLabelF : BCenterLabel :=
  ⟨⟨Paper18.f, (simple_mem_B_iff Paper18.f).mpr (by simp [Paper18.f])⟩,
    (bSimple_transparent_iff ⟨Paper18.f, by change (2 : ℕ) • (0 : ZMod 4) = 0; simp⟩).mpr
      (Or.inr rfl)⟩

/-- The actual center has exactly the two simple representatives labelled
by zero and the distinguished degree. -/
def bCenterLabelEquivBool : BCenterLabel ≃ Bool where
  toFun i := if i.val.val = 0 then false else true
  invFun b := if b then bCenterLabelF else bCenterLabelZero
  left_inv i := by
    apply Subtype.ext
    apply Subtype.ext
    rcases bCenterLabel_zero_or_f i with hi | hi
    · simp [hi, bCenterLabelZero]
    · simp [hi, bCenterLabelF, show Paper18.f ≠ 0 by decide]
  right_inv b := by
    cases b <;> simp [bCenterLabelZero, bCenterLabelF, show Paper18.f ≠ 0 by decide]

lemma bCenter_fpdim_simple (i : BCenterLabel) :
    bCenterSkeleton.fusionBasis.fpdim i = 1 := by
  have h := bCenterSkeleton.fpdim_map bSkeleton
    (centralizerInclusion (Set.univ : Set B)) (bCenterSkeleton.simpleObject i)
  change bSkeleton.fpdim (bSkeleton.simpleObject i.val) =
    bCenterSkeleton.fpdim (bCenterSkeleton.simpleObject i) at h
  rw [bSkeleton.fpdim_simple, bCenterSkeleton.fpdim_simple, b_fpdim_simple] at h
  exact h.symm

theorem bCenter_totalFPdim : bCenterSkeleton.fusionBasis.totalFPdim = 2 := by
  simp only [Paper18.FusionBasis.totalFPdim, bCenter_fpdim_simple, one_pow,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  change (Fintype.card BCenterLabel : ℝ) = 2
  rw [Fintype.card_congr bCenterLabelEquivBool, Fintype.card_bool]
  norm_num

/-- The fixed actual modular ambient category has exactly the dimension
required of a minimal nondegenerate extension of its centralizer. -/
theorem minimal_extension_dimension :
    (PointedVec.skeleton Paper18.PointedA).fusionBasis.totalFPdim =
      bSkeleton.fusionBasis.totalFPdim * bCenterSkeleton.fusionBasis.totalFPdim := by
  rw [ambient_totalFPdim, b_totalFPdim, bCenter_totalFPdim]
  norm_num

end Paper18.Category.AppendixBPointed
