import Paper18.Category.PointedRepEquivalenceBasic

/-! # Fullness of the actual center sign-representation functor -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
namespace Paper18.Category.AppendixBPointed
open RepresentationZ2

@[reassoc (attr := simp)]
lemma totalParity_π (X : BCenter) (a : Paper18.PointedA) :
    totalParity X ≫ biproduct.π X.obj.obj a =
      centerParityChar a • biproduct.π X.obj.obj a := by
  change biproduct.map (PointedVec.degreeMap centerParityChar X.obj.obj) ≫
    biproduct.π X.obj.obj a = _
  rw [biproduct.map_π]
  simp

/-- Intertwiners have homogeneous matrix blocks of equal parity. -/
lemma centerRep_intertwiner_block {X Y : BCenter}
    (f : centerRepFunctor.obj X ⟶ centerRepFunctor.obj Y) (a b : Paper18.PointedA) :
    centerParityChar a • (biproduct.ι X.obj.obj a ≫ f.hom ≫ biproduct.π Y.obj.obj b) =
      centerParityChar b • (biproduct.ι X.obj.obj a ≫ f.hom ≫ biproduct.π Y.obj.obj b) := by
  have hf : totalParity X ≫ f.hom = f.hom ≫ totalParity Y := by
    simpa [centerRepFunctor, actionOfInvolution] using f.comm generator
  have h := congrArg
    (fun k => biproduct.ι X.obj.obj a ≫ k ≫ biproduct.π Y.obj.obj b) hf
  simp only [Category.assoc] at h
  erw [fiber_totalParity_assoc] at h
  rw [totalParity_π] at h
  simpa only [Linear.smul_comp, Category.assoc, Linear.comp_smul] using h

/-- Distinct homogeneous blocks of an actual intertwiner vanish, using both
the center support theorem and separation by the actual parity character. -/
lemma centerRep_intertwiner_offDiagonal {X Y : BCenter}
    (f : centerRepFunctor.obj X ⟶ centerRepFunctor.obj Y)
    (a b : Paper18.PointedA) (hab : a ≠ b) :
    biproduct.ι X.obj.obj a ≫ f.hom ≫ biproduct.π Y.obj.obj b = 0 := by
  by_cases ha0 : a = 0
  · subst a
    by_cases hbf : b = Paper18.f
    · subst b
      by_contra hn
      have h := (smul_left_injective ℂ hn) (centerRep_intertwiner_block f 0 Paper18.f)
      norm_num at h
    · have hb0 : b ≠ 0 := Ne.symm hab
      exact (bCenter_fiber_isZero Y b hb0 hbf).eq_of_tgt _ _
  · by_cases haf : a = Paper18.f
    · subst a
      by_cases hb0 : b = 0
      · subst b
        by_contra hn
        have h := (smul_left_injective ℂ hn) (centerRep_intertwiner_block f Paper18.f 0)
        norm_num at h
      · exact (bCenter_fiber_isZero Y b hb0 (Ne.symm hab)).eq_of_tgt _ _
    · exact (bCenter_fiber_isZero X a ha0 haf).eq_of_src _ _

/-- Recover the actual homogeneous morphism from an intertwiner. -/
def intertwinerToCenter {X Y : BCenter}
    (f : centerRepFunctor.obj X ⟶ centerRepFunctor.obj Y) : X ⟶ Y := fun a =>
  biproduct.ι X.obj.obj a ≫ f.hom ≫ biproduct.π Y.obj.obj a

lemma centerRep_map_intertwinerToCenter {X Y : BCenter}
    (f : centerRepFunctor.obj X ⟶ centerRepFunctor.obj Y) :
    centerRepFunctor.map (intertwinerToCenter f) = f := by
  apply Action.Hom.ext
  change biproduct.map (intertwinerToCenter f) = f.hom
  apply biproduct.hom_ext'
  intro a
  apply biproduct.hom_ext
  intro b
  by_cases hab : a = b
  · subst b
    simp [intertwinerToCenter, Category.assoc]
  · simp only [Category.assoc]
    rw [centerRep_intertwiner_offDiagonal f a b hab]
    simp [hab]

instance centerRepFunctor_full : centerRepFunctor.Full where
  map_surjective f := ⟨intertwinerToCenter f, centerRep_map_intertwinerToCenter f⟩

end Paper18.Category.AppendixBPointed
