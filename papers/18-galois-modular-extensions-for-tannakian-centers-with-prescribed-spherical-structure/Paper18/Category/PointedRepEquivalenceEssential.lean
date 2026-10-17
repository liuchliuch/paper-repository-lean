import Paper18.Category.PointedRepEquivalenceFull

/-! # Actual eigenspace realizations of all C₂ representations in the center -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped ZeroObject
namespace Paper18.Category.AppendixBPointed
open RepresentationZ2

lemma center_total_resolution (X : BCenter) :
    biproduct.π X.obj.obj 0 ≫ biproduct.ι X.obj.obj 0 +
      biproduct.π X.obj.obj Paper18.f ≫ biproduct.ι X.obj.obj Paper18.f =
        𝟙 (centerFiberFunctor.obj X) := by
  apply biproduct.hom_ext'
  intro a
  by_cases ha0 : a = 0
  · subst a
    simp [show (0 : Paper18.PointedA) ≠ Paper18.f by decide]
    rfl
  · by_cases haf : a = Paper18.f
    · subst a
      simp [show Paper18.f ≠ (0 : Paper18.PointedA) by decide]
      rfl
    · exact (bCenter_fiber_isZero X a ha0 haf).eq_of_src _ _

@[simp] lemma center_total_projection_inclusion (X : BCenter) (a : Paper18.PointedA)
    (x : X.obj.obj a) :
    (biproduct.π X.obj.obj a).hom ((biproduct.ι X.obj.obj a).hom x) = x :=
  LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (biproduct.ι_π_self X.obj.obj a)) x

@[simp] lemma center_total_projection_inclusion_ne (X : BCenter) (a b : Paper18.PointedA)
    (hab : a ≠ b) (x : X.obj.obj a) :
    (biproduct.π X.obj.obj b).hom ((biproduct.ι X.obj.obj a).hom x) = 0 :=
  LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (biproduct.ι_π_ne X.obj.obj hab)) x

def centerToBinary (X : BCenter) :
    centerFiberFunctor.obj X →ₗ[ℂ] (X.obj.obj 0 × X.obj.obj Paper18.f) :=
  (biproduct.π X.obj.obj 0).hom.prod (biproduct.π X.obj.obj Paper18.f).hom

def binaryToCenter (X : BCenter) :
    (X.obj.obj 0 × X.obj.obj Paper18.f) →ₗ[ℂ] centerFiberFunctor.obj X :=
  LinearMap.coprod (biproduct.ι X.obj.obj 0).hom (biproduct.ι X.obj.obj Paper18.f).hom

/-- Actual total vectors split into their two supported homogeneous components. -/
def centerTotalEquiv (X : BCenter) :
    centerFiberFunctor.obj X ≃ₗ[ℂ] (X.obj.obj 0 × X.obj.obj Paper18.f) where
  toLinearMap := centerToBinary X
  invFun := binaryToCenter X
  left_inv v := LinearMap.congr_fun
    (congrArg ModuleCat.Hom.hom (center_total_resolution X)) v
  right_inv v := by
    apply Prod.ext
    · change (biproduct.π X.obj.obj 0).hom
        ((biproduct.ι X.obj.obj 0).hom v.1 +
          (biproduct.ι X.obj.obj Paper18.f).hom v.2) = v.1
      rw [map_add]
      erw [center_total_projection_inclusion X 0,
        center_total_projection_inclusion_ne X Paper18.f 0 (by decide)]
      exact add_zero _
    · change (biproduct.π X.obj.obj Paper18.f).hom
        ((biproduct.ι X.obj.obj 0).hom v.1 +
          (biproduct.ι X.obj.obj Paper18.f).hom v.2) = v.2
      rw [map_add]
      erw [center_total_projection_inclusion_ne X 0 Paper18.f (by decide),
        center_total_projection_inclusion X Paper18.f]
      exact zero_add _

/-- The actual parity involution acts by the two signs in those coordinates. -/
lemma centerTotalEquiv_parity (X : BCenter) (v : centerFiberFunctor.obj X) :
    centerTotalEquiv X ((totalParity X).hom v) =
      ((centerTotalEquiv X v).1, -(centerTotalEquiv X v).2) := by
  apply Prod.ext
  · have h := LinearMap.congr_fun
      (congrArg ModuleCat.Hom.hom (totalParity_π X 0)) v
    change (biproduct.π X.obj.obj 0).hom ((totalParity X).hom v) =
      centerParityChar 0 • (biproduct.π X.obj.obj 0).hom v at h
    rw [centerParityChar_zero, one_smul] at h
    exact h
  · have h := LinearMap.congr_fun
      (congrArg ModuleCat.Hom.hom (totalParity_π X Paper18.f)) v
    change (biproduct.π X.obj.obj Paper18.f).hom ((totalParity X).hom v) =
      centerParityChar Paper18.f • (biproduct.π X.obj.obj Paper18.f).hom v at h
    rw [centerParityChar_f, neg_one_smul] at h
    exact h

/-- The concrete graded object with positive eigenspace in degree zero and
negative eigenspace in degree `f`. -/
def eigenGrading (V : FDRep ℂ H) : Vec := fun a =>
  if a = 0 then FGModuleCat.of ℂ (plusSpace V)
  else if a = Paper18.f then FGModuleCat.of ℂ (minusSpace V)
  else 0

def eigenCenter (V : FDRep ℂ H) : BCenter :=
  ofCenterSupport (eigenGrading V) (fun a ha0 haf => by
    change IsZero (if a = 0 then FGModuleCat.of ℂ (plusSpace V)
      else if a = Paper18.f then FGModuleCat.of ℂ (minusSpace V) else 0)
    rw [if_neg ha0, if_neg haf]
    exact isZero_zero _)

def eigenFiberZeroIso (V : FDRep ℂ H) :
    (eigenCenter V).obj.obj 0 ≅ FGModuleCat.of ℂ (plusSpace V) :=
  eqToIso (by simp [eigenCenter, eigenGrading])

def eigenFiberFIso (V : FDRep ℂ H) :
    (eigenCenter V).obj.obj Paper18.f ≅ FGModuleCat.of ℂ (minusSpace V) :=
  eqToIso (by simp [eigenCenter, eigenGrading, show Paper18.f ≠ (0 : Paper18.PointedA) by decide])

/-- The concrete eigenspace decomposition gives the underlying vector-space
isomorphism of the desired representation isomorphism. -/
def eigenTotalEquiv (V : FDRep ℂ H) : centerFiberFunctor.obj (eigenCenter V) ≃ₗ[ℂ] V :=
  (centerTotalEquiv (eigenCenter V)).trans
    (((FGModuleCat.isoToLinearEquiv (eigenFiberZeroIso V)).prodCongr
      (FGModuleCat.isoToLinearEquiv (eigenFiberFIso V))).trans (eigenspaceEquiv V))

lemma eigenTotalEquiv_generator (V : FDRep ℂ H) (v : centerFiberFunctor.obj (eigenCenter V)) :
    eigenTotalEquiv V ((totalParity (eigenCenter V)).hom v) =
      V.ρ generator (eigenTotalEquiv V v) := by
  unfold eigenTotalEquiv
  rw [LinearEquiv.trans_apply, centerTotalEquiv_parity]
  simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, map_neg]
  exact (eigenspaceEquiv_generator V _).symm

/-- Every finite-dimensional C₂ representation is actually isomorphic to
the sign representation of its supported eigenspace grading. -/
def eigenRepresentationIso (V : FDRep ℂ H) : centerRepFunctor.obj (eigenCenter V) ≅ V :=
  Action.mkIso (eigenTotalEquiv V).toFGModuleCatIso (fun g => by
    rcases eq_one_or_generator g with rfl | rfl
    · simp
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      change eigenTotalEquiv V ((totalParity (eigenCenter V)).hom v) =
        V.ρ generator (eigenTotalEquiv V v)
      exact eigenTotalEquiv_generator V v)

instance centerRepFunctor_essSurj : centerRepFunctor.EssSurj where
  mem_essImage V := ⟨eigenCenter V, ⟨eigenRepresentationIso V⟩⟩

instance centerRepFunctor_isEquivalence : centerRepFunctor.IsEquivalence where

end Paper18.Category.AppendixBPointed
