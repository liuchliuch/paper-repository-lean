import Paper18.Category.PointedRepEquivalenceTotalMonoidal
import Paper18.Category.RepresentationZ2Action
import Paper18.Category.PointedSupport
import Paper18.Category.PointedCharacters

/-! # The actual sign representation of an Appendix B center object -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.Monoidal
namespace Paper18.Category.AppendixBPointed
open RepresentationZ2

/-- The first-coordinate fourth-root character separates the two center degrees. -/
def centerParityChar : AddChar Paper18.PointedA ℂ :=
  fourthRoot.compAddMonoidHom
    { toFun := Prod.fst
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

@[simp] lemma centerParityChar_zero : centerParityChar 0 = 1 :=
  centerParityChar.map_zero_eq_one

@[simp] lemma centerParityChar_f : centerParityChar Paper18.f = -1 := by
  change fourthRoot (2 : ZMod 4) = -1
  simp [fourthRoot_apply, Paper18.ZMod.val_two_four]

/-- The genuine tensor automorphism giving parity on the actual transparent center. -/
def centerParity : 𝟭 BCenter ≅ 𝟭 BCenter where
  hom :=
    { app X := PointedVec.degreeMap centerParityChar X.obj.obj
      naturality := fun {X Y} f => PointedVec.degreeMap_naturality _ f }
  inv :=
    { app X := PointedVec.degreeMap (fun a => (centerParityChar a)⁻¹) X.obj.obj
      naturality := fun {X Y} f => PointedVec.degreeMap_naturality _ f }
  hom_inv_id := by
    ext X
    exact (PointedVec.characterAutomorphism centerParityChar).hom_inv_id_app X.obj.obj
  inv_hom_id := by
    ext X
    exact (PointedVec.characterAutomorphism centerParityChar).inv_hom_id_app X.obj.obj

instance centerParity_monoidal : centerParity.hom.IsMonoidal where
  unit := by
    change 𝟙 _ ≫ PointedVec.degreeMap centerParityChar (𝟙_ Vec) = 𝟙 _
    rw [Category.id_comp, PointedVec.characterMap_unit]
  tensor X Y := by
    change 𝟙 _ ≫ PointedVec.degreeMap centerParityChar (X.obj.obj ⊗ Y.obj.obj) =
      (PointedVec.degreeMap centerParityChar X.obj.obj ⊗ₘ
        PointedVec.degreeMap centerParityChar Y.obj.obj) ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id, PointedVec.characterMap_tensor]

/-- Parity is actually involutive on every object, by the proved support theorem. -/
lemma centerParity_involutive (X : BCenter) :
    centerParity.hom.app X ≫ centerParity.hom.app X = 𝟙 X := by
  funext a
  change (centerParityChar a • 𝟙 (X.obj.obj a)) ≫
    (centerParityChar a • 𝟙 (X.obj.obj a)) = 𝟙 (X.obj.obj a)
  by_cases ha0 : a = 0
  · subst a
    simp
  · by_cases haf : a = Paper18.f
    · subst a
      simp
    · exact (bCenter_fiber_isZero X a ha0 haf).eq_of_src _ _

/-- The actual vector-space fiber functor on the transparent center. -/
def centerFiberFunctor : BCenter ⥤ FGModuleCat ℂ :=
  ((centralizerInclusion (Set.univ : Set B)) ⋙ BInclusion) ⋙ PointedVec.totalFunctor

instance centerFiberFunctor_additive : centerFiberFunctor.Additive := by
  unfold centerFiberFunctor
  infer_instance

instance centerFiberFunctor_linear : centerFiberFunctor.Linear ℂ := by
  unfold centerFiberFunctor
  infer_instance

instance centerFiberFunctor_faithful : centerFiberFunctor.Faithful := by
  unfold centerFiberFunctor
  infer_instance

/-- Its strong tensor structure is the proved convolution totalization structure. -/
def centerFiberFunctorCoreMonoidal : centerFiberFunctor.CoreMonoidal where
  εIso := PointedVec.totalUnitIso
  μIso X Y := PointedVec.totalTensorIso X.obj.obj Y.obj.obj
  μIso_hom_natural_left f X :=
    PointedVec.totalFunctorCoreMonoidal.μIso_hom_natural_left f X.obj.obj
  μIso_hom_natural_right X f :=
    PointedVec.totalFunctorCoreMonoidal.μIso_hom_natural_right X.obj.obj f
  associativity X Y Z := PointedVec.totalTensorHom_associativity X.obj.obj Y.obj.obj Z.obj.obj
  left_unitality X := PointedVec.totalTensorHom_left_unitality X.obj.obj
  right_unitality X := PointedVec.totalTensorHom_right_unitality X.obj.obj

instance centerFiberFunctor_monoidal : centerFiberFunctor.Monoidal :=
  centerFiberFunctorCoreMonoidal.toMonoidal

def totalParity (X : BCenter) : centerFiberFunctor.obj X ⟶ centerFiberFunctor.obj X :=
  centerFiberFunctor.map (centerParity.hom.app X)

lemma totalParity_involutive (X : BCenter) : totalParity X ≫ totalParity X = 𝟙 _ := by
  rw [totalParity, ← centerFiberFunctor.map_comp, centerParity_involutive,
    CategoryTheory.Functor.map_id]

/-- Forget the grading but retain its actual C₂ sign action. -/
def centerRepFunctor : BCenter ⥤ FDRep ℂ H where
  obj X := actionOfInvolution (centerFiberFunctor.obj X) (totalParity X) (totalParity_involutive X)
  map {X Y} f := mapOfInvolution (totalParity X) (totalParity Y)
    (totalParity_involutive X) (totalParity_involutive Y) (centerFiberFunctor.map f) (by
      simp only [totalParity, ← centerFiberFunctor.map_comp]
      exact congrArg centerFiberFunctor.map (centerParity.hom.naturality f).symm)
  map_id X := by
    apply Action.Hom.ext
    exact centerFiberFunctor.map_id X
  map_comp f g := by
    apply Action.Hom.ext
    exact centerFiberFunctor.map_comp f g

instance centerRepFunctor_additive : centerRepFunctor.Additive where
  map_add := by
    intros
    apply Action.Hom.ext
    exact centerFiberFunctor.map_add

instance centerRepFunctor_linear : centerRepFunctor.Linear ℂ where
  map_smul f c := by
    apply Action.Hom.ext
    exact centerFiberFunctor.map_smul c f

instance centerRepFunctor_faithful : centerRepFunctor.Faithful where
  map_injective {_ _} _ _ h :=
    centerFiberFunctor.map_injective (congrArg Action.Hom.hom h)

@[reassoc (attr := simp)]
lemma fiber_totalParity (X : BCenter) (a : Paper18.PointedA) :
    biproduct.ι X.obj.obj a ≫ totalParity X =
      centerParityChar a • biproduct.ι X.obj.obj a := by
  change biproduct.ι X.obj.obj a ≫
    PointedVec.totalFunctor.map (PointedVec.degreeMap centerParityChar X.obj.obj) = _
  rw [PointedVec.totalFunctor_ι_map]
  simp

end Paper18.Category.AppendixBPointed
