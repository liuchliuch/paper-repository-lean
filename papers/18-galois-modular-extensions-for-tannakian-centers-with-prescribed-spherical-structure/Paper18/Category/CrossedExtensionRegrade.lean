import Paper18.Category.QuasiFusionCategory
import Paper18.Category.CrossedExtensionCochain

/-! # Actual regrading and tensor comparison maps -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
namespace Paper18.Category.CrossedExtension
variable {A : Type} [Fintype A] [AddGroup A]
open GradedObject.Monoidal
local instance regradeBaseMonoidal : MonoidalCategory (GradedObject A (FGModuleCat ℂ)) :=
  GradedObject.monoidalCategory

/-- Actual pullback of finite graded vector spaces along a degree automorphism. -/
def regradeFunctor (e : A ≃+ A) : PointedVec A ⥤ PointedVec A :=
  GradedObject.comap (FGModuleCat ℂ) e

instance regradeFunctor_additive (e : A ≃+ A) : (regradeFunctor e).Additive where
  map_add := by intros; rfl
instance regradeFunctor_linear (e : A ≃+ A) : (regradeFunctor e).Linear ℂ where
  map_smul := by intros; rfl
instance regradeFunctor_faithful (e : A ≃+ A) : (regradeFunctor e).Faithful where
  map_injective {X Y} f g h := by
    funext a
    obtain ⟨b, rfl⟩ := e.surjective a
    exact congrFun h b

/-- An actual equivalence of the underlying graded categories. -/
def regradeEquivalence (e : A ≃+ A) : PointedVec A ≌ PointedVec A :=
  GradedObject.comapEquiv (FGModuleCat ℂ) e.symm.toEquiv

/-- The canonical convolution tensor comparison after actual regrading. -/
def regradeTensorHom (e : A ≃+ A) (X Y : PointedVec A) :
    (regradeFunctor e).obj X ⊗ (regradeFunctor e).obj Y ⟶
      (regradeFunctor e).obj (X ⊗ Y) := fun k =>
  tensorObjDesc (fun a b h => ιTensorObj X Y (e a) (e b) (e k)
    (by rw [← e.map_add, h]))

@[reassoc (attr := simp)]
lemma inclusion_regradeTensorHom (e : A ≃+ A) (X Y : PointedVec A)
    (a b k : A) (h : a + b = k) :
    ιTensorObj ((regradeFunctor e).obj X) ((regradeFunctor e).obj Y) a b k h ≫
        regradeTensorHom e X Y k =
      ιTensorObj X Y (e a) (e b) (e k) (by rw [← e.map_add, h]) := by
  simp [regradeTensorHom]

/-- The inverse comparison explicitly reindexes every homogeneous convolution
summand; it is not inferred from a dimension equality. -/
def regradeTensorInv (e : A ≃+ A) (X Y : PointedVec A) :
    (regradeFunctor e).obj (X ⊗ Y) ⟶
      (regradeFunctor e).obj X ⊗ (regradeFunctor e).obj Y := fun k =>
  tensorObjDesc (fun a b h =>
    eqToHom (by simp only [regradeFunctor, GradedObject.comap, Pi.comap,
      e.apply_symm_apply]) ≫
    ιTensorObj ((regradeFunctor e).obj X) ((regradeFunctor e).obj Y)
      (e.symm a) (e.symm b) k (by rw [← e.symm.map_add, h, e.symm_apply_apply]))

@[reassoc (attr := simp)]
lemma inclusion_regradeTensorInv (e : A ≃+ A) (X Y : PointedVec A)
    (a b k : A) (h : a + b = e k) :
    ιTensorObj X Y a b (e k) h ≫ regradeTensorInv e X Y k =
      eqToHom (by simp only [regradeFunctor, GradedObject.comap, Pi.comap,
        e.apply_symm_apply]) ≫
        ιTensorObj ((regradeFunctor e).obj X) ((regradeFunctor e).obj Y)
          (e.symm a) (e.symm b) k (by rw [← e.symm.map_add, h, e.symm_apply_apply]) := by
  simp [regradeTensorInv]

lemma eqToHom_tensorInclusion (X Y : PointedVec A) {a a' b b' k : A}
    (ha : a' = a) (hb : b' = b) (h : a + b = k) (h' : a' + b' = k)
    (q : X a ⊗ Y b = X a' ⊗ Y b') :
    eqToHom q ≫ ιTensorObj X Y a' b' k h' = ιTensorObj X Y a b k h := by
  subst a'
  subst b'
  simp

/-- Actual tensor-product isomorphism for pullback by a degree automorphism. -/
def regradeTensorIso (e : A ≃+ A) (X Y : PointedVec A) :
    (regradeFunctor e).obj X ⊗ (regradeFunctor e).obj Y ≅
      (regradeFunctor e).obj (X ⊗ Y) where
  hom := regradeTensorHom e X Y
  inv := regradeTensorInv e X Y
  hom_inv_id := by
    apply GradedObject.hom_ext
    intro k
    apply tensorObj_ext
    intro a b h
    change _ ≫ (regradeTensorHom e X Y k ≫ regradeTensorInv e X Y k) = _ ≫ 𝟙 _
    rw [inclusion_regradeTensorHom_assoc, inclusion_regradeTensorInv]
    rw [comp_id]
    exact eqToHom_tensorInclusion _ _ (e.symm_apply_apply a) (e.symm_apply_apply b) _ _ _
  inv_hom_id := by
    apply GradedObject.hom_ext
    intro k
    apply tensorObj_ext
    intro a b h
    change _ ≫ (regradeTensorInv e X Y k ≫ regradeTensorHom e X Y k) = _ ≫ 𝟙 _
    rw [inclusion_regradeTensorInv_assoc, inclusion_regradeTensorHom]
    rw [comp_id]
    exact eqToHom_tensorInclusion _ _ (e.apply_symm_apply a) (e.apply_symm_apply b) _ _ _

lemma regradeTensorHom_naturality (e : A ≃+ A) {X X' Y Y' : PointedVec A}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    ((regradeFunctor e).map f ⊗ₘ (regradeFunctor e).map g) ≫ regradeTensorHom e X' Y' =
      regradeTensorHom e X Y ≫ (regradeFunctor e).map (f ⊗ₘ g) := by
  apply GradedObject.hom_ext
  intro k
  apply tensorObj_ext
  intro a b h
  change ιTensorObj ((regradeFunctor e).obj X) ((regradeFunctor e).obj Y) a b k h ≫
      GradedObject.Monoidal.tensorHom ((regradeFunctor e).map f) ((regradeFunctor e).map g) k ≫ _ =
    ιTensorObj ((regradeFunctor e).obj X) ((regradeFunctor e).obj Y) a b k h ≫
      regradeTensorHom e X Y k ≫ GradedObject.Monoidal.tensorHom f g (e k)
  simp
  rfl

end Paper18.Category.CrossedExtension
