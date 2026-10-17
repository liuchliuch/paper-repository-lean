import Paper18.Category.FixedBoundaryNeutralComparison
import Paper18.Category.FixedBoundaryAlgebraTranslation

/-!
# The specified neutral comparison respects actual algebra translations

The boundary-module equivalence extends alpha uniquely to every neutral
module. Its translation compatibility follows from the actual comparison
on boundary modules and actual essential surjectivity. In particular this
retains the actual regular group action, without an equivariance premise.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj Obj
universe v u v' u'
namespace Paper18.Category.FixedBoundary
variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℂ A]
  [MonoidalCategory A] [BraidedCategory A] [MonoidalPreadditive A] [MonoidalLinear ℂ A]
  [HasKernels A] [HasFiniteBiproducts A] [RightRigidCategory A] [HasCoequalizers A]
  [∀ X Y : A, FiniteDimensional ℂ (X ⟶ Y)]
  {N : Type u'} [Category.{v'} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N] [MonoidalPreadditive N] [MonoidalLinear ℂ N]
  [RightRigidCategory N] [HasCoequalizers N]
  (i : A ⥤ N) [i.Braided] [i.Full] [i.Faithful] [i.Additive] [i.Linear ℂ]
  (R : A) [MonObj R] [IsCommMonObj R]
  {T : N} (B : TensorInverse T)
  (himage : ∀ X : A, Centralizes T (i.obj X))
  (t : R ⟶ R) [IsMonHom t]

/-- Actual algebra restriction preserves the actual neutral component,
because its underlying object and hence monodromy are unchanged. -/
def neutralModuleComap : SignKernel.Positive (neutralModuleCharacter i R B himage) ⥤
    SignKernel.Positive (neutralModuleCharacter i R B himage) where
  obj M := ⟨(Mod_.comap (i.map t)).obj M.obj, by
    apply (B.moduleMonodromy_neutral_iff (i.obj R) (himage R) _).mpr
    exact (B.moduleMonodromy_neutral_iff (i.obj R) (himage R) M.obj).mp M.property⟩
  map f := (Mod_.comap (i.map t)).map f
  map_id M := (Mod_.comap (i.map t)).map_id M.obj
  map_comp f g := (Mod_.comap (i.map t)).map_comp f g

/-- Module transport commutes with restriction before and after its
actual lift to the neutral category. -/
def neutralModuleComapImageIso (M : Mod_ A R) :
    (neutralModuleLift i R B himage).obj ((Mod_.comap t).obj M) ≅
      (neutralModuleComap i R B himage t).obj ((neutralModuleLift i R B himage).obj M) :=
  ObjectProperty.isoMk _ ((InternalModule.mapModulesComapIso i R t).app M)

@[simp] theorem neutralModuleComapImageIso_hom (M : Mod_ A R) :
    (neutralModuleComapImageIso i R B himage t M).hom.hom = 𝟙 (i.obj M.X) := rfl

variable (P : BoundaryAutoequivalence i) (S : SeparableAlgebra R)
  (hfull : ∀ Y : N, Centralizes T Y → ∃ X : A, Nonempty (i.obj X ≅ Y))
  (e : P.functor.obj T ≅ T)

/-- The actual extended neutral alpha has unchanged underlying components
under every actual boundary-algebra translation. This is the component
form of its actual equivariance for the regular action. -/
theorem neutralComparison_comap_hom
    (M : SignKernel.Positive (neutralModuleCharacter i R B himage)) :
    ((neutralComparisonUnderlying i P R B himage S hfull e).hom.app
      ((neutralModuleComap i R B himage t).obj M)).hom =
        ((neutralComparisonUnderlying i P R B himage S hfull e).hom.app M).hom := by
  letI := neutralModuleLift_essSurj i R B himage S hfull
  obtain ⟨X, ⟨q⟩⟩ := Functor.EssSurj.mem_essImage (F := neutralModuleLift i R B himage) M
  let z := neutralModuleComapImageIso i R B himage t X ≪≫
    (neutralModuleComap i R B himage t).mapIso q
  let a := neutralComparisonUnderlying i P R B himage S hfull e
  have hn := congrArg (fun f => f.hom) (a.hom.naturality q.hom)
  have hz := congrArg (fun f => f.hom) (a.hom.naturality z.hom)
  have hX := neutralComparison_component i P R B himage S hfull e X
  have hXt := neutralComparison_component i P R B himage S hfull e ((Mod_.comap t).obj X)
  change P.functor.map q.hom.hom ≫ (a.hom.app M).hom =
    (a.hom.app ((neutralModuleLift i R B himage).obj X)).hom ≫ q.hom.hom at hn
  change P.functor.map z.hom.hom ≫
      (a.hom.app ((neutralModuleComap i R B himage t).obj M)).hom =
    (a.hom.app ((neutralModuleLift i R B himage).obj ((Mod_.comap t).obj X))).hom ≫
      z.hom.hom at hz
  have hzq : z.hom.hom = q.hom.hom := by
    change 𝟙 _ ≫ q.hom.hom = q.hom.hom
    exact Category.id_comp _
  change (a.hom.app ((neutralModuleLift i R B himage).obj X)).hom =
    P.boundary.hom.app X.X at hX
  change (a.hom.app ((neutralModuleLift i R B himage).obj ((Mod_.comap t).obj X))).hom =
    P.boundary.hom.app X.X at hXt
  rw [hzq, hXt] at hz
  rw [hX] at hn
  letI : IsIso q.hom.hom := ((Mod_.forget (D := N) (i.obj R)).mapIso
    ((SignKernel.inclusion (neutralModuleCharacter i R B himage)).mapIso q)).isIso_hom
  apply (cancel_epi (P.functor.map q.hom.hom)).mp
  exact hz.trans hn.symm

/-- The extended prescribed alpha is an actual equivariant comparison
for restriction along every boundary algebra endomorphism. -/
theorem neutralComparison_comap
    (M : SignKernel.Positive (neutralModuleCharacter i R B himage)) :
    (P.moduleComapComparison R t).hom.app M.obj ≫
        (Mod_.comap (i.map t)).map
          ((neutralComparisonUnderlying i P R B himage S hfull e).hom.app M) =
      (neutralComparisonUnderlying i P R B himage S hfull e).hom.app
        ((neutralModuleComap i R B himage t).obj M) := by
  apply Mod_.Hom.ext
  change 𝟙 _ ≫ ((neutralComparisonUnderlying i P R B himage S hfull e).hom.app M).hom =
    ((neutralComparisonUnderlying i P R B himage S hfull e).hom.app
      ((neutralModuleComap i R B himage t).obj M)).hom
  rw [Category.id_comp]
  exact (neutralComparison_comap_hom i R B himage t P S hfull e M).symm

/-- The inverse comparison obeys the same actual translation coherence. -/
theorem neutralComparison_comap_inv
    (M : SignKernel.Positive (neutralModuleCharacter i R B himage)) :
    (Mod_.comap (i.map t)).map
        ((neutralComparisonUnderlying i P R B himage S hfull e).inv.app M) ≫
          (P.moduleComapComparison R t).inv.app M.obj =
      (neutralComparisonUnderlying i P R B himage S hfull e).inv.app
        ((neutralModuleComap i R B himage t).obj M) := by
  let a := neutralComparisonUnderlying i P R B himage S hfull e
  apply (cancel_mono (a.hom.app ((neutralModuleComap i R B himage t).obj M))).mp
  rw [← neutralComparison_comap i R B himage t P S hfull e M]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← (Mod_.comap (i.map t)).map_comp, a.inv_hom_id_app,
    (Mod_.comap (i.map t)).map_id]
  rw [neutralComparison_comap]
  exact (a.inv_hom_id_app ((neutralModuleComap i R B himage t).obj M)).symm

end Paper18.Category.FixedBoundary
