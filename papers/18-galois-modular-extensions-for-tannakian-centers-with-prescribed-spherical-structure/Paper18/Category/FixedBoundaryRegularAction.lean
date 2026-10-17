import Paper18.Category.TannakianDeequivariantization
import Paper18.Category.RepresentationRightTranslation
import Paper18.Category.EquivariantBasic
import Paper18.Category.SeparableModulesLinear

/-!
# The actual regular-algebra action for an arbitrary tensor embedding

The regular algebra need not be transparent. Right translation induces restriction of
scalars on its actual module category. Inverse right translation gives the
usual weak left-action convention.
-/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped MonObj Obj
universe v u
namespace Paper18.Category.FixedBoundary
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C]
  {G : Type} [Group G] [Fintype G] (F : FDRep ℂ G ⥤ C) [F.Monoidal]

/-- The actual regular algebra transported through any strong tensor functor. -/
def regularAlgebra : C := F.obj (Representation.functions (G := G))

instance regularAlgebraMonObj : MonObj (regularAlgebra F) := Functor.monObjObj _

/-- Actual modules over the transported regular algebra. -/
abbrev Modules := Mod_ C (regularAlgebra F)

/-- Actual separability transported through the given tensor functor. -/
def regularSeparable : SeparableAlgebra (regularAlgebra F) :=
  Representation.functionsSeparable.map F

/-- Right translation as an actual regular-algebra endomorphism in the
ambient braided category. -/
def regularTranslation (g : G) : (regularAlgebra F) ⟶ (regularAlgebra F) :=
  F.map (Representation.rightTranslation g)

instance regularTranslationIsMonHom (g : G) :
    IsMonHom ((regularTranslation F) g) := by
  dsimp [regularTranslation, regularAlgebra]
  infer_instance

@[simp] lemma regularTranslation_one : (regularTranslation F) (1 : G) = 𝟙 _ := by
  simp [regularTranslation, regularAlgebra]

lemma regularTranslation_mul (g h : G) :
    (regularTranslation F) (g * h) = (regularTranslation F) h ≫ (regularTranslation F) g := by
  simp only [regularTranslation, Representation.rightTranslation_mul, Functor.map_comp]

/-- Inverse right translation acts on genuine internal modules by
restriction of scalars. -/
def moduleTranslation (g : G) : (Modules F) ⥤ (Modules F) :=
  Mod_.comap ((regularTranslation F) g⁻¹)

/-- Unit coherence, with the identity underlying ambient morphism. -/
def moduleTranslationUnit : (moduleTranslation F) 1 ≅ 𝟭 (Modules F) :=
  NatIso.ofComponents (fun M => {
    hom := Mod_.Hom.mk' (𝟙 M.X) (by
      change (((regularTranslation F) (1 : G)⁻¹ ▷ M.X) ≫ γ[(regularAlgebra F),M.X]) ≫ 𝟙 _ =
        ((regularAlgebra F) ◁ 𝟙 M.X) ≫ γ[(regularAlgebra F),M.X]
      simp)
    inv := Mod_.Hom.mk' (𝟙 M.X) (by
      change γ[(regularAlgebra F),M.X] ≫ 𝟙 M.X =
        ((regularAlgebra F) ◁ 𝟙 M.X) ≫
          ((regularTranslation F) (1 : G)⁻¹ ▷ M.X) ≫ γ[(regularAlgebra F),M.X]
      simp)
    hom_inv_id := by
      apply Mod_.Hom.ext
      change 𝟙 M.X ≫ 𝟙 M.X = 𝟙 M.X
      simp
    inv_hom_id := by
      apply Mod_.Hom.ext
      change 𝟙 M.X ≫ 𝟙 M.X = 𝟙 M.X
      simp }) (by
      intro M N f
      apply Mod_.Hom.ext
      simp [moduleTranslation, Mod_.comap])

/-- Multiplication coherence, with the identity underlying ambient
morphism; its module law is the actual right-translation multiplication law. -/
def moduleTranslationMul (g h : G) :
    (moduleTranslation F) h ⋙ (moduleTranslation F) g ≅ (moduleTranslation F) (g * h) :=
  NatIso.ofComponents (fun M => {
    hom := Mod_.Hom.mk' (𝟙 M.X) (by
      change (((regularTranslation F) g⁻¹ ▷ M.X) ≫
        ((regularTranslation F) h⁻¹ ▷ M.X) ≫ γ[(regularAlgebra F),M.X]) ≫ 𝟙 M.X =
        ((regularAlgebra F) ◁ 𝟙 M.X) ≫
          ((regularTranslation F) (g * h)⁻¹ ▷ M.X) ≫ γ[(regularAlgebra F),M.X]
      simp only [Category.comp_id, MonoidalCategory.whiskerLeft_id, Category.id_comp]
      rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight,
        ← (regularTranslation_mul F), mul_inv_rev])
    inv := Mod_.Hom.mk' (𝟙 M.X) (by
      change (((regularTranslation F) (g * h)⁻¹ ▷ M.X) ≫ γ[(regularAlgebra F),M.X]) ≫ 𝟙 M.X =
        ((regularAlgebra F) ◁ 𝟙 M.X) ≫ ((regularTranslation F) g⁻¹ ▷ M.X) ≫
          ((regularTranslation F) h⁻¹ ▷ M.X) ≫ γ[(regularAlgebra F),M.X]
      simp only [Category.comp_id, MonoidalCategory.whiskerLeft_id, Category.id_comp]
      rw [mul_inv_rev, (regularTranslation_mul F), MonoidalCategory.comp_whiskerRight,
        Category.assoc])
    hom_inv_id := by
      apply Mod_.Hom.ext
      change 𝟙 M.X ≫ 𝟙 M.X = 𝟙 M.X
      simp
    inv_hom_id := by
      apply Mod_.Hom.ext
      change 𝟙 M.X ≫ 𝟙 M.X = 𝟙 M.X
      simp }) (by
      intro M N f
      apply Mod_.Hom.ext
      simp [moduleTranslation, Mod_.comap])

end Paper18.Category.FixedBoundary

namespace Paper18.Category.FixedBoundary
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C]
  {G : Type} [Group G] [Fintype G] (F : FDRep ℂ G ⥤ C) [F.Monoidal]

lemma module_eqToHom_hom {M N : (Modules F)} (e : M = N) :
    (eqToHom e).hom = eqToHom (congrArg (fun M : (Modules F) => M.X) e) := by
  cases e
  rfl

/-- The actual coherent left action of the finite group on the internal
module category, constructed from inverse right translations. -/
def regularAction : WeakAction G (Modules F) where
  ρ := (moduleTranslation F)
  unitIso := (moduleTranslationUnit F)
  mulIso := (moduleTranslationMul F)
  assoc g h k M := by
    apply Mod_.Hom.ext
    simp [moduleTranslation, moduleTranslationMul,
      Mod_.comap, module_eqToHom_hom]
  one_mul g M := by
    apply Mod_.Hom.ext
    simp [moduleTranslation, moduleTranslationMul,
      moduleTranslationUnit, Mod_.comap, module_eqToHom_hom]
  mul_one g M := by
    apply Mod_.Hom.ext
    simp [moduleTranslation, moduleTranslationMul,
      moduleTranslationUnit, Mod_.comap, module_eqToHom_hom]

end Paper18.Category.FixedBoundary

namespace Paper18.Category.FixedBoundary
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  {G : Type} [Group G] [Fintype G] (F : FDRep ℂ G ⥤ C) [F.Monoidal]

instance moduleTranslationAdditive (g : G) : ((moduleTranslation F) g).Additive where
  map_add := by
    intro M N f h
    apply Mod_.Hom.ext
    rfl

instance moduleTranslationLinear (g : G) : ((moduleTranslation F) g).Linear ℂ where
  map_smul := by
    intro M N f c
    apply Mod_.Hom.ext
    rfl

instance regularActionAdditive (g : G) :
    ((regularAction F).ρ g).Additive := (moduleTranslationAdditive F) g

instance regularActionLinear (g : G) :
    ((regularAction F).ρ g).Linear ℂ := (moduleTranslationLinear F) g

end Paper18.Category.FixedBoundary
