import Paper18.Category.TannakianDeequivariantization
import Paper18.Category.RepresentationRightTranslation
import Paper18.Category.EquivariantBasic
import Paper18.Category.SeparableModulesLinear

/-!
# The actual group action on de-equivariant modules

Right translation on the regular function algebra induces restriction of
scalars on its actual module category. Inverse right translation gives the
usual weak left-action convention.
-/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped MonObj Obj
universe v u
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C]
  {G : Type} [Group G] [Fintype G] (T : TannakianCenter C G)

/-- Right translation as an actual regular-algebra endomorphism in the
ambient braided category. -/
def TannakianCenter.regularTranslation (g : G) : T.regularAlgebra ⟶ T.regularAlgebra :=
  T.inclusion.map (Representation.rightTranslation g)

instance TannakianCenter.regularTranslationIsMonHom (g : G) :
    IsMonHom (T.regularTranslation g) := by
  dsimp [TannakianCenter.regularTranslation, TannakianCenter.regularAlgebra]
  infer_instance

@[simp] lemma TannakianCenter.regularTranslation_one : T.regularTranslation (1 : G) = 𝟙 _ := by
  simp [TannakianCenter.regularTranslation, TannakianCenter.regularAlgebra]

lemma TannakianCenter.regularTranslation_mul (g h : G) :
    T.regularTranslation (g * h) = T.regularTranslation h ≫ T.regularTranslation g := by
  simp only [TannakianCenter.regularTranslation, Representation.rightTranslation_mul, Functor.map_comp]

/-- Inverse right translation acts on genuine internal modules by
restriction of scalars. -/
def TannakianCenter.moduleTranslation (g : G) : T.Deequivariantization ⥤ T.Deequivariantization :=
  Mod_.comap (T.regularTranslation g⁻¹)

/-- Unit coherence, with the identity underlying ambient morphism. -/
def TannakianCenter.moduleTranslationUnit : T.moduleTranslation 1 ≅ 𝟭 T.Deequivariantization :=
  NatIso.ofComponents (fun M => {
    hom := Mod_.Hom.mk' (𝟙 M.X) (by
      change ((T.regularTranslation (1 : G)⁻¹ ▷ M.X) ≫ γ[T.regularAlgebra,M.X]) ≫ 𝟙 _ =
        (T.regularAlgebra ◁ 𝟙 M.X) ≫ γ[T.regularAlgebra,M.X]
      simp)
    inv := Mod_.Hom.mk' (𝟙 M.X) (by
      change γ[T.regularAlgebra,M.X] ≫ 𝟙 M.X =
        (T.regularAlgebra ◁ 𝟙 M.X) ≫
          (T.regularTranslation (1 : G)⁻¹ ▷ M.X) ≫ γ[T.regularAlgebra,M.X]
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
      simp [TannakianCenter.moduleTranslation, Mod_.comap])

/-- Multiplication coherence, with the identity underlying ambient
morphism; its module law is the actual right-translation multiplication law. -/
def TannakianCenter.moduleTranslationMul (g h : G) :
    T.moduleTranslation h ⋙ T.moduleTranslation g ≅ T.moduleTranslation (g * h) :=
  NatIso.ofComponents (fun M => {
    hom := Mod_.Hom.mk' (𝟙 M.X) (by
      change ((T.regularTranslation g⁻¹ ▷ M.X) ≫
        (T.regularTranslation h⁻¹ ▷ M.X) ≫ γ[T.regularAlgebra,M.X]) ≫ 𝟙 M.X =
        (T.regularAlgebra ◁ 𝟙 M.X) ≫
          (T.regularTranslation (g * h)⁻¹ ▷ M.X) ≫ γ[T.regularAlgebra,M.X]
      simp only [Category.comp_id, MonoidalCategory.whiskerLeft_id, Category.id_comp]
      rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight,
        ← T.regularTranslation_mul, mul_inv_rev])
    inv := Mod_.Hom.mk' (𝟙 M.X) (by
      change ((T.regularTranslation (g * h)⁻¹ ▷ M.X) ≫ γ[T.regularAlgebra,M.X]) ≫ 𝟙 M.X =
        (T.regularAlgebra ◁ 𝟙 M.X) ≫ (T.regularTranslation g⁻¹ ▷ M.X) ≫
          (T.regularTranslation h⁻¹ ▷ M.X) ≫ γ[T.regularAlgebra,M.X]
      simp only [Category.comp_id, MonoidalCategory.whiskerLeft_id, Category.id_comp]
      rw [mul_inv_rev, T.regularTranslation_mul, MonoidalCategory.comp_whiskerRight,
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
      simp [TannakianCenter.moduleTranslation, Mod_.comap])

end Paper18.Category

namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C]
  {G : Type} [Group G] [Fintype G] (T : TannakianCenter C G)

lemma module_eqToHom_hom {M N : T.Deequivariantization} (e : M = N) :
    (eqToHom e).hom = eqToHom (congrArg (fun M : T.Deequivariantization => M.X) e) := by
  cases e
  rfl

/-- The actual coherent left action of the finite group on the internal
module category, constructed from inverse right translations. -/
def TannakianCenter.deequivariantAction : WeakAction G T.Deequivariantization where
  ρ := T.moduleTranslation
  unitIso := T.moduleTranslationUnit
  mulIso := T.moduleTranslationMul
  assoc g h k M := by
    apply Mod_.Hom.ext
    simp [TannakianCenter.moduleTranslation, TannakianCenter.moduleTranslationMul,
      Mod_.comap, module_eqToHom_hom]
  one_mul g M := by
    apply Mod_.Hom.ext
    simp [TannakianCenter.moduleTranslation, TannakianCenter.moduleTranslationMul,
      TannakianCenter.moduleTranslationUnit, Mod_.comap, module_eqToHom_hom]
  mul_one g M := by
    apply Mod_.Hom.ext
    simp [TannakianCenter.moduleTranslation, TannakianCenter.moduleTranslationMul,
      TannakianCenter.moduleTranslationUnit, Mod_.comap, module_eqToHom_hom]

end Paper18.Category

namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  {G : Type} [Group G] [Fintype G] (T : TannakianCenter C G)

instance TannakianCenter.moduleTranslationAdditive (g : G) : (T.moduleTranslation g).Additive where
  map_add := by
    intro M N f h
    apply Mod_.Hom.ext
    rfl

instance TannakianCenter.moduleTranslationLinear (g : G) : (T.moduleTranslation g).Linear ℂ where
  map_smul := by
    intro M N f c
    apply Mod_.Hom.ext
    rfl

instance TannakianCenter.deequivariantActionAdditive (g : G) :
    (T.deequivariantAction.ρ g).Additive := T.moduleTranslationAdditive g

instance TannakianCenter.deequivariantActionLinear (g : G) :
    (T.deequivariantAction.ρ g).Linear ℂ := T.moduleTranslationLinear g

end Paper18.Category
