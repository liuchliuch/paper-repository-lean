import Paper18.Category.BalancedModuleCategoryFreeMaps
import Paper18.Category.BalancedModuleCategoryDetection

/-! # Balanced natural maps respect every actual free bimodule map -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u vE uE
namespace Paper18.Category.BalancedModuleCategory
/-- Actual commuting squares compose in every category. -/
lemma compose_square {E : Type uE} [Category.{vE} E]
    {X₀ X₁ X₂ Y₀ Y₁ Y₂ : E}
    {f : X₀ ⟶ X₁} {f' : X₁ ⟶ X₂} {g : Y₀ ⟶ Y₁} {g' : Y₁ ⟶ Y₂}
    {t₀ : X₀ ⟶ Y₀} {t₁ : X₁ ⟶ Y₁} {t₂ : X₂ ⟶ Y₂}
    (h : f ≫ t₁ = t₀ ≫ g) (h' : f' ≫ t₂ = t₁ ≫ g') :
    (f ≫ f') ≫ t₂ = t₀ ≫ (g ≫ g') := by
  rw [assoc, h', ← assoc, h, assoc]

lemma vertical_square {E : Type uE} [Category.{vE} E]
    {X₀ X₁ Y₀ Y₁ Z₀ Z₁ : E}
    {f : X₀ ⟶ X₁} {g : Y₀ ⟶ Y₁} {k : Z₀ ⟶ Z₁}
    {b₀ : X₀ ⟶ Y₀} {b₁ : X₁ ⟶ Y₁} {c₀ : Y₀ ⟶ Z₀} {c₁ : Y₁ ⟶ Z₁}
    (h : f ≫ b₁ = b₀ ≫ g) (h' : g ≫ c₁ = c₀ ≫ k) :
    f ≫ (b₁ ≫ c₁) = (b₀ ≫ c₀) ≫ k := by
  rw [← assoc, h, assoc, h', ← assoc]

variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  {A B : D} [MonObj A] [MonObj B]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
variable {E : Type uE} [Category.{vE} E]
  {F G : BimoduleRelativeTensor.Native A B ⥤ E}
  (τ : external (A := A) (B := B) ⋙ F ⟶ external ⋙ G)

/-- The actual balancing square for a map of the two restricted functors. -/
def IsBalancedNatural : Prop := ∀ (M : Mod_ D A) (X : D) (N : RightModules B),
  F.map (balancingIso M X N).hom ≫ τ.app (M, rightAmbientTensor N X) =
    τ.app (RelativeTensor.ambientTensor M X, N) ≫ G.map (balancingIso M X N).hom

theorem externalFreeMap_naturality (hτ : IsBalancedNatural τ)
    {X Y : D} (f : X ⟶ (A ⊗ Y) ⊗ B) :
    F.map (externalFreeMap f) ≫ τ.app (InternalModule.free A Y, Mod_.regular (mop B)) =
      τ.app (InternalModule.free A X, Mod_.regular (mop B)) ≫ G.map (externalFreeMap f) := by
  have h₃ := τ.naturality (CategoryTheory.Prod.mkHom
    (InternalModule.actionHom (InternalModule.free A Y)) (rightRegularMultiply (B := B)))
  have h₁ := τ.naturality (CategoryTheory.Prod.mkHom
    (RelativeTensor.ambientFreeIso (A ⊗ Y) B).inv (𝟙 (Mod_.regular (mop B))))
  have h₀ := τ.naturality (CategoryTheory.Prod.mkHom
    (InternalModule.freeMap f) (𝟙 (Mod_.regular (mop B))))
  simp only [Functor.comp_map, InternalModule.free_X, Mod_.regular] at h₀ h₁ h₃
  dsimp only [externalFreeMap]
  simp only [Functor.map_comp, assoc]
  have hs := compose_square (compose_square (compose_square h₀ h₁)
    (hτ (InternalModule.free A (A ⊗ Y)) B (Mod_.regular (mop B)))) h₃
  simpa only [assoc] using hs

variable [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]

/-- No naturality on native free maps is an extra input: it follows from
the three-variable balancing square and the proved actual factorization. -/
theorem free_naturality (hτ : IsBalancedNatural τ) {X Y : D}
    (g : externalObj (InternalModule.free A X) (Mod_.regular (mop B)) ⟶
      externalObj (InternalModule.free A Y) (Mod_.regular (mop B))) :
    F.map g ≫ τ.app (InternalModule.free A Y, Mod_.regular (mop B)) =
      τ.app (InternalModule.free A X, Mod_.regular (mop B)) ≫ G.map g := by
  rw [externalFreeMap_factorization g]
  exact externalFreeMap_naturality τ hτ _

end Paper18.Category.BalancedModuleCategory
