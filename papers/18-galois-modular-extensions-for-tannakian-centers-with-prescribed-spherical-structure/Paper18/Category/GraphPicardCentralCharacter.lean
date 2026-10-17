import Paper18.Category.GraphPicardCentralFunctor
import Paper18.Category.GraphPicardCentralAction

/-! # The actual algebra character on the right central action

The central commutative algebra acts on each of its modules.  Its right
action is an actual module-natural map to the identity module functor;
its multiplicativity follows from the actual module associativity law.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped MonObj MonoidalLeftAction
universe v u
namespace Paper18.Category.GraphPicard
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  (A : Center D) [MonObj A] [IsCommMonObj A]
local instance characterUnderlyingMonObj : MonObj A.1 :=
  Functor.monObjObj (F := Center.forget D) A
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

/-- The actual right algebra action, inside the actual category of
strong additive complex-linear module endofunctors. -/
def centralCharacter :
    (rightCentralAction D (Mod_ D A.1)).obj A ⟶
      𝟙_ (ModuleAlphaInduction.End Dᴹᵒᵖ (Mod_ D A.1)) :=
  ⟨centralActionCounit A, show ModuleFunctor.IsModuleNatural Dᴹᵒᵖ (centralActionCounit A) from inferInstance⟩

@[simp] lemma centralCharacter_app (M : Mod_ D A.1) :
    ((centralCharacter A).val.app M).hom = centralRightAction A M := rfl

/-- The actual unit of the central algebra acts as the identity. -/
lemma centralCharacter_one :
    (rightCentralUnitIso D (Mod_ D A.1)).hom ≫
        (rightCentralAction D (Mod_ D A.1)).map η[A] ≫ centralCharacter A = 𝟙 _ := by
  apply ModuleFunctor.bundled_hom_ext
  ext M
  change ((rightCentralUnitIso D (Mod_ D A.1)).hom.val.app M).hom ≫
      M.X ◁ (η[A]).f ≫ centralRightAction A M = 𝟙 M.X
  rw [rightCentralUnitIso_hom_app]
  change (ρ_ M.X).inv ≫ M.X ◁ (η[A]).f ≫ centralRightAction A M = 𝟙 M.X
  rw [← underlying_unit A, centralRightAction_one]
  exact Iso.inv_hom_id _

/-- The actual multiplication of the central algebra acts by composing
its actual right actions. -/
lemma centralCharacter_mul :
    (rightCentralTensorIso D (Mod_ D A.1) A A).hom ≫
        (rightCentralAction D (Mod_ D A.1)).map μ[A] ≫ centralCharacter A =
      (centralCharacter A ⊗ₘ centralCharacter A) ≫
        (λ_ (𝟙_ (ModuleAlphaInduction.End Dᴹᵒᵖ (Mod_ D A.1)))).hom := by
  apply ModuleFunctor.bundled_hom_ext
  ext M
  change ((rightCentralTensorIso D (Mod_ D A.1) A A).hom.val.app M).hom ≫
      M.X ◁ (μ[A]).f ≫ centralRightAction A M =
    (centralRightAction A (RelativeTensor.ambientTensor M A.1) ≫ centralRightAction A M) ≫ 𝟙 M.X
  rw [rightCentralTensorIso_hom_app]
  simp only [Category.comp_id]
  have hnat := centralRightAction_naturality A (centralRightActionHom A M)
  change centralRightAction A (RelativeTensor.ambientTensor M A.1) ≫ centralRightAction A M =
    centralRightAction A M ▷ A.1 ≫ centralRightAction A M at hnat
  rw [hnat]
  change (α_ M.X A.1 A.1).hom ≫ M.X ◁ (μ[A]).f ≫ centralRightAction A M = _
  rw [← underlying_mul A, central_right_assoc]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- The actual character is a genuine algebra homomorphism for the
actual mapped algebra, rather than only an underlying natural map. -/
def centralCharacter_isMonHom :
    letI : MonObj ((rightCentralAction D (Mod_ D A.1)).obj A) :=
      Functor.monObjObj (F := rightCentralAction D (Mod_ D A.1)) A
    IsMonHom (centralCharacter A) := by
  letI : MonObj ((rightCentralAction D (Mod_ D A.1)).obj A) :=
    Functor.monObjObj (F := rightCentralAction D (Mod_ D A.1)) A
  refine { one_hom := ?_, mul_hom := ?_ }
  · change ((rightCentralUnitIso D (Mod_ D A.1)).hom ≫
      (rightCentralAction D (Mod_ D A.1)).map η[A]) ≫ centralCharacter A = 𝟙 _
    simpa only [Category.assoc] using centralCharacter_one A
  · change ((rightCentralTensorIso D (Mod_ D A.1) A A).hom ≫
      (rightCentralAction D (Mod_ D A.1)).map μ[A]) ≫ centralCharacter A =
        (centralCharacter A ⊗ₘ centralCharacter A) ≫
          (λ_ (𝟙_ (ModuleAlphaInduction.End Dᴹᵒᵖ (Mod_ D A.1)))).hom
    simpa only [Category.assoc] using centralCharacter_mul A

/-- Every actual central cap into the algebra produces a genuine
morphism in the actual module-endofunctor category. -/
def centralCapHom {Z : Center D} (q : Z ⟶ A) :
    (rightCentralAction D (Mod_ D A.1)).obj Z ⟶
      𝟙_ (ModuleAlphaInduction.End Dᴹᵒᵖ (Mod_ D A.1)) :=
  (rightCentralAction D (Mod_ D A.1)).map q ≫ centralCharacter A

@[simp] lemma centralCapHom_app {Z : Center D} (q : Z ⟶ A) (M : Mod_ D A.1) :
    ((centralCapHom A q).val.app M).hom =
      M.X ◁ q.f ≫ centralRightAction A M := rfl

/-- A genuine multiplication relation among central caps is preserved
by the actual algebra character. -/
lemma centralCapHom_mul {Z W V : Center D} (q : Z ⟶ A) (r : W ⟶ A)
    (s : V ⟶ A) (t : Z ⊗ W ⟶ V)
    (h : (q ⊗ₘ r) ≫ μ[A] = t ≫ s) :
    (centralCapHom A q ⊗ₘ centralCapHom A r) ≫
        (λ_ (𝟙_ (ModuleAlphaInduction.End Dᴹᵒᵖ (Mod_ D A.1)))).hom =
      Functor.LaxMonoidal.μ (rightCentralAction D (Mod_ D A.1)) Z W ≫
        (rightCentralAction D (Mod_ D A.1)).map t ≫ centralCapHom A s := by
  dsimp only [centralCapHom]
  rw [← tensorHom_comp_tensorHom_assoc, ← centralCharacter_mul]
  change _ ≫ (Functor.LaxMonoidal.μ (rightCentralAction D (Mod_ D A.1)) A A ≫
    (rightCentralAction D (Mod_ D A.1)).map μ[A] ≫ centralCharacter A) = _
  rw [Functor.LaxMonoidal.μ_natural_assoc, ← Functor.map_comp_assoc, h,
    Functor.map_comp]
  simp only [Category.assoc]

end Paper18.Category.GraphPicard
