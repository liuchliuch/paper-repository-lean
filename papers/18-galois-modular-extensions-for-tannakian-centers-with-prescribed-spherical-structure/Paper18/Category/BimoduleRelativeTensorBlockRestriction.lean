import Paper18.Category.BimoduleRelativeTensorMixedWattsReconstruction

/-! # Actual restriction to a split algebra quotient

Restriction of scalars along a split epimorphism of arbitrary algebra
objects is fully faithful and strong for the actual ambient right action.
No commutativity, braiding, or pivotal structure is used.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u
namespace Paper18.Category.BimoduleRelativeTensor.Block
open ModuleFunctor
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  {R B : D} [MonObj R] [MonObj B] (p : R ⟶ B) [IsMonHom p]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

instance restriction_faithful : (Mod_.comap (D := D) p).Faithful where
  map_injective {M N} f g h := by
    apply Mod_.Hom.ext
    exact congrArg (fun k : (Mod_.comap (D := D) p).obj M ⟶
      (Mod_.comap (D := D) p).obj N => k.hom) h

/-- An actual map commuting with the restricted action commutes with the
quotient action, by actual epimorphic cancellation. -/
def restrictionPreimage [IsSplitEpi p] {M N : Mod_ D B}
    (f : (Mod_.comap (D := D) p).obj M ⟶ (Mod_.comap (D := D) p).obj N) : M ⟶ N :=
  Mod_.Hom.mk' f.hom (by
    letI : IsSplitEpi (p ▷ M.X) :=
      inferInstanceAs (IsSplitEpi ((tensorRight M.X).map p))
    apply (cancel_epi (p ▷ M.X)).mp
    have h := f.isMod_Hom.smul_hom
    change (p ▷ M.X ≫ γ[B,M.X]) ≫ f.hom =
      R ◁ f.hom ≫ p ▷ N.X ≫ γ[B,N.X] at h
    change p ▷ M.X ≫ γ[B,M.X] ≫ f.hom =
      p ▷ M.X ≫ B ◁ f.hom ≫ γ[B,N.X]
    rw [← whisker_exchange_assoc]
    simpa only [assoc] using h)

instance restriction_full [IsSplitEpi p] : (Mod_.comap (D := D) p).Full where
  map_surjective f := ⟨restrictionPreimage p f, by apply Mod_.Hom.ext; rfl⟩

def restrictionFullyFaithful [IsSplitEpi p] : (Mod_.comap (D := D) p).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful _

/-- The two ambient-tensor action formulas agree by actual associator
naturality at the algebra quotient map. -/
lemma restrictionTensor_action (M : Mod_ D B) (X : D) :
    γ[R,(RelativeTensor.ambientTensor ((Mod_.comap (D := D) p).obj M) X).X] =
      γ[R,((Mod_.comap (D := D) p).obj (RelativeTensor.ambientTensor M X)).X] := by
  change (α_ R M.X X).inv ≫ (p ▷ M.X ≫ γ[B,M.X]) ▷ X =
    p ▷ (M.X ⊗ X) ≫ (α_ B M.X X).inv ≫ γ[B,M.X] ▷ X
  rw [comp_whiskerRight, ← associator_inv_naturality_left_assoc]

def restrictionTensorIso (M : Mod_ D B) (X : D) :
    RelativeTensor.ambientTensor ((Mod_.comap (D := D) p).obj M) X ≅
      (Mod_.comap (D := D) p).obj (RelativeTensor.ambientTensor M X) where
  hom := Mod_.Hom.mk' (𝟙 _) (by
    simp only [comp_id, MonoidalLeftAction.actionHomRight_id, id_comp]
    exact restrictionTensor_action p M X)
  inv := Mod_.Hom.mk' (𝟙 _) (by
    simp only [comp_id, MonoidalLeftAction.actionHomRight_id, id_comp]
    exact (restrictionTensor_action p M X).symm)
  hom_inv_id := by apply Mod_.Hom.ext; exact id_comp _
  inv_hom_id := by apply Mod_.Hom.ext; exact id_comp _

def restrictionLaxLeftLinear : (Mod_.comap (D := D) p).LaxLeftLinear Dᴹᵒᵖ where
  μₗ X M := (restrictionTensorIso p M X.unmop).hom
  μₗ_naturality_left f M := by
    apply Mod_.Hom.ext
    change (M.X ◁ f.unmop) ≫ 𝟙 _ = 𝟙 _ ≫ (M.X ◁ f.unmop)
    simp
  μₗ_naturality_right X M N f := by
    apply Mod_.Hom.ext
    change f.hom ▷ X.unmop ≫ 𝟙 _ = 𝟙 _ ≫ f.hom ▷ X.unmop
    simp
  μₗ_associativity X Y M := by
    apply Mod_.Hom.ext
    change 𝟙 _ ≫ (α_ M.X Y.unmop X.unmop).inv =
      (α_ M.X Y.unmop X.unmop).inv ≫ (𝟙 _ ▷ X.unmop) ≫ 𝟙 _
    simp
  μₗ_unitality M := by
    apply Mod_.Hom.ext
    change (ρ_ M.X).hom = 𝟙 _ ≫ (ρ_ M.X).hom
    simp

def restrictionLeftLinear : (Mod_.comap (D := D) p).LeftLinear Dᴹᵒᵖ := by
  letI := restrictionLaxLeftLinear p
  letI (X : Dᴹᵒᵖ) (M : Mod_ D B) :
      IsIso (Functor.LaxLeftLinear.μₗ (Mod_.comap (D := D) p) X M) :=
    (restrictionTensorIso p M X.unmop).isIso_hom
  exact ModuleFunctor.leftLinearOfLax (Mod_.comap (D := D) p)

section Linear
variable [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]

instance restriction_additive : (Mod_.comap (D := D) p).Additive where
  map_add := by intros; apply Mod_.Hom.ext; rfl

instance restriction_linear : (Mod_.comap (D := D) p).Linear ℂ where
  map_smul _ _ := by apply Mod_.Hom.ext; rfl

/-- The actual strong additive linear ambient-module restriction functor. -/
def restrictionBundled : Bundled Dᴹᵒᵖ (Mod_ D B) (Mod_ D R) where
  toFunctor := Mod_.comap p
  leftLinear := restrictionLeftLinear p
  additive := inferInstance
  linear := inferInstance

end Linear
end Paper18.Category.BimoduleRelativeTensor.Block
