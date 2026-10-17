import Paper18.Category.BimoduleRelativeTensorFunctorLineator

/-! # Actual module linearity of the ambient tensor comparison -/
noncomputable section
set_option maxHeartbeats 1000000
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u
namespace Paper18.Category.BimoduleRelativeTensor
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [HasCoequalizers D] [LeftRigidCategory D] [RightRigidCategory D]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
variable {R S : D} [MonObj R] [MonObj S] (P : Native R S)

@[reassoc]
lemma moduleπ_left (N : Mod_ D S) :
    R ◁ moduleπ P N ≫ γ[R,((tensorFunctor P).obj N).X] =
      (α_ R P.X.X N.X).inv ≫ γ[R,P.X.X] ▷ N.X ≫ moduleπ P N :=
  π_left P (moduleAsNative N)

instance moduleπ_right_left_epi (N : Mod_ D S) (X Y : D) :
    Epi (Y ◁ (moduleπ P N ▷ X)) := by
  exact inferInstanceAs (Epi ((tensorRight X ⋙ tensorLeft Y).map
    (coequalizer.π (γ[mop S,P.X].hom ▷ N.X)
      ((α_ P.X.X S N.X).hom ≫ P.X.X ◁ γ[S,N.X]))))

lemma lineatorRaw_linear (N : Mod_ D S) (X : D) :
    ((α_ R ((tensorFunctor P).obj N).X X).inv ≫
        γ[R,((tensorFunctor P).obj N).X] ▷ X) ≫ lineatorRaw P N X =
      R ◁ lineatorRaw P N X ≫
        γ[R,((tensorFunctor P).obj (RelativeTensor.ambientTensor N X)).X] := by
  apply (cancel_epi (R ◁ (moduleπ P N ▷ X))).mp
  calc
    _ = (α_ R (P.X.X ⊗ N.X) X).inv ≫
        (R ◁ moduleπ P N ≫ γ[R,((tensorFunctor P).obj N).X]) ▷ X ≫
          lineatorRaw P N X := by monoidal
    _ = (α_ R (P.X.X ⊗ N.X) X).inv ≫
        ((α_ R P.X.X N.X).inv ≫ γ[R,P.X.X] ▷ N.X ≫ moduleπ P N) ▷ X ≫
          lineatorRaw P N X := by rw [moduleπ_left]
    _ = R ◁ (α_ P.X.X N.X X).hom ≫
        (α_ R P.X.X (N.X ⊗ X)).inv ≫ γ[R,P.X.X] ▷ (N.X ⊗ X) ≫
          moduleπ P (RelativeTensor.ambientTensor N X) := by
      simp only [comp_whiskerRight, assoc]
      rw [moduleπ_lineatorRaw]
      monoidal
    _ = _ := by
      have ht : R ◁ moduleπ P (RelativeTensor.ambientTensor N X) ≫
          γ[R,((tensorFunctor P).obj (RelativeTensor.ambientTensor N X)).X] =
          (α_ R P.X.X (N.X ⊗ X)).inv ≫ γ[R,P.X.X] ▷ (N.X ⊗ X) ≫
            moduleπ P (RelativeTensor.ambientTensor N X) :=
        moduleπ_left P (RelativeTensor.ambientTensor N X)
      rw [← ht]
      rw [← whiskerLeft_comp_assoc, ← moduleπ_lineatorRaw]
      rw [whiskerLeft_comp, assoc]

/-- The actual tensor comparison is a morphism of actual left modules. -/
def lineatorHom (N : Mod_ D S) (X : D) :
    RelativeTensor.ambientTensor ((tensorFunctor P).obj N) X ⟶
      (tensorFunctor P).obj (RelativeTensor.ambientTensor N X) :=
  Mod_.Hom.mk' (lineatorRaw P N X) (lineatorRaw_linear P N X)

/-- The actual ambient inverse of the comparison is also module linear. -/
def lineatorIso (N : Mod_ D S) (X : D) :
    RelativeTensor.ambientTensor ((tensorFunctor P).obj N) X ≅
      (tensorFunctor P).obj (RelativeTensor.ambientTensor N X) where
  hom := lineatorHom P N X
  inv := by
    letI : IsMod_Hom R
        (M := (RelativeTensor.ambientTensor ((tensorFunctor P).obj N) X).X)
        (N := ((tensorFunctor P).obj (RelativeTensor.ambientTensor N X)).X)
        (lineatorRawIso P N X).hom := (lineatorHom P N X).isMod_Hom
    exact ⟨(lineatorRawIso P N X).inv⟩
  hom_inv_id := by apply Mod_.Hom.ext; exact (lineatorRawIso P N X).hom_inv_id
  inv_hom_id := by apply Mod_.Hom.ext; exact (lineatorRawIso P N X).inv_hom_id

end Paper18.Category.BimoduleRelativeTensor
