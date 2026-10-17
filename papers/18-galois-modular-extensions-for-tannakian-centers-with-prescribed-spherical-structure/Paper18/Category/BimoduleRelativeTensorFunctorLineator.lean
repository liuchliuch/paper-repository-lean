import Paper18.Category.BimoduleRelativeTensorFunctorBasic

/-! # The actual ambient tensor comparison for relative tensor functors -/
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

lemma lineator_balanced (N : Mod_ D S) (X : D) :
    (γ[mop S,P.X].hom ▷ N.X) ▷ X ≫
        (α_ P.X.X N.X X).hom ≫ moduleπ P (RelativeTensor.ambientTensor N X) =
      ((α_ P.X.X S N.X).hom ≫ P.X.X ◁ γ[S,N.X]) ▷ X ≫
        (α_ P.X.X N.X X).hom ≫ moduleπ P (RelativeTensor.ambientTensor N X) := by
  calc
    _ = (α_ (P.X.X ⊗ S) N.X X).hom ≫ γ[mop S,P.X].hom ▷ (N.X ⊗ X) ≫
        moduleπ P (RelativeTensor.ambientTensor N X) := by monoidal
    _ = (α_ (P.X.X ⊗ S) N.X X).hom ≫ (α_ P.X.X S (N.X ⊗ X)).hom ≫
        P.X.X ◁ ((α_ S N.X X).inv ≫ γ[S,N.X] ▷ X) ≫
          moduleπ P (RelativeTensor.ambientTensor N X) := by
      have h : γ[mop S,P.X].hom ▷ (N.X ⊗ X) ≫
          moduleπ P (RelativeTensor.ambientTensor N X) =
          (α_ P.X.X S (N.X ⊗ X)).hom ≫
            P.X.X ◁ ((α_ S N.X X).inv ≫ γ[S,N.X] ▷ X) ≫
              moduleπ P (RelativeTensor.ambientTensor N X) :=
        moduleπ_condition P (RelativeTensor.ambientTensor N X)
      rw [h]
    _ = _ := by monoidal

/-- The actual comparison of balancing coequalizers with ambient tensor. -/
def lineatorRaw (N : Mod_ D S) (X : D) :
    ((tensorFunctor P).obj N).X ⊗ X ⟶
      ((tensorFunctor P).obj (RelativeTensor.ambientTensor N X)).X :=
  (PreservesCoequalizer.iso (tensorRight X)
    (γ[mop S,P.X].hom ▷ N.X)
    ((α_ P.X.X S N.X).hom ≫ P.X.X ◁ γ[S,N.X])).inv ≫
      coequalizer.desc ((α_ P.X.X N.X X).hom ≫
        moduleπ P (RelativeTensor.ambientTensor N X)) (by
          simpa only [assoc] using lineator_balanced P N X)

@[reassoc (attr := simp)]
lemma moduleπ_lineatorRaw (N : Mod_ D S) (X : D) :
    moduleπ P N ▷ X ≫ lineatorRaw P N X =
      (α_ P.X.X N.X X).hom ≫ moduleπ P (RelativeTensor.ambientTensor N X) :=
  π_tensor_id_preserves_coequalizer_inv_desc _ _ _ _

lemma lineatorInv_balanced (N : Mod_ D S) (X : D) :
    γ[mop S,P.X].hom ▷ (N.X ⊗ X) ≫ (α_ P.X.X N.X X).inv ≫ moduleπ P N ▷ X =
      (α_ P.X.X S (N.X ⊗ X)).hom ≫
        P.X.X ◁ ((α_ S N.X X).inv ≫ γ[S,N.X] ▷ X) ≫
          (α_ P.X.X N.X X).inv ≫ moduleπ P N ▷ X := by
  calc
    _ = (α_ (P.X.X ⊗ S) N.X X).inv ≫
        (γ[mop S,P.X].hom ▷ N.X ≫ moduleπ P N) ▷ X := by monoidal
    _ = (α_ (P.X.X ⊗ S) N.X X).inv ≫
        ((α_ P.X.X S N.X).hom ≫ P.X.X ◁ γ[S,N.X] ≫ moduleπ P N) ▷ X := by
      rw [moduleπ_condition]
    _ = _ := by monoidal

def lineatorInvRaw (N : Mod_ D S) (X : D) :
    ((tensorFunctor P).obj (RelativeTensor.ambientTensor N X)).X ⟶
      ((tensorFunctor P).obj N).X ⊗ X :=
  coequalizer.desc ((α_ P.X.X N.X X).inv ≫ moduleπ P N ▷ X) (by
    simpa only [assoc] using lineatorInv_balanced P N X)

@[reassoc (attr := simp)]
lemma moduleπ_lineatorInvRaw (N : Mod_ D S) (X : D) :
    moduleπ P (RelativeTensor.ambientTensor N X) ≫ lineatorInvRaw P N X =
      (α_ P.X.X N.X X).inv ≫ moduleπ P N ▷ X := coequalizer.π_desc _ _

instance moduleπ_right_epi (N : Mod_ D S) (X : D) : Epi (moduleπ P N ▷ X) := by
  exact inferInstanceAs (Epi ((tensorRight X).map
    (coequalizer.π (γ[mop S,P.X].hom ▷ N.X)
      ((α_ P.X.X S N.X).hom ≫ P.X.X ◁ γ[S,N.X]))))

def lineatorRawIso (N : Mod_ D S) (X : D) :
    ((tensorFunctor P).obj N).X ⊗ X ≅
      ((tensorFunctor P).obj (RelativeTensor.ambientTensor N X)).X where
  hom := lineatorRaw P N X
  inv := lineatorInvRaw P N X
  hom_inv_id := by
    apply (cancel_epi (moduleπ P N ▷ X)).mp
    rw [moduleπ_lineatorRaw_assoc, moduleπ_lineatorInvRaw, Iso.hom_inv_id_assoc, comp_id]
  inv_hom_id := by
    apply (cancel_epi (moduleπ P (RelativeTensor.ambientTensor N X))).mp
    rw [moduleπ_lineatorInvRaw_assoc, moduleπ_lineatorRaw, Iso.inv_hom_id_assoc, comp_id]

end Paper18.Category.BimoduleRelativeTensor
