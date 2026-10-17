import Paper18.Category.ModuleFunctorAdjointStrong

/-! # Rigid cap coordinates for actual native module functors

The action of a diagonal cap is constructed from a genuine lineator.
Commuting with these cap coordinates detects module naturality, by the
actual rigid action adjunction. No module-algebra or splitting property
is an input to this detection theorem.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped MonoidalLeftAction
universe v u vM uM vN uN
namespace Paper18.Category.CentralFunctorAdjointSeparable
open MonoidalLeftAction
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {M : Type uM} [Category.{vM} M] [MonoidalLeftAction C M]
  {N : Type uN} [Category.{vN} N] [MonoidalLeftAction C N]
  (F : M ⥤ N) [F.LeftLinear C]

/-- The actual diagonal cap at a specified actual dual pair. -/
def capComponent (X DX : C) [ExactPairing X DX] :
    actionLeft M X ⋙ F ⋙ actionLeft N DX ⟶ F where
  app m := Functor.LaxLeftLinear.μₗ F DX (X ⊙ₗ m) ≫
    F.map ((ModuleFunctor.actionEvaluation M X DX).app m)
  naturality {m n} f := by
    change (DX ⊴ₗ F.map (X ⊴ₗ f)) ≫
        (Functor.LaxLeftLinear.μₗ F DX (X ⊙ₗ n) ≫
          F.map ((ModuleFunctor.actionEvaluation M X DX).app n)) =
      (Functor.LaxLeftLinear.μₗ F DX (X ⊙ₗ m) ≫
        F.map ((ModuleFunctor.actionEvaluation M X DX).app m)) ≫ F.map f
    rw [Functor.LaxLeftLinear.μₗ_naturality_right_assoc]
    simp only [Category.assoc, ← F.map_comp]
    have hn := (ModuleFunctor.actionEvaluation M X DX).naturality f
    change (DX ⊴ₗ (X ⊴ₗ f)) ≫ (ModuleFunctor.actionEvaluation M X DX).app n =
      (ModuleFunctor.actionEvaluation M X DX).app m ≫ f at hn
    rw [hn]

@[simp] lemma capComponent_app (X DX : C) [ExactPairing X DX] (m : M) :
    (capComponent F X DX).app m =
      Functor.LaxLeftLinear.μₗ F DX (X ⊙ₗ m) ≫
        F.map ((ModuleFunctor.actionEvaluation M X DX).app m) := rfl

/-- The cap coordinate is exactly the actual adjoint transpose of the
inverse lineator. -/
lemma capComponent_eq_transpose (X DX : C) [ExactPairing X DX] (m : M) :
    (capComponent F X DX).app m =
      DX ⊴ₗ Functor.OplaxLeftLinear.δₗ F X m ≫
        (ModuleFunctor.actionEvaluation N X DX).app (F.obj m) :=
  ModuleFunctor.lineator_actionEvaluation_oplax F X DX m

variable {F} {G : M ⥤ N} [G.LeftLinear C] (τ : F ⟶ G)

/-- A genuine module natural transformation commutes with the actual
diagonal cap coordinates. -/
lemma capComponent_comm_of_moduleNatural [ModuleFunctor.IsModuleNatural C τ]
    (X DX : C) [ExactPairing X DX] (m : M) :
    (capComponent F X DX).app m ≫ τ.app m =
      DX ⊴ₗ τ.app (X ⊙ₗ m) ≫ (capComponent G X DX).app m := by
  simp only [capComponent_app, Category.assoc]
  erw [τ.naturality ((ModuleFunctor.actionEvaluation M X DX).app m)]
  rw [← Category.assoc]
  erw [ModuleFunctor.IsModuleNatural.lineator (τ := τ) DX (X ⊙ₗ m)]
  rw [Category.assoc]

/-- At an actual dual pair, cap-coordinate compatibility is precisely
the original lineator compatibility. -/
lemma capComponent_comm_iff (X DX : C) [ExactPairing X DX] (m : M) :
    (capComponent F X DX).app m ≫ τ.app m =
      DX ⊴ₗ τ.app (X ⊙ₗ m) ≫ (capComponent G X DX).app m ↔
    Functor.LaxLeftLinear.μₗ F X m ≫ τ.app (X ⊙ₗ m) =
      X ⊴ₗ τ.app m ≫ Functor.LaxLeftLinear.μₗ G X m := by
  have hi :
      τ.app (X ⊙ₗ m) ≫ Functor.OplaxLeftLinear.δₗ G X m =
          Functor.OplaxLeftLinear.δₗ F X m ≫ X ⊴ₗ τ.app m ↔
      Functor.LaxLeftLinear.μₗ F X m ≫ τ.app (X ⊙ₗ m) =
          X ⊴ₗ τ.app m ≫ Functor.LaxLeftLinear.μₗ G X m := by
    constructor
    · intro h
      apply (cancel_mono (Functor.OplaxLeftLinear.δₗ G X m)).mp
      rw [Category.assoc, h]
      simp only [Category.assoc, Functor.LeftLinear.μₗ_comp_δₗ,
        Functor.LeftLinear.μₗ_comp_δₗ_assoc, Category.comp_id]
    · intro h
      apply (cancel_epi (Functor.LaxLeftLinear.μₗ F X m)).mp
      rw [← Category.assoc, h]
      simp only [Category.assoc, Functor.LeftLinear.μₗ_comp_δₗ, Category.comp_id,
        Functor.LeftLinear.μₗ_comp_δₗ_assoc]
  rw [← hi]
  have hn := (ModuleFunctor.actionEvaluation N X DX).naturality (τ.app m)
  change (DX ⊴ₗ (X ⊴ₗ τ.app m)) ≫
      (ModuleFunctor.actionEvaluation N X DX).app (G.obj m) =
    (ModuleFunctor.actionEvaluation N X DX).app (F.obj m) ≫ τ.app m at hn
  constructor
  · intro h
    apply ((ModuleFunctor.actionAdjunction N X DX).homEquiv _ _).symm.injective
    change (DX ⊴ₗ (τ.app (X ⊙ₗ m) ≫ Functor.OplaxLeftLinear.δₗ G X m)) ≫
        (ModuleFunctor.actionEvaluation N X DX).app (G.obj m) =
      (DX ⊴ₗ (Functor.OplaxLeftLinear.δₗ F X m ≫ X ⊴ₗ τ.app m)) ≫
        (ModuleFunctor.actionEvaluation N X DX).app (G.obj m)
    rw [actionHomRight_comp, actionHomRight_comp, Category.assoc,
      ← capComponent_eq_transpose]
    rw [Category.assoc, hn]
    rw [← Category.assoc, ← capComponent_eq_transpose]
    exact h.symm
  · intro h
    rw [capComponent_eq_transpose, capComponent_eq_transpose]
    simp only [Category.assoc]
    rw [← hn]
    rw [← Category.assoc, ← actionHomRight_comp, ← h, actionHomRight_comp,
      Category.assoc]

variable [RightRigidCategory C]
attribute [local instance 2000] RightRigidCategory.rightDual

/-- The actual diagonal cap equations detect native module naturality
for every actual natural transformation between actual strong module functors. -/
theorem moduleNatural_iff_capComponent :
    ModuleFunctor.IsModuleNatural C τ ↔
      ∀ (X : C) (m : M), (capComponent F X Xᘁ).app m ≫ τ.app m =
        Xᘁ ⊴ₗ τ.app (X ⊙ₗ m) ≫ (capComponent G X Xᘁ).app m := by
  constructor
  · intro h
    letI := h
    exact fun X m => capComponent_comm_of_moduleNatural τ X Xᘁ m
  · intro h
    exact ⟨fun X m => (capComponent_comm_iff τ X Xᘁ m).mp (h X m)⟩

end Paper18.Category.CentralFunctorAdjointSeparable
