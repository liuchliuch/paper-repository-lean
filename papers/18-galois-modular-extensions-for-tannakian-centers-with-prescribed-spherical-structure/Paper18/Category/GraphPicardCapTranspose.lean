import Paper18.Category.PivotalFunctor

/-! # Rigid transposition of actual cap families

The transposition is the actual rigid Hom equivalence, normalized by the
actual right unitor. Its inverse is the actual evaluation composite.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u v' u'
namespace Paper18.Category.GraphPicard
variable {E : Type u} [Category.{v} E] [MonoidalCategory E]

/-- The actual cap-to-arrow bijection supplied by an actual exact pairing. -/
def capTransposeEquiv (U V P : E) [ExactPairing U V] :
    (V ⊗ P ⟶ 𝟙_ E) ≃ (P ⟶ U) where
  toFun e := tensorLeftHomEquiv P U V (𝟙_ E) e ≫ (ρ_ U).hom
  invFun h := (tensorLeftHomEquiv P U V (𝟙_ E)).symm (h ≫ (ρ_ U).inv)
  left_inv e := by
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact (tensorLeftHomEquiv P U V (𝟙_ E)).symm_apply_apply e
  right_inv h := by
    dsimp only
    rw [Equiv.apply_symm_apply]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The inverse transpose is exactly the genuine evaluation after the
actual left whisker of the original arrow. -/
lemma capTransposeEquiv_symm_apply (U V P : E) [ExactPairing U V] (h : P ⟶ U) :
    (capTransposeEquiv U V P).symm h = V ◁ h ≫ ε_ U V := by
  dsimp only [capTransposeEquiv, Equiv.coe_fn_symm_mk, tensorLeftHomEquiv]
  simp only [whiskerLeft_comp, Category.assoc]
  monoidal

/-- An actual cap is recovered exactly from its actual transpose. -/
@[reassoc] lemma capTransposeEquiv_evaluation (U V P : E) [ExactPairing U V]
    (e : V ⊗ P ⟶ 𝟙_ E) :
    V ◁ capTransposeEquiv U V P e ≫ ε_ U V = e := by
  rw [← capTransposeEquiv_symm_apply]
  exact (capTransposeEquiv U V P).symm_apply_apply e

/-- Testing against the actual evaluation detects equality of arrows. -/
lemma cap_evaluation_injective (U V P : E) [ExactPairing U V]
    {f g : P ⟶ U} (h : V ◁ f ≫ ε_ U V = V ◁ g ≫ ε_ U V) : f = g := by
  apply (capTransposeEquiv U V P).symm.injective
  simpa only [capTransposeEquiv_symm_apply] using h

variable {C : Type u'} [Category.{v'} C] [MonoidalCategory C] [RightRigidCategory C]
attribute [local instance 2000] RightRigidCategory.rightDual
variable (F : C ⥤ E) [F.Monoidal]

/-- Strong monoidal transport preserves the actual naturality equation
of the dual evaluation. No chosen dual in the target is required. -/
@[reassoc] lemma mappedEvaluation_naturality {X Y : C} (f : X ⟶ Y) :
    F.map (dualMap C f) ▷ F.obj X ≫
        @ExactPairing.evaluation E _ _ (F.obj X) (F.obj (dual C X))
          (mapExactPairing F X (dual C X)) =
      F.obj (dual C Y) ◁ F.map f ≫
        @ExactPairing.evaluation E _ _ (F.obj Y) (F.obj (dual C Y))
          (mapExactPairing F Y (dual C Y)) := by
  change F.map (dualMap C f) ▷ F.obj X ≫
      Functor.LaxMonoidal.μ F (dual C X) X ≫ F.map (ε_ X (dual C X)) ≫
        Functor.OplaxMonoidal.η F =
    F.obj (dual C Y) ◁ F.map f ≫
      Functor.LaxMonoidal.μ F (dual C Y) Y ≫ F.map (ε_ Y (dual C Y)) ≫
        Functor.OplaxMonoidal.η F
  rw [Functor.LaxMonoidal.μ_natural_left_assoc,
    Functor.LaxMonoidal.μ_natural_right_assoc,
    ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  exact congrArg (fun k => Functor.LaxMonoidal.μ F (dual C Y) X ≫ F.map k ≫
    Functor.OplaxMonoidal.η F) (rightAdjointMate_comp_evaluation f)

/-- A genuinely dinatural cap family transposes to an actual natural
transformation. The required naturality is proved by testing against the
actual transported evaluation. -/
def capFamilyNatTrans (G : C ⥤ E)
    (e : ∀ X : C, F.obj (dual C X) ⊗ G.obj X ⟶ 𝟙_ E)
    (he : ∀ {X Y : C} (f : X ⟶ Y),
      F.map (dualMap C f) ▷ G.obj X ≫ e X =
        F.obj (dual C Y) ◁ G.map f ≫ e Y) : G ⟶ F where
  app X := by
    letI := mapExactPairing F X (dual C X)
    exact capTransposeEquiv (F.obj X) (F.obj (dual C X)) (G.obj X) (e X)
  naturality {X Y} f := by
    letI := mapExactPairing F X (dual C X)
    letI := mapExactPairing F Y (dual C Y)
    apply cap_evaluation_injective (F.obj Y) (F.obj (dual C Y)) (G.obj X)
    simp only [whiskerLeft_comp, Category.assoc]
    rw [capTransposeEquiv_evaluation, ← mappedEvaluation_naturality F f,
      whisker_exchange_assoc, capTransposeEquiv_evaluation]
    exact (he f).symm

@[reassoc] lemma capFamilyNatTrans_evaluation (G : C ⥤ E)
    (e : ∀ X : C, F.obj (dual C X) ⊗ G.obj X ⟶ 𝟙_ E)
    (he : ∀ {X Y : C} (f : X ⟶ Y),
      F.map (dualMap C f) ▷ G.obj X ≫ e X =
        F.obj (dual C Y) ◁ G.map f ≫ e Y) (X : C) :
    F.obj (dual C X) ◁ (capFamilyNatTrans F G e he).app X ≫
      @ExactPairing.evaluation E _ _ (F.obj X) (F.obj (dual C X))
        (mapExactPairing F X (dual C X)) = e X := by
  letI := mapExactPairing F X (dual C X)
  exact capTransposeEquiv_evaluation _ _ _ _

end Paper18.Category.GraphPicard
