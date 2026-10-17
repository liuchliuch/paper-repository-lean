import Paper18.Category.LocalModulesBraiding
import Paper18.Category.FixedBoundaryRestriction
import Paper18.Category.CentralizerClosure

/-!
# The actual crossed balancing map

When actual monodromy with the regular algebra equals an actual algebra
translation, the ambient braiding descends to a relative tensor with the
translated first module. This is the second crossing required in the
fixed-boundary problem. The category of all modules has no assumed braiding.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory CategoryTheory.Limits
open scoped MonObj
universe v u
namespace Paper18.Category.FixedBoundary
open RelativeTensor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  {A : C} [MonObj A]

@[reassoc] private theorem crossing_first_action (M N : Mod_ C A) :
    γ[A,M.X] ▷ N.X ≫ (β_ M.X N.X).hom =
      (α_ A M.X N.X).hom ≫ (A ◁ (β_ M.X N.X).hom) ≫
        (α_ A N.X M.X).inv ≫ (β_ A N.X).hom ▷ M.X ≫
          (α_ N.X A M.X).hom ≫ (N.X ◁ γ[A,M.X]) := by
  rw [braiding_naturality_left]
  change (β_ (A ⊗ M.X) N.X).hom ≫ (N.X ◁ γ[A,M.X]) = _
  rw [braiding_tensor_left_hom]
  simp only [Category.assoc]

@[reassoc] private theorem crossing_second_action (M N : Mod_ C A) :
    (α_ M.X A N.X).hom ≫ (M.X ◁ γ[A,N.X]) ≫ (β_ M.X N.X).hom =
      (β_ M.X A).hom ▷ N.X ≫ (α_ A M.X N.X).hom ≫
        (A ◁ (β_ M.X N.X).hom) ≫ (α_ A N.X M.X).inv ≫ γ[A,N.X] ▷ M.X := by
  rw [braiding_naturality_right]
  change (α_ M.X A N.X).hom ≫ (β_ M.X (A ⊗ N.X)).hom ≫ γ[A,N.X] ▷ M.X = _
  rw [braiding_tensor_right_hom]
  simp

variable (e : A ≅ A) [IsMonHom e.hom]

/-- The actual translated balancing relation absorbs the actual
regular-algebra monodromy. -/
@[reassoc] theorem translated_braid_action_balanced
    {M N : Mod_ C A} {Z : C} (q : N.X ⊗ M.X ⟶ Z)
    (hq : RelativeTensor.Balanced N ((Mod_.comap e.hom).obj M) q)
    (hN : (doubleBraiding A N.X).hom = e.hom ▷ N.X) :
    (β_ A N.X).hom ▷ M.X ≫ (α_ N.X A M.X).hom ≫
      (N.X ◁ γ[A,M.X]) ≫ q = γ[A,N.X] ▷ M.X ≫ q := by
  apply (cancel_epi ((e.hom ▷ N.X) ▷ M.X)).mp
  have hh : (e.hom ▷ N.X) ≫ γ[A,N.X] =
      (β_ A N.X).hom ≫ rightAction N := by
    rw [← hN]
    simp only [doubleBraiding, Iso.trans_hom, rightAction, Category.assoc]
  rw [← comp_whiskerRight_assoc, braiding_naturality_left, comp_whiskerRight]
  simp only [Category.assoc]
  rw [associator_naturality_middle_assoc]
  have hb : rightAction N ▷ M.X ≫ q =
      (α_ N.X A M.X).hom ≫ (N.X ◁ (e.hom ▷ M.X)) ≫
        (N.X ◁ γ[A,M.X]) ≫ q := by
    change rightAction N ▷ M.X ≫ q =
      ((α_ N.X A M.X).hom ≫ (N.X ◁ ((e.hom ▷ M.X) ≫ γ[A,M.X]))) ≫ q at hq
    simpa only [whiskerLeft_comp, Category.assoc] using hq
  rw [← hb]
  rw [← comp_whiskerRight_assoc, ← hh, comp_whiskerRight]
  simp only [Category.assoc]

/-- The positive ambient crossing is balanced into the actual translated
relative tensor whenever its algebra monodromy is that translation. -/
theorem translated_balanced_braiding
    {M N : Mod_ C A} {Z : C} (q : N.X ⊗ M.X ⟶ Z)
    (hq : RelativeTensor.Balanced N ((Mod_.comap e.hom).obj M) q)
    (hN : (doubleBraiding A N.X).hom = e.hom ▷ N.X) :
    RelativeTensor.Balanced M N ((β_ M.X N.X).hom ≫ q) := by
  unfold RelativeTensor.Balanced parallelLeft parallelRight rightAction
  simp only [comp_whiskerRight, Category.assoc]
  rw [crossing_first_action_assoc, translated_braid_action_balanced e q hq hN]
  simpa only [Category.assoc] using
    congrArg (fun k => k ≫ q) (crossing_second_action M N).symm

/-- The same actual translated balancing identity proves module linearity. -/
theorem translated_linear_braiding
    {M N P : Mod_ C A} (q : N.X ⊗ M.X ⟶ P.X)
    (hq : RelativeTensor.Balanced N ((Mod_.comap e.hom).obj M) q)
    (hN : (doubleBraiding A N.X).hom = e.hom ▷ N.X)
    (hlin : (A ◁ q) ≫ γ[A,P.X] =
      (α_ A N.X M.X).inv ≫ γ[A,N.X] ▷ M.X ≫ q) :
    (α_ A M.X N.X).inv ≫ γ[A,M.X] ▷ N.X ≫ (β_ M.X N.X).hom ≫ q =
      (A ◁ ((β_ M.X N.X).hom ≫ q)) ≫ γ[A,P.X] := by
  rw [crossing_first_action_assoc]
  simp only [Iso.inv_hom_id_assoc]
  rw [translated_braid_action_balanced e q hq hN, whiskerLeft_comp]
  simp only [Category.assoc]
  rw [hlin]

variable [RightRigidCategory C] [HasCoequalizers C] [IsCommMonObj A]

/-- The actual ambient braiding descends to an actual crossed module map. -/
def translatedBraidingHom (M N : Mod_ C A)
    (hN : (doubleBraiding A N.X).hom = e.hom ▷ N.X) :
    M ⊗ N ⟶ N ⊗ (Mod_.comap e.hom).obj M :=
  descModule M N _ ((β_ M.X N.X).hom ≫ π N ((Mod_.comap e.hom).obj M))
    (translated_balanced_braiding e _ (condition N ((Mod_.comap e.hom).obj M)) hN)
    (translated_linear_braiding e _ (condition N ((Mod_.comap e.hom).obj M)) hN
      (π_action N ((Mod_.comap e.hom).obj M)))

@[reassoc (attr := simp)] theorem π_translatedBraidingHom (M N : Mod_ C A)
    (hN : (doubleBraiding A N.X).hom = e.hom ▷ N.X) :
    π M N ≫ (translatedBraidingHom e M N hN).hom =
      (β_ M.X N.X).hom ≫ π N ((Mod_.comap e.hom).obj M) :=
  π_desc M N _ _

/-- Naturality in the translated first module holds before the actual
balancing quotient. -/
@[reassoc] theorem translatedBraiding_naturality_left
    {M M' : Mod_ C A} (f : M ⟶ M') (N : Mod_ C A)
    (hN : (doubleBraiding A N.X).hom = e.hom ▷ N.X) :
    (f ▷ N) ≫ translatedBraidingHom e M' N hN =
      translatedBraidingHom e M N hN ≫ (N ◁ (Mod_.comap e.hom).map f) := by
  apply module_hom_ext
  change π M N ≫ (f ▷ N).hom ≫ (translatedBraidingHom e M' N hN).hom =
    π M N ≫ (translatedBraidingHom e M N hN).hom ≫
      (N ◁ (Mod_.comap e.hom).map f).hom
  rw [π_whiskerRight_assoc, π_translatedBraidingHom,
    π_translatedBraidingHom_assoc, π_whiskerLeft]
  exact braiding_naturality_left_assoc f.hom N.X _

/-- Naturality in any actual module map preserving the specified
translation follows from ambient braiding naturality. -/
@[reassoc] theorem translatedBraiding_naturality_right
    (M : Mod_ C A) {N N' : Mod_ C A} (f : N ⟶ N')
    (hN : (doubleBraiding A N.X).hom = e.hom ▷ N.X)
    (hN' : (doubleBraiding A N'.X).hom = e.hom ▷ N'.X) :
    (M ◁ f) ≫ translatedBraidingHom e M N' hN' =
      translatedBraidingHom e M N hN ≫ (f ▷ (Mod_.comap e.hom).obj M) := by
  apply module_hom_ext
  change π M N ≫ (M ◁ f).hom ≫ (translatedBraidingHom e M N' hN').hom =
    π M N ≫ (translatedBraidingHom e M N hN).hom ≫
      (f ▷ (Mod_.comap e.hom).obj M).hom
  rw [π_whiskerLeft_assoc, π_translatedBraidingHom,
    π_translatedBraidingHom_assoc, π_whiskerRight]
  exact braiding_naturality_right_assoc M.X f.hom _

/-- The actual crossed quotient map is epimorphic, because its composite
with the balancing quotient is the ambient braiding followed by another
balancing quotient. -/
instance translatedBraidingHom_epi (M N : Mod_ C A)
    (hN : (doubleBraiding A N.X).hom = e.hom ▷ N.X) :
    Epi (translatedBraidingHom e M N hN) := by
  let c := translatedBraidingHom e M N hN
  haveI : Epi (π M N ≫ c.hom) := by
    dsimp only [c]
    rw [π_translatedBraidingHom]
    infer_instance
  haveI : Epi c.hom := epi_of_epi (π M N) c.hom
  exact (Mod_.forget (D := C) A).epi_of_epi_map (inferInstanceAs (Epi c.hom))

end Paper18.Category.FixedBoundary
