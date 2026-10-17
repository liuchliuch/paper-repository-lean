import Paper18.Category.GraphPicardTensorTransposeMonoidal

/-! # Actual cap unit insertions and rigid transposition -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal
universe v u v' u'
namespace Paper18.Category.GraphPicard
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {E : Type u'} [Category.{v'} E] [MonoidalCategory E]

/-- A strong tensor functor transports the genuine unit insertion into
the tensor of two genuine unit-based arrows. -/
lemma map_capUnitInsertion (H : C ⥤ E) [H.Monoidal] {U V : C}
    (a : 𝟙_ C ⟶ U) (b : 𝟙_ C ⟶ V) :
    (λ_ (𝟙_ E)).inv ≫ ((ε H ≫ H.map a) ⊗ₘ (ε H ≫ H.map b)) ≫ μ H U V =
      ε H ≫ H.map ((λ_ (𝟙_ C)).inv ≫ (a ⊗ₘ b)) := by
  rw [← tensorHom_comp_tensorHom_assoc, μ_natural, ε_tensorHom_comp_μ_assoc,
    ← leftUnitor_inv_naturality_assoc, Iso.inv_hom_id_assoc, ← H.map_comp]

attribute [local instance 2000] RightRigidCategory.rightDual
variable [RightRigidCategory C]
  (F G : C ⥤ E) [F.Monoidal] [G.Monoidal]
  (e : ∀ X : C, F.obj (dual C X) ⊗ G.obj X ⟶ 𝟙_ E)
  (he : ∀ {X Y : C} (f : X ⟶ Y),
    F.map (dualMap C f) ▷ G.obj X ≫ e X =
      F.obj (dual C Y) ◁ G.map f ≫ e Y)

/-- Actual unit insertion normalization suffices for the actual unit
condition of the cap transpose. -/
theorem capFamilyNatTrans_unit_of_insertion
    (h : (λ_ (𝟙_ E)).inv ≫
      ((ε F ≫ F.map (dualUnitIso (C := C)).inv) ⊗ₘ ε G) ≫ e (𝟙_ C) = 𝟙 _) :
    ε G ≫ (capFamilyNatTrans F G e he).app (𝟙_ C) = ε F := by
  apply capFamilyNatTrans_unit_of_cap_unit F G e he
  apply (cancel_epi ((ε F ≫ F.map (dualUnitIso (C := C)).inv) ▷ (𝟙_ E))).mp
  have hh := congrArg ((λ_ (𝟙_ E)).hom ≫ ·) h
  simp only [← assoc, Iso.hom_inv_id, id_comp, comp_id] at hh
  rw [← reassoc_of% (MonoidalCategory.tensorHom_def
    (ε F ≫ F.map (dualUnitIso (C := C)).inv) (ε G)), hh,
    rightUnitor_naturality_assoc]
  simp only [assoc]
  rw [← F.map_comp_assoc, Iso.inv_hom_id, F.map_id, id_comp,
    Functor.Monoidal.ε_η, comp_id]
  exact unitors_equal (C := E)

end Paper18.Category.GraphPicard
