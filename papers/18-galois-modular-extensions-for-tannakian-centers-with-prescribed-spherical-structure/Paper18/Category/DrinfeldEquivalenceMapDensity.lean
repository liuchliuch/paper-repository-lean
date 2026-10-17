import Paper18.Category.DrinfeldEquivalenceMapBasic

/-! # Extending the half-braiding hexagon from an essential image -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u
namespace Paper18.Category.DrinfeldEquivalence
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]

@[reassoc]
lemma tensorNat_naturality {X U V : D} (b : tensorLeft X ≅ tensorRight X) (f : U ⟶ V) :
    X ◁ f ≫ b.hom.app V = b.hom.app U ≫ f ▷ X := b.hom.naturality f

def hexagonRHS {X : D} (b : tensorLeft X ≅ tensorRight X) (U V : D) :
    X ⊗ (U ⊗ V) ⟶ (U ⊗ V) ⊗ X :=
  (α_ X U V).inv ≫ b.hom.app U ▷ V ≫ (α_ U X V).hom ≫ U ◁ b.hom.app V ≫ (α_ U V X).inv

lemma hexagonRHS_natural_left {X U U' : D} (b : tensorLeft X ≅ tensorRight X)
    (f : U ⟶ U') (V : D) :
    X ◁ (f ▷ V) ≫ hexagonRHS b U' V =
      hexagonRHS b U V ≫ (f ▷ V) ▷ X := by
  calc
    _ = (α_ X U V).inv ≫ (X ◁ f ≫ b.hom.app U') ▷ V ≫
        (α_ U' X V).hom ≫ U' ◁ b.hom.app V ≫ (α_ U' V X).inv := by
      dsimp [hexagonRHS]
      monoidal
    _ = (α_ X U V).inv ≫ (b.hom.app U ≫ f ▷ X) ▷ V ≫
        (α_ U' X V).hom ≫ U' ◁ b.hom.app V ≫ (α_ U' V X).inv := by
      rw [tensorNat_naturality b f]
    _ = _ := by
      simp only [hexagonRHS, comp_whiskerRight, assoc]
      rw [associator_naturality_left_assoc, ← whisker_exchange_assoc]
      dsimp only [tensorLeft, tensorRight, curriedTensor, Functor.flip]
      rw [associator_inv_naturality_left]

lemma hexagonRHS_natural_right {X V V' : D} (b : tensorLeft X ≅ tensorRight X)
    (U : D) (f : V ⟶ V') :
    X ◁ (U ◁ f) ≫ hexagonRHS b U V' =
      hexagonRHS b U V ≫ (U ◁ f) ▷ X := by
  calc
    _ = (α_ X U V).inv ≫ b.hom.app U ▷ V ≫ (α_ U X V).hom ≫
        U ◁ (X ◁ f ≫ b.hom.app V') ≫ (α_ U V' X).inv := by
      simp only [hexagonRHS, assoc]
      rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc]
      dsimp only [tensorLeft, tensorRight, curriedTensor, Functor.flip]
      rw [associator_naturality_right_assoc, ← whiskerLeft_comp_assoc]
    _ = (α_ X U V).inv ≫ b.hom.app U ▷ V ≫ (α_ U X V).hom ≫
        U ◁ (b.hom.app V ≫ f ▷ X) ≫ (α_ U V' X).inv := by
      rw [tensorNat_naturality b f]
    _ = _ := by
      simp only [hexagonRHS, whiskerLeft_comp, assoc]
      rw [associator_inv_naturality_middle]

lemma hexagon_of_iso_left {X U U' : D} (b : tensorLeft X ≅ tensorRight X)
    (e : U ≅ U') (V : D)
    (h : b.hom.app (U ⊗ V) = hexagonRHS b U V) :
    b.hom.app (U' ⊗ V) = hexagonRHS b U' V := by
  apply (cancel_epi (X ◁ (e.hom ▷ V))).mp
  rw [tensorNat_naturality b (e.hom ▷ V), h, hexagonRHS_natural_left]

lemma hexagon_of_iso_right {X V V' : D} (b : tensorLeft X ≅ tensorRight X)
    (U : D) (e : V ≅ V')
    (h : b.hom.app (U ⊗ V) = hexagonRHS b U V) :
    b.hom.app (U ⊗ V') = hexagonRHS b U V' := by
  apply (cancel_epi (X ◁ (U ◁ e.hom))).mp
  rw [tensorNat_naturality b (U ◁ e.hom), h, hexagonRHS_natural_right]

lemma comm_of_iso {A B U V : D} (a : tensorLeft A ≅ tensorRight A)
    (b : tensorLeft B ≅ tensorRight B) (f : A ⟶ B) (e : U ≅ V)
    (h : f ▷ U ≫ b.hom.app U = a.hom.app U ≫ U ◁ f) :
    f ▷ V ≫ b.hom.app V = a.hom.app V ≫ V ◁ f := by
  apply (cancel_epi (A ◁ e.hom)).mp
  rw [whisker_exchange_assoc, tensorNat_naturality b e.hom,
    reassoc_of% h, whisker_exchange, ← tensorNat_naturality_assoc a e.hom]

end Paper18.Category.DrinfeldEquivalence
