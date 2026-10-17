import Paper18.Category.FixedBoundaryModuleStrong
import Mathlib.CategoryTheory.Monoidal.Action.End

/-! # Actual composition of native strong module functors -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalLeftAction
universe v u vM uM vN uN vP uP
namespace Paper18.Category.ModuleAlphaInduction
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {M : Type uM} [Category.{vM} M] [MonoidalLeftAction C M]
  {N : Type uN} [Category.{vN} N] [MonoidalLeftAction C N]
  {P : Type uP} [Category.{vP} P] [MonoidalLeftAction C P]
  (F : M ⥤ N) (G : N ⥤ P) [F.LeftLinear C] [G.LeftLinear C]

/-- Composite lineators are the actual outer lineator followed by the
actual image of the inner lineator. -/
def compLaxLeftLinear : (F ⋙ G).LaxLeftLinear C where
  μₗ X m := Functor.LaxLeftLinear.μₗ G X (F.obj m) ≫ G.map (Functor.LaxLeftLinear.μₗ F X m)
  μₗ_naturality_left {X X'} f m := by
    change f ⊵ₗ G.obj (F.obj m) ≫
      (Functor.LaxLeftLinear.μₗ G X' (F.obj m) ≫ G.map (Functor.LaxLeftLinear.μₗ F X' m)) =
      (Functor.LaxLeftLinear.μₗ G X (F.obj m) ≫ G.map (Functor.LaxLeftLinear.μₗ F X m)) ≫
        G.map (F.map (f ⊵ₗ m))
    rw [Functor.LaxLeftLinear.μₗ_naturality_left_assoc]
    simp only [Category.assoc, ← G.map_comp, Functor.LaxLeftLinear.μₗ_naturality_left]
  μₗ_naturality_right X {m n} f := by
    change X ⊴ₗ G.map (F.map f) ≫
      (Functor.LaxLeftLinear.μₗ G X (F.obj n) ≫ G.map (Functor.LaxLeftLinear.μₗ F X n)) =
      (Functor.LaxLeftLinear.μₗ G X (F.obj m) ≫ G.map (Functor.LaxLeftLinear.μₗ F X m)) ≫
        G.map (F.map (X ⊴ₗ f))
    rw [Functor.LaxLeftLinear.μₗ_naturality_right_assoc]
    simp only [Category.assoc, ← G.map_comp, Functor.LaxLeftLinear.μₗ_naturality_right]
  μₗ_associativity X Y m := by
    change (Functor.LaxLeftLinear.μₗ G (X ⊗ Y) (F.obj m) ≫
      G.map (Functor.LaxLeftLinear.μₗ F (X ⊗ Y) m)) ≫ G.map (F.map (αₗ X Y m).hom) =
      (αₗ X Y (G.obj (F.obj m))).hom ≫
        X ⊴ₗ (Functor.LaxLeftLinear.μₗ G Y (F.obj m) ≫ G.map (Functor.LaxLeftLinear.μₗ F Y m)) ≫
          (Functor.LaxLeftLinear.μₗ G X (F.obj (Y ⊙ₗ m)) ≫
            G.map (Functor.LaxLeftLinear.μₗ F X (Y ⊙ₗ m)))
    simp only [Category.assoc, ← G.map_comp]
    rw [Functor.LaxLeftLinear.μₗ_associativity F, G.map_comp, G.map_comp]
    rw [← Category.assoc, ← Category.assoc, Functor.LaxLeftLinear.μₗ_associativity G]
    simp only [Category.assoc, actionHomRight_comp]
    rw [Functor.LaxLeftLinear.μₗ_naturality_right_assoc]
  μₗ_unitality m := by
    change (λₗ (G.obj (F.obj m))).hom =
      (Functor.LaxLeftLinear.μₗ G (𝟙_ C) (F.obj m) ≫ G.map (Functor.LaxLeftLinear.μₗ F (𝟙_ C) m)) ≫
        G.map (F.map (λₗ m).hom)
    rw [Category.assoc, ← G.map_comp, ← Functor.LaxLeftLinear.μₗ_unitality,
      ← Functor.LaxLeftLinear.μₗ_unitality]

/-- Actual composite strong module functors. -/
instance compLeftLinear : (F ⋙ G).LeftLinear C := by
  letI := compLaxLeftLinear (C := C) F G
  letI (X : C) (m : M) : IsIso (Functor.LaxLeftLinear.μₗ (F ⋙ G) X m) := by
    change IsIso (Functor.LaxLeftLinear.μₗ G X (F.obj m) ≫ G.map (Functor.LaxLeftLinear.μₗ F X m))
    infer_instance
  exact ModuleFunctor.leftLinearOfLax (C := C) (F ⋙ G)

@[simp] theorem comp_μ (X : C) (m : M) :
    Functor.LaxLeftLinear.μₗ (F ⋙ G) X m =
      Functor.LaxLeftLinear.μₗ G X (F.obj m) ≫ G.map (Functor.LaxLeftLinear.μₗ F X m) := rfl

@[simp] theorem comp_δ (X : C) (m : M) :
    Functor.OplaxLeftLinear.δₗ (F ⋙ G) X m =
      G.map (Functor.OplaxLeftLinear.δₗ F X m) ≫ Functor.OplaxLeftLinear.δₗ G X (F.obj m) := by
  change inv (Functor.LaxLeftLinear.μₗ G X (F.obj m) ≫
    G.map (Functor.LaxLeftLinear.μₗ F X m)) = _
  symm
  apply IsIso.eq_inv_of_hom_inv_id
  simp only [Category.assoc, ← G.map_comp_assoc,
    Functor.LeftLinear.μₗ_comp_δₗ, G.map_id, Category.id_comp]

section InverseNaturality
variable {F} {H : M ⥤ N} [H.LeftLinear C]

/-- Invertibility of actual lineators allows module compatibility to be
checked on their actual inverse lineators. -/
theorem moduleNatural_of_inverse_lineator (τ : F ⟶ H)
    (h : ∀ (X : C) (m : M),
      τ.app (X ⊙ₗ m) ≫ Functor.OplaxLeftLinear.δₗ H X m =
        Functor.OplaxLeftLinear.δₗ F X m ≫ X ⊴ₗ τ.app m) :
    ModuleFunctor.IsModuleNatural C τ where
  lineator X m := by
    apply (cancel_mono (Functor.OplaxLeftLinear.δₗ H X m)).mp
    rw [Category.assoc, h]
    simp
end InverseNaturality

section Natural
variable {F G} {H : N ⥤ P} [H.LeftLinear C]
  (τ : G ⟶ H) [ModuleFunctor.IsModuleNatural C τ]

instance moduleNatural_whiskerLeft :
    ModuleFunctor.IsModuleNatural C (Functor.whiskerLeft F τ) where
  lineator X m := by
    change (Functor.LaxLeftLinear.μₗ G X (F.obj m) ≫ G.map (Functor.LaxLeftLinear.μₗ F X m)) ≫
      τ.app (F.obj (X ⊙ₗ m)) =
      X ⊴ₗ τ.app (F.obj m) ≫
        (Functor.LaxLeftLinear.μₗ H X (F.obj m) ≫ H.map (Functor.LaxLeftLinear.μₗ F X m))
    rw [Category.assoc, τ.naturality, ← Category.assoc, ModuleFunctor.IsModuleNatural.lineator]
    simp only [Category.assoc]
end Natural

section NaturalRight
variable {F} {H : M ⥤ N} [H.LeftLinear C]
  (τ : F ⟶ H) [ModuleFunctor.IsModuleNatural C τ]

instance moduleNatural_whiskerRight :
    ModuleFunctor.IsModuleNatural C (Functor.whiskerRight τ G) where
  lineator X m := by
    change (Functor.LaxLeftLinear.μₗ G X (F.obj m) ≫ G.map (Functor.LaxLeftLinear.μₗ F X m)) ≫
      G.map (τ.app (X ⊙ₗ m)) =
      X ⊴ₗ G.map (τ.app m) ≫
        (Functor.LaxLeftLinear.μₗ G X (H.obj m) ≫ G.map (Functor.LaxLeftLinear.μₗ H X m))
    rw [Category.assoc, ← G.map_comp, ModuleFunctor.IsModuleNatural.lineator,
      G.map_comp, ← Category.assoc, ← Functor.LaxLeftLinear.μₗ_naturality_right]
    simp only [Category.assoc]
end NaturalRight

end Paper18.Category.ModuleAlphaInduction
