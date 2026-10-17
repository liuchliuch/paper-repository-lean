import Paper18.Category.GraphPicardNativeMonoidalBasic

/-! # Actual monoidal comparison isomorphisms for simultaneous mopping -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalOpposite
open CategoryTheory.Functor.LaxMonoidal
universe v u v' u' v'' u''
namespace Paper18.Category.GraphPicard
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  {E : Type u''} [Category.{v''} E] [MonoidalCategory E]

/-- A genuine natural isomorphism induces one between the simultaneous
monoidal opposites, retaining its actual components. -/
def simultaneousMopNatIso {F G : C ⥤ D} (e : F ≅ G) :
    simultaneousMop F ≅ simultaneousMop G :=
  NatIso.ofComponents (fun X => Iso.mop (e.app X.unmop))
    (fun {X Y} f => by
      apply Quiver.Hom.unmop_inj
      exact e.hom.naturality f.unmop)

omit [MonoidalCategory C] [MonoidalCategory D] in
@[simp] theorem simultaneousMopNatIso_hom_app_unmop {F G : C ⥤ D} (e : F ≅ G)
    (X : Cᴹᵒᵖ) :
    ((simultaneousMopNatIso e).hom.app X).unmop = e.hom.app X.unmop := rfl
omit [MonoidalCategory C] [MonoidalCategory D] in
@[simp] theorem simultaneousMopNatIso_inv_app_unmop {F G : C ⥤ D} (e : F ≅ G)
    (X : Cᴹᵒᵖ) :
    ((simultaneousMopNatIso e).inv.app X).unmop = e.inv.app X.unmop := rfl

/-- Both tensor orders reverse in the actual tensor compatibility
identity for a monoidal natural isomorphism. -/
instance simultaneousMopNatIsoMonoidal {F G : C ⥤ D} [F.Monoidal] [G.Monoidal]
    (e : F ≅ G) [NatTrans.IsMonoidal e.hom] :
    NatTrans.IsMonoidal (simultaneousMopNatIso e).hom where
  unit := by
    apply Quiver.Hom.unmop_inj
    exact NatTrans.IsMonoidal.unit (τ := e.hom)
  tensor X Y := by
    apply Quiver.Hom.unmop_inj
    exact NatTrans.IsMonoidal.tensor (τ := e.hom) Y.unmop X.unmop

/-- Simultaneous mopping preserves the actual identity functor. -/
def simultaneousMopIdIso : simultaneousMop (𝟭 C) ≅ 𝟭 Cᴹᵒᵖ :=
  NatIso.ofComponents (fun X => Iso.refl X) (fun f => by
    change f ≫ 𝟙 _ = 𝟙 _ ≫ f
    simp)

instance simultaneousMopIdIsoMonoidal :
    NatTrans.IsMonoidal (simultaneousMopIdIso (C := C)).hom where
  unit := by
    apply Quiver.Hom.unmop_inj
    change (𝟙 (𝟙_ C)) ≫ 𝟙 _ = 𝟙 _
    simp
  tensor X Y := by
    apply Quiver.Hom.unmop_inj
    change (𝟙 (Y.unmop ⊗ X.unmop)) ≫ 𝟙 _ = (𝟙 _ ⊗ₘ 𝟙 _) ≫ 𝟙 _
    simp

/-- The actual composition comparison has identity components. -/
def simultaneousMopCompIso (F : C ⥤ D) (G : D ⥤ E) :
    simultaneousMop (F ⋙ G) ≅ simultaneousMop F ⋙ simultaneousMop G :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
    change (G.map (F.map f.unmop)).mop ≫ 𝟙 _ = 𝟙 _ ≫ (G.map (F.map f.unmop)).mop
    simp)

instance simultaneousMopCompIsoMonoidal (F : C ⥤ D) (G : D ⥤ E)
    [F.Monoidal] [G.Monoidal] :
    NatTrans.IsMonoidal (simultaneousMopCompIso F G).hom where
  unit := by
    apply Quiver.Hom.unmop_inj
    change (ε G ≫ G.map (ε F)) ≫ 𝟙 _ = ε G ≫ G.map (ε F)
    simp
  tensor X Y := by
    apply Quiver.Hom.unmop_inj
    change (μ G (F.obj Y.unmop) (F.obj X.unmop) ≫ G.map (μ F Y.unmop X.unmop)) ≫ 𝟙 _ =
      (𝟙 _ ⊗ₘ 𝟙 _) ≫ μ G (F.obj Y.unmop) (F.obj X.unmop) ≫
        G.map (μ F Y.unmop X.unmop)
    simp

end Paper18.Category.GraphPicard
