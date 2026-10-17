import Paper18.Category.DrinfeldEquivalenceMapMonoidal

/-! # Actual center lifts of monoidal natural isomorphisms -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal CategoryTheory.Functor.Monoidal
universe v u v' u'
namespace Paper18.Category.DrinfeldEquivalence
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  {F G : C ⥤ D} [F.Monoidal] [F.IsEquivalence] [G.Monoidal] [G.IsEquivalence]
  (a : F ≅ G) [NatTrans.IsMonoidal a.hom]

lemma natIso_delta (U V : C) :
    δ F U V ≫ (a.hom.app U ⊗ₘ a.hom.app V) = a.hom.app (U ⊗ V) ≫ δ G U V := by
  apply (cancel_epi (μ F U V)).mp
  rw [← assoc, μ_δ, id_comp, NatTrans.IsMonoidal.tensor_assoc, μ_δ, comp_id]

lemma natIso_comm_image (Z : Center C) (U : C) :
    a.hom.app Z.1 ▷ F.obj U ≫ (halfIso G.asEquivalence Z (F.obj U)).hom =
      (halfIso F.asEquivalence Z (F.obj U)).hom ≫ F.obj U ◁ a.hom.app Z.1 := by
  apply (cancel_mono (a.hom.app U ▷ G.obj Z.1)).mp
  simp only [assoc]
  rw [← halfIso_functor_naturality G Z (a.hom.app U)]
  have hl : a.hom.app Z.1 ▷ F.obj U ≫ G.obj Z.1 ◁ a.hom.app U =
      a.hom.app Z.1 ⊗ₘ a.hom.app U := (tensorHom_def _ _).symm
  have hr : F.obj U ◁ a.hom.app Z.1 ≫ a.hom.app U ▷ G.obj Z.1 =
      a.hom.app U ⊗ₘ a.hom.app Z.1 := (tensorHom_def' _ _).symm
  rw [reassoc_of% hl, hr, halfIso_functor_image G Z U, halfIso_functor_image F Z U]
  simp only [assoc]
  rw [← NatTrans.IsMonoidal.tensor_assoc, natIso_delta,
    ← a.hom.naturality_assoc]

/-- Every actual monoidal natural isomorphism of tensor equivalences
lifts to an actual monoidal natural isomorphism of their center functors. -/
def mapNatIso : map F ≅ map G :=
  NatIso.ofComponents (fun Z => Center.isoMk {
    f := a.hom.app Z.1
    comm U := comm_of_image F (A := (map F).obj Z) (B := (map G).obj Z) (a.hom.app Z.1) (natIso_comm_image a Z) U })
    (fun f => by apply Center.Hom.ext; exact a.hom.naturality f.f)

@[simp] lemma mapNatIso_hom_app_f (Z : Center C) :
    ((mapNatIso a).hom.app Z).f = a.hom.app Z.1 := rfl

instance mapNatIso_monoidal : NatTrans.IsMonoidal (mapNatIso a).hom where
  unit := by apply Center.Hom.ext; exact NatTrans.IsMonoidal.unit (τ := a.hom)
  tensor Z W := by apply Center.Hom.ext; exact NatTrans.IsMonoidal.tensor (τ := a.hom) Z.1 W.1

instance reflIso_monoidal : NatTrans.IsMonoidal (Iso.refl F).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (𝟙 F))

instance transIso_monoidal {H : C ⥤ D} [H.Monoidal] [H.IsEquivalence]
    (b : G ≅ H) [NatTrans.IsMonoidal b.hom] : NatTrans.IsMonoidal (a ≪≫ b).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (a.hom ≫ b.hom))

lemma mapNatIso_refl : mapNatIso (Iso.refl F) = Iso.refl (map F) := by
  apply Iso.ext
  ext Z
  rfl

lemma mapNatIso_trans {H : C ⥤ D} [H.Monoidal] [H.IsEquivalence]
    (b : G ≅ H) [NatTrans.IsMonoidal b.hom] :
    mapNatIso (a ≪≫ b) = mapNatIso a ≪≫ mapNatIso b := by
  apply Iso.ext
  ext Z
  rfl

end Paper18.Category.DrinfeldEquivalence
