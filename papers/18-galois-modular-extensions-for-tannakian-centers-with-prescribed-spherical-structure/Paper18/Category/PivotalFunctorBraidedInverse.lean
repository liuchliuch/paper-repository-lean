import Paper18.Category.DrinfeldPivotalBraided

/-! # Pivotal preservation by actual braided inverse functors -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u v' u'
namespace Paper18.Category.PreservesPivotal
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  [RightRigidCategory D] [BraidedCategory D]
  {F : C ⥤ D} [F.Braided] {G : D ⥤ C} [G.Braided]
  {J : PivotalStructure C} {K : PivotalStructure D}

/-- A natural isomorphism between actual braided tensor functors transports
pivotal preservation, because its naturality transports actual twists. -/
theorem of_braided_iso {H : C ⥤ D} [H.Braided] (e : F ≅ H)
    (h : PreservesPivotal F J K) : PreservesPivotal H J K := by
  apply preservesPivotal_of_twist
  intro X
  apply (cancel_epi (e.hom.app X)).mp
  calc
    _ = F.map (J.twistIso X).hom ≫ e.hom.app X :=
      (e.hom.naturality (J.twistIso X).hom).symm
    _ = (K.twistIso (F.obj X)).hom ≫ e.hom.app X := by rw [h.twist]
    _ = _ := (K.twist_naturality (e.hom.app X)).symm

/-- A braided inverse to a faithful braided pivotal tensor functor is
pivotal through its own canonical double-dual comparison. -/
theorem braided_inverse [F.Faithful] (e : G ⋙ F ≅ 𝟭 D)
    (h : PreservesPivotal F J K) : PreservesPivotal G K J := by
  apply preservesPivotal_of_twist
  intro Y
  apply F.map_injective
  apply (cancel_mono (e.hom.app Y)).mp
  rw [h.twist]
  have hn := e.hom.naturality (K.twistIso Y).hom
  change F.map (G.map (K.twistIso Y).hom) ≫ e.hom.app Y =
    e.hom.app Y ≫ (K.twistIso Y).hom at hn
  exact hn.trans (K.twist_naturality (e.hom.app Y))

end Paper18.Category.PreservesPivotal
