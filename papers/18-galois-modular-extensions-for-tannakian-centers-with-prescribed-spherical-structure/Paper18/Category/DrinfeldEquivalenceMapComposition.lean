import Paper18.Category.DrinfeldEquivalenceMapNatIso

/-! # Identity and composition coherence of the actual center lift -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal CategoryTheory.Functor.Monoidal
universe v u v' u' v'' u''
namespace Paper18.Category.DrinfeldEquivalence
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  {E : Type u''} [Category.{v''} E] [MonoidalCategory E]

/-- Lift an underlying isomorphism once its actual crossing equation is proved. -/
def centralIso {A B : Center C} (e : A.1 ≅ B.1)
    (h : ∀ U, e.hom ▷ U ≫ (B.2.β U).hom = (A.2.β U).hom ≫ U ◁ e.hom) : A ≅ B := by
  let f : A ⟶ B := ⟨e.hom, h⟩
  haveI : IsIso f.f := by change IsIso e.hom; infer_instance
  exact Center.isoMk f

/-- The identity tensor equivalence induces the identity center functor. -/
def identityIso (C : Type u) [Category.{v} C] [MonoidalCategory C] :
    map (𝟭 C) ≅ 𝟭 (Center C) :=
  NatIso.ofComponents (fun Z => centralIso (A := (map (𝟭 C)).obj Z) (B := Z)
    (Iso.refl Z.1) (fun U => by
      change 𝟙 Z.1 ▷ U ≫ (Z.2.β U).hom =
        (halfIso (𝟭 C).asEquivalence Z U).hom ≫ U ◁ 𝟙 Z.1
      have h := halfIso_functor_image (𝟭 C) Z U
      simpa using h.symm))
    (fun f => by apply Center.Hom.ext; simp [centralIso])

@[simp] lemma identityIso_hom_app_f (Z : Center C) :
    ((identityIso C).hom.app Z).f = 𝟙 Z.1 := rfl

instance identityIso_monoidal : NatTrans.IsMonoidal (identityIso C).hom where
  unit := by apply Center.Hom.ext; simp [identityIso, centralIso]; rfl
  tensor Z W := by apply Center.Hom.ext; simp [identityIso, centralIso]

variable (F : C ⥤ D) [F.Monoidal] [F.IsEquivalence]
  (G : D ⥤ E) [G.Monoidal] [G.IsEquivalence]

lemma composition_comm_image (Z : Center C) (U : C) :
    (halfIso (F ⋙ G).asEquivalence Z ((F ⋙ G).obj U)).hom =
      (halfIso G.asEquivalence ((map F).obj Z) ((F ⋙ G).obj U)).hom := by
  rw [halfIso_functor_image (F ⋙ G) Z U]
  change _ = (halfIso G.asEquivalence ((map F).obj Z) (G.obj (F.obj U))).hom
  rw [halfIso_functor_image G ((map F).obj Z) (F.obj U)]
  change _ = μ G (F.obj Z.1) (F.obj U) ≫
    G.map (halfIso F.asEquivalence Z (F.obj U)).hom ≫ δ G (F.obj U) (F.obj Z.1)
  rw [halfIso_functor_image F Z U]
  simp only [Functor.LaxMonoidal.comp_μ, Functor.OplaxMonoidal.comp_δ,
    Functor.comp_map, G.map_comp, assoc]

/-- The composite lift has the same underlying composite functor; its
comparison is the identity on every underlying object. -/
def compositionIso : map F ⋙ map G ≅ map (F ⋙ G) :=
  NatIso.ofComponents (fun Z => centralIso
    (A := (map F ⋙ map G).obj Z) (B := (map (F ⋙ G)).obj Z)
    (Iso.refl (G.obj (F.obj Z.1))) (fun U => comm_of_image (F ⋙ G)
      (A := (map F ⋙ map G).obj Z) (B := (map (F ⋙ G)).obj Z)
      (𝟙 _) (fun V => by
        simpa using composition_comm_image F G Z V) U))
    (fun f => by apply Center.Hom.ext; simp [centralIso])

@[simp] lemma compositionIso_hom_app_f (Z : Center C) :
    ((compositionIso F G).hom.app Z).f = 𝟙 (G.obj (F.obj Z.1)) := rfl

instance compositionIso_monoidal : NatTrans.IsMonoidal (compositionIso F G).hom where
  unit := by
    apply Center.Hom.ext
    simp [Functor.LaxMonoidal.comp_ε, compositionIso, centralIso]
  tensor Z W := by
    apply Center.Hom.ext
    simp [Functor.LaxMonoidal.comp_μ, compositionIso, centralIso]

end Paper18.Category.DrinfeldEquivalence
