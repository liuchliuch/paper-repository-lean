import Paper18.Category.FixedBoundaryModules

/-! # Actual algebra isomorphisms induce module-category equivalences -/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped MonObj
universe v u
namespace Paper18.Category.InternalModule
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {A B : C} [MonObj A] [MonObj B]

instance comapFaithful (f : A ⟶ B) [IsMonHom f] : (Mod_.comap (D := C) f).Faithful where
  map_injective {M N} {g h} hh := by
    have he := congrArg (fun k : (Mod_.comap (D := C) f).obj M ⟶
      (Mod_.comap (D := C) f).obj N => k.hom) hh
    exact Mod_.Hom.ext he

/-- Restriction along an algebra isomorphism reflects the actual module
intertwining equation by cancellation of the algebra isomorphism. -/
instance comapFullOfIso (f : A ⟶ B) [IsMonHom f] [IsIso f] :
    (Mod_.comap (D := C) f).Full where
  map_surjective {M N} g := by
    let h : M ⟶ N := Mod_.Hom.mk' g.hom (by
      change γ[B,M.X] ≫ g.hom = (B ◁ g.hom) ≫ γ[B,N.X]
      apply (cancel_epi (f ▷ M.X)).mp
      rw [← whisker_exchange_assoc]
      have hg := g.isMod_Hom.smul_hom
      change ((f ▷ M.X) ≫ γ[B,M.X]) ≫ g.hom =
        (A ◁ g.hom) ≫ (f ▷ N.X) ≫ γ[B,N.X] at hg
      simpa only [Category.assoc] using hg)
    exact ⟨h, Mod_.Hom.ext rfl⟩

/-- Restricting along an algebra isomorphism and its inverse gives an
actual module isomorphism, with identity underlying morphism. -/
def comapCancelIso (e : A ≅ B) [IsMonHom e.hom] (M : Mod_ C A) :
    (Mod_.comap e.hom).obj ((Mod_.comap e.inv).obj M) ≅ M := by
  let f : (Mod_.comap e.hom).obj ((Mod_.comap e.inv).obj M) ⟶ M :=
    Mod_.Hom.mk' (𝟙 M.X) (by
      change ((e.hom ▷ M.X) ≫ (e.inv ▷ M.X) ≫ γ[A,M.X]) ≫ 𝟙 M.X =
        (A ◁ 𝟙 M.X) ≫ γ[A,M.X]
      simp only [Category.comp_id, ← comp_whiskerRight_assoc, e.hom_inv_id,
        id_whiskerRight, Category.id_comp, MonoidalCategory.whiskerLeft_id])
  letI : IsIso f.hom := inferInstanceAs (IsIso (𝟙 M.X))
  letI := internalModule_isIso_of_underlying f
  exact asIso f

/-- Actual essential surjectivity of algebra-isomorphism restriction. -/
theorem comapEssSurj (e : A ≅ B) [IsMonHom e.hom] :
    (Mod_.comap (D := C) e.hom).EssSurj where
  mem_essImage M := ⟨(Mod_.comap e.inv).obj M, ⟨comapCancelIso e M⟩⟩

/-- The actual categorical equivalence induced by an algebra isomorphism. -/
def algebraRestrictionEquivalence (e : A ≅ B) [IsMonHom e.hom] : Mod_ C B ≌ Mod_ C A := by
  letI := comapEssSurj e
  letI : (Mod_.comap (D := C) e.hom).IsEquivalence := {}
  exact (Mod_.comap e.hom).asEquivalence

end Paper18.Category.InternalModule
