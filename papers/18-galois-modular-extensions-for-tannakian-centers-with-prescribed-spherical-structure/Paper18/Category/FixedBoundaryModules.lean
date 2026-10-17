import Paper18.Category.TannakianDescent

/-!
# Actual internal-module transport through a tensor functor

The boundary comparison in Lemma A.1 identifies the image regular algebra.
The functor constructed here transports actual module actions and actual
module morphisms, before any crossed-extension classification is used.
-/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped MonObj Obj
universe v u v' u'
namespace Paper18.Category.InternalModule
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal] {A : C} [MonObj A]

/-- Tensor transport of the actual internal module action. -/
def mapModuleObj (M : Mod_ C A) : Mod_ D (F.obj A) :=
  letI : ModObj (F.obj A) (F.obj M.X) :=
    { smul := Functor.LaxMonoidal.μ F A M.X ≫ F.map γ[A,M.X]
      one_smul' := by
        change (Functor.LaxMonoidal.ε F ≫ F.map η[A]) ▷ F.obj M.X ≫
            (Functor.LaxMonoidal.μ F A M.X ≫ F.map γ[A,M.X]) = (λ_ (F.obj M.X)).hom
        simp only [comp_whiskerRight, Category.assoc]
        rw [Functor.LaxMonoidal.μ_natural_left_assoc, ← F.map_comp,
          InternalModule.one_smul]
        exact (Functor.LaxMonoidal.left_unitality F M.X).symm
      mul_smul' := by
        change (Functor.LaxMonoidal.μ F A A ≫ F.map μ[A]) ▷ F.obj M.X ≫
            (Functor.LaxMonoidal.μ F A M.X ≫ F.map γ[A,M.X]) =
          (α_ (F.obj A) (F.obj A) (F.obj M.X)).hom ≫
            (F.obj A ◁ (Functor.LaxMonoidal.μ F A M.X ≫ F.map γ[A,M.X])) ≫
              (Functor.LaxMonoidal.μ F A M.X ≫ F.map γ[A,M.X])
        simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
        rw [Functor.LaxMonoidal.μ_natural_left_assoc, ← F.map_comp,
          InternalModule.mul_smul]
        simp only [F.map_comp]
        rw [Functor.LaxMonoidal.associativity_assoc,
          ← Functor.LaxMonoidal.μ_natural_right_assoc] }
  ⟨F.obj M.X⟩

@[simp] theorem mapModuleObj_X (M : Mod_ C A) : (mapModuleObj F M).X = F.obj M.X := rfl

/-- Tensor transport preserves the actual module-intertwining equation. -/
def mapModuleHom {M N : Mod_ C A} (f : M ⟶ N) :
    mapModuleObj F M ⟶ mapModuleObj F N :=
  Mod_.Hom.mk' (F.map f.hom) (by
    change (Functor.LaxMonoidal.μ F A M.X ≫ F.map γ[A,M.X]) ≫ F.map f.hom =
      (F.obj A ◁ F.map f.hom) ≫ Functor.LaxMonoidal.μ F A N.X ≫ F.map γ[A,N.X]
    rw [Category.assoc, ← F.map_comp, f.isMod_Hom.smul_hom]
    change Functor.LaxMonoidal.μ F A M.X ≫ F.map ((A ◁ f.hom) ≫ γ[A,N.X]) = _
    rw [F.map_comp, ← Category.assoc, ← Functor.LaxMonoidal.μ_natural_right]
    exact Category.assoc _ _ _)

/-- The actual induced functor on internal module categories. -/
def mapModules : Mod_ C A ⥤ Mod_ D (F.obj A) where
  obj := mapModuleObj F
  map f := mapModuleHom F f
  map_id M := by
    apply Mod_.Hom.ext
    change F.map (𝟙 M.X) = 𝟙 (F.obj M.X)
    exact F.map_id M.X
  map_comp f g := by
    apply Mod_.Hom.ext
    change F.map (f.hom ≫ g.hom) = F.map f.hom ≫ F.map g.hom
    exact F.map_comp _ _

/-- Tensor transport has exactly the expected underlying functor. -/
theorem mapModules_comp_forget :
    mapModules F ⋙ Mod_.forget (D := D) (F.obj A) = Mod_.forget (D := C) A ⋙ F := rfl

instance mapModulesFaithful [F.Faithful] : (mapModules F (A := A)).Faithful where
  map_injective h := by
    apply Mod_.Hom.ext
    exact F.map_injective (congrArg Mod_.Hom.hom h)

/-- Full faithfulness of the tensor functor transports to actual modules;
the intertwining law is reflected after cancellation of the tensorator. -/
instance mapModulesFull [F.Full] [F.Faithful] : (mapModules F (A := A)).Full where
  map_surjective {M N} f := by
    let k := F.preimage f.hom
    have hk : F.map k = f.hom := F.map_preimage f.hom
    let g : M ⟶ N := Mod_.Hom.mk' k (by
      apply F.map_injective
      change F.map (γ[A,M.X] ≫ k) = F.map ((A ◁ k) ≫ γ[A,N.X])
      rw [F.map_comp, F.map_comp]
      apply (cancel_epi (Functor.LaxMonoidal.μ F A M.X)).mp
      rw [hk, ← Functor.LaxMonoidal.μ_natural_right_assoc, hk]
      have hf := f.isMod_Hom.smul_hom
      change (Functor.LaxMonoidal.μ F A M.X ≫ F.map γ[A,M.X]) ≫ f.hom =
        (F.obj A ◁ f.hom) ≫ (Functor.LaxMonoidal.μ F A N.X ≫ F.map γ[A,N.X]) at hf
      simpa only [Category.assoc] using hf)
    exact ⟨g, Mod_.Hom.ext hk⟩

section Additive
variable [Preadditive C] [Preadditive D] [MonoidalPreadditive C] [MonoidalPreadditive D]
  [Linear ℂ C] [Linear ℂ D] [MonoidalLinear ℂ C] [MonoidalLinear ℂ D]

instance mapModulesAdditive [F.Additive] : (mapModules F (A := A)).Additive where
  map_add := by
    intro M N f g
    apply Mod_.Hom.ext
    change F.map (f.hom + g.hom) = F.map f.hom + F.map g.hom
    exact F.map_add


instance mapModulesLinear [F.Linear ℂ] : (mapModules F (A := A)).Linear ℂ where
  map_smul f c := by
    apply Mod_.Hom.ext
    change F.map (c • f.hom) = c • F.map f.hom
    exact F.map_smul _ _

end Additive

end Paper18.Category.InternalModule
