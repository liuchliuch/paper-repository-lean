import Paper18.Category.WeakActionQuotientStandardTransport

/-! # Transporting genuine weak actions through a family of natural isomorphisms

The original pentagon and triangle laws imply the transported laws.
Only the actual unit and multiplication normalization squares are inputs.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category
universe v u w
namespace Paper18.Category.WeakAction
variable {Γ : Type w} [Group Γ] {C : Type u} [Category.{v} C]

@[reassoc] lemma isoFamily_eqToHom (F H : Γ → C ⥤ C) (σ : ∀ g, F g ≅ H g)
    {x y : Γ} (h : x=y) (X : C) :
    eqToHom (congrArg (fun t => (F t).obj X) h) ≫ (σ y).hom.app X =
      (σ x).hom.app X ≫ eqToHom (congrArg (fun t => (H t).obj X) h) := by
  subst y
  simp

section Coherence
variable (A : WeakAction Γ C) (F : Γ → C ⥤ C)
  (σ : ∀ g, A.ρ g ≅ F g) (ν : ∀ g h, F h ⋙ F g ≅ F (g*h))
  (hm : ∀ g h X, (A.mulIso g h).hom.app X ≫ (σ (g*h)).hom.app X =
    (A.ρ g).map ((σ h).hom.app X) ≫ (σ g).hom.app ((F h).obj X) ≫ (ν g h).hom.app X)

include A σ hm in
lemma isoTransport_assoc (g h k : Γ) (X : C) :
    (F g).map ((ν h k).hom.app X) ≫ (ν g (h*k)).hom.app X =
      (ν g h).hom.app ((F k).obj X) ≫ (ν (g*h) k).hom.app X ≫
        eqToHom (congrArg (fun t => (F t).obj X) (_root_.mul_assoc g h k)) := by
  let u := (A.ρ g).map ((A.ρ h).map ((σ k).hom.app X)) ≫
    (A.ρ g).map ((σ h).hom.app ((F k).obj X)) ≫
      (σ g).hom.app ((F h).obj ((F k).obj X))
  haveI : IsIso u := by dsimp [u]; infer_instance
  apply (cancel_epi u).mp
  have hl : u ≫ (F g).map ((ν h k).hom.app X) ≫ (ν g (h*k)).hom.app X =
      (A.ρ g).map ((A.mulIso h k).hom.app X) ≫
        (A.mulIso g (h*k)).hom.app X ≫ (σ (g*(h*k))).hom.app X := by
    dsimp only [u]
    simp only [Category.assoc]
    rw [← reassoc_of% (σ g).hom.naturality ((ν h k).hom.app X)]
    rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
    simp only [Category.assoc]
    rw [← hm h k X, Functor.map_comp]
    simp only [Category.assoc]
    rw [← hm g (h*k) X]
  have hr : u ≫ (ν g h).hom.app ((F k).obj X) ≫ (ν (g*h) k).hom.app X ≫
        eqToHom (congrArg (fun t => (F t).obj X) (_root_.mul_assoc g h k)) =
      (A.mulIso g h).hom.app ((A.ρ k).obj X) ≫ (A.mulIso (g*h) k).hom.app X ≫
        (σ ((g*h)*k)).hom.app X ≫
          eqToHom (congrArg (fun t => (F t).obj X) (_root_.mul_assoc g h k)) := by
    dsimp only [u]
    simp only [Category.assoc]
    rw [← reassoc_of% (hm g h ((F k).obj X))]
    have hn := (A.mulIso g h).hom.naturality ((σ k).hom.app X)
    dsimp only [Functor.comp_map] at hn
    rw [reassoc_of% hn]
    rw [← reassoc_of% (hm (g*h) k X)]
  simp only [Category.assoc]
  rw [hl, hr, reassoc_of% (A.assoc g h k X)]
  simp only [Category.assoc]
  rw [isoFamily_eqToHom A.ρ F σ (_root_.mul_assoc g h k) X]

variable (e : F 1 ≅ 𝟭 C)
  (hu : ∀ X, (σ 1).hom.app X ≫ e.hom.app X = A.unitIso.hom.app X)

include A σ hm hu in
lemma isoTransport_one_mul (g : Γ) (X : C) :
    (ν 1 g).hom.app X ≫ eqToHom (congrArg (fun t => (F t).obj X) (_root_.one_mul g)) =
      e.hom.app ((F g).obj X) := by
  apply (cancel_epi ((A.ρ 1).map ((σ g).hom.app X) ≫
    (σ 1).hom.app ((F g).obj X))).mp
  simp only [Category.assoc]
  rw [← reassoc_of% (hm 1 g X), hu]
  rw [← isoFamily_eqToHom A.ρ F σ (_root_.one_mul g) X, reassoc_of% (A.one_mul g X)]
  exact (A.unitIso.hom.naturality ((σ g).hom.app X)).symm

include A σ hm hu in
lemma isoTransport_mul_one (g : Γ) (X : C) :
    (ν g 1).hom.app X ≫ eqToHom (congrArg (fun t => (F t).obj X) (_root_.mul_one g)) =
      (F g).map (e.hom.app X) := by
  apply (cancel_epi ((A.ρ g).map ((σ 1).hom.app X) ≫
    (σ g).hom.app ((F 1).obj X))).mp
  simp only [Category.assoc]
  rw [← reassoc_of% (hm g 1 X),
    ← isoFamily_eqToHom A.ρ F σ (_root_.mul_one g) X, reassoc_of% (A.mul_one g X)]
  rw [← (σ g).hom.naturality (e.hom.app X)]
  rw [← Functor.map_comp_assoc, hu]
  rfl

end Coherence

/-- Actual normalization squares transport all weak-action coherences.
No transported associativity or triangle law is supplied as an input. -/
def ofIsoFamily (A : WeakAction Γ C) (F : Γ → C ⥤ C)
    (σ : ∀ g, A.ρ g ≅ F g) (e : F 1 ≅ 𝟭 C)
    (ν : ∀ g h, F h ⋙ F g ≅ F (g*h))
    (hu : ∀ X, (σ 1).hom.app X ≫ e.hom.app X = A.unitIso.hom.app X)
    (hm : ∀ g h X, (A.mulIso g h).hom.app X ≫ (σ (g*h)).hom.app X =
      (A.ρ g).map ((σ h).hom.app X) ≫ (σ g).hom.app ((F h).obj X) ≫ (ν g h).hom.app X) :
    WeakAction Γ C where
  ρ := F
  unitIso := e
  mulIso := ν
  assoc := isoTransport_assoc A F σ ν hm
  one_mul := isoTransport_one_mul A F σ ν hm e hu
  mul_one := isoTransport_mul_one A F σ ν hm e hu

/-- The actual normalization is an actual weak-action isomorphism. -/
def ofIsoFamilyActionIso (A : WeakAction Γ C) (F : Γ → C ⥤ C)
    (σ : ∀ g, A.ρ g ≅ F g) (e : F 1 ≅ 𝟭 C)
    (ν : ∀ g h, F h ⋙ F g ≅ F (g*h))
    (hu : ∀ X, (σ 1).hom.app X ≫ e.hom.app X = A.unitIso.hom.app X)
    (hm : ∀ g h X, (A.mulIso g h).hom.app X ≫ (σ (g*h)).hom.app X =
      (A.ρ g).map ((σ h).hom.app X) ≫ (σ g).hom.app ((F h).obj X) ≫ (ν g h).hom.app X) :
    ActionIso A (ofIsoFamily A F σ e ν hu hm) where
  iso := σ
  unit := hu
  mul := hm

section MultiplicationOnly
variable (A : WeakAction Γ C) (F : Γ → C ⥤ C)
  (σ : ∀ g, A.ρ g ≅ F g) (ν : ∀ g h, F h ⋙ F g ≅ F (g*h))
  (hm : ∀ g h X, (A.mulIso g h).hom.app X ≫ (σ (g*h)).hom.app X =
    (A.ρ g).map ((σ h).hom.app X) ≫ (σ g).hom.app ((F h).obj X) ≫ (ν g h).hom.app X)

/-- The actual unit normalization is constructed from the original unit. -/
def isoFamilyUnit : F 1 ≅ 𝟭 C := (σ 1).symm ≪≫ A.unitIso

lemma isoFamilyUnit_comp (X : C) :
    (σ 1).hom.app X ≫ (isoFamilyUnit A F σ).hom.app X = A.unitIso.hom.app X := by
  dsimp only [isoFamilyUnit, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  simp only [Iso.hom_inv_id_app_assoc]

/-- Actual multiplication normalization alone constructs the transported
weak action, with its unit normalization derived canonically. -/
def ofIsoFamilyMul : WeakAction Γ C :=
  ofIsoFamily A F σ (isoFamilyUnit A F σ) ν (isoFamilyUnit_comp A F σ) hm

/-- The actual normalization family is a coherent isomorphism of weak actions. -/
def ofIsoFamilyMulActionIso : ActionIso A (ofIsoFamilyMul A F σ ν hm) :=
  ofIsoFamilyActionIso A F σ (isoFamilyUnit A F σ) ν (isoFamilyUnit_comp A F σ) hm

section Monoidal
variable [MonoidalCategory C] [∀ g : Γ, (A.ρ g).Monoidal] [A.IsMonoidal]
  [∀ g : Γ, (F g).Monoidal]
  [∀ g : Γ, NatTrans.IsMonoidal (σ g).hom]
  [∀ g h : Γ, NatTrans.IsMonoidal (ν g h).hom]

instance ofIsoFamilyMul_rho_monoidal (g : Γ) :
    ((ofIsoFamilyMul A F σ ν hm).ρ g).Monoidal :=
  inferInstanceAs (F g).Monoidal

instance ofIsoFamilyMul_monoidal : (ofIsoFamilyMul A F σ ν hm).IsMonoidal where
  unit_monoidal := by
    change NatTrans.IsMonoidal ((σ 1).symm ≪≫ A.unitIso).hom
    dsimp only [Iso.trans_hom, Iso.symm_hom]
    infer_instance
  mul_monoidal g h := inferInstanceAs (NatTrans.IsMonoidal (ν g h).hom)

instance ofIsoFamilyMulActionIso_monoidal :
    (ofIsoFamilyMulActionIso A F σ ν hm).IsMonoidal where
  iso_monoidal g := inferInstanceAs (NatTrans.IsMonoidal (σ g).hom)
end Monoidal

section Linear
variable [Preadditive C] [Linear ℂ C]
  [∀ g : Γ, (F g).Additive] [∀ g : Γ, (F g).Linear ℂ]

instance ofIsoFamilyMul_rho_additive (g : Γ) :
    ((ofIsoFamilyMul A F σ ν hm).ρ g).Additive := inferInstanceAs (F g).Additive

instance ofIsoFamilyMul_rho_linear (g : Γ) :
    ((ofIsoFamilyMul A F σ ν hm).ρ g).Linear ℂ :=
  inferInstanceAs (Functor.Linear ℂ (F g))
end Linear
end MultiplicationOnly

end Paper18.Category.WeakAction
