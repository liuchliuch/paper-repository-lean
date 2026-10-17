import Paper18.Category.EquivariantAveraging
import Paper18.Category.SemisimpleSplitting

/-!
# Universal induction and coinduction morphisms

Induction is both a left and a right adjoint on Hom spaces for a finite
weak action. The universal morphisms below show directly that the actual
forgetful functor sends categorical monomorphisms and epimorphisms to
underlying monomorphisms and epimorphisms. Combined with averaging, every
mono and epi in an equivariantization of a finite semisimple category splits.
-/

noncomputable section
open Classical CategoryTheory CategoryTheory.Limits
open scoped BigOperators
universe v u w t
namespace Paper18.Category.WeakAction
variable {G : Type w} [Group G] [Fintype G] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear ℂ C] [HasFiniteBiproducts C]
  (A : WeakAction G C) [∀ g : G, (A.ρ g).Additive] [∀ g : G, (A.ρ g).Linear ℂ]

attribute [local instance] Paper18.Category.additive_preservesBiproductsOfFiniteShape

/-- Extension of an arbitrary underlying map to an equivariant map from
induction, using the actual structure maps on its target. -/
def inductionHom {Z : C} {X : A.Equivariant} (f : Z ⟶ X.obj) : A.induction Z ⟶ X where
  hom := biproduct.desc fun g : G => (A.ρ g).map f ≫ (X.structureIso g).hom
  comm g := by
    apply Paper18.Category.map_biproduct_hom_ext (A.ρ g) (fun h : G => (A.ρ h).obj Z)
    intro h
    rw [← Functor.map_comp_assoc, biproduct.ι_desc, Functor.map_comp,
      Category.assoc, X.mul]
    conv_rhs =>
      erw [← Category.assoc, A.map_ι_inductionIso, Category.assoc, biproduct.ι_desc]
    erw [(A.mulIso g h).hom.naturality_assoc f]

omit [Linear ℂ C] [∀ g : G, (A.ρ g).Linear ℂ] in
/-- Restricting induction extension to the identity summand recovers the
original underlying map. -/
@[simp]
theorem inductionHom_inclusion {Z : C} {X : A.Equivariant} (f : Z ⟶ X.obj) :
    (A.inductionRetract Z).i ≫ (A.inductionHom f).hom = f := by
  dsimp only [inductionRetract, inductionHom]
  rw [Category.assoc, biproduct.ι_desc, X.unit]
  erw [A.unitIso.hom.naturality f]
  simp

omit [Linear ℂ C] [∀ g : G, (A.ρ g).Linear ℂ] in
/-- The induction extension commutes with actual equivariant maps. -/
theorem inductionHom_comp {Z : C} {X Y : A.Equivariant}
    (f : Z ⟶ X.obj) (h : X ⟶ Y) :
    A.inductionHom f ≫ h = A.inductionHom (f ≫ h.hom) := by
  apply Equivariant.Hom.ext
  apply biproduct.hom_ext'
  intro g
  dsimp only [inductionHom, Equivariant.comp_hom]
  rw [biproduct.ι_desc_assoc, biproduct.ι_desc, Functor.map_comp]
  simp only [Category.assoc]
  rw [h.comm]

omit [Linear ℂ C] [∀ g : G, (A.ρ g).Linear ℂ] in
/-- The structure map on induction in projection form. -/
@[reassoc]
theorem inductionIso_π (Z : C) (g h : G) :
    (A.inductionIso Z g).hom ≫ biproduct.π (fun k : G => (A.ρ k).obj Z) (g * h) =
      (A.ρ g).map (biproduct.π (fun k : G => (A.ρ k).obj Z) h) ≫
        (A.mulIso g h).hom.app Z := by
  apply Paper18.Category.map_biproduct_hom_ext (A.ρ g) (fun k : G => (A.ρ k).obj Z)
  intro k
  rw [A.map_ι_inductionIso_assoc, ← Functor.map_comp_assoc]
  by_cases hk : k = h
  · subst k
    simp
  · rw [biproduct.ι_π_ne _ hk]
    have hg : g * k ≠ g * h := fun he => hk (mul_left_cancel he)
    rw [biproduct.ι_π_ne _ hg]
    simp

/-- Coextension of an arbitrary underlying map to a map into induction,
which is also the finite coinduction object. -/
def coinductionHom {X : A.Equivariant} {Z : C} (f : X.obj ⟶ Z) : X ⟶ A.induction Z where
  hom := biproduct.lift fun g : G => (X.structureIso g).inv ≫ (A.ρ g).map f
  comm g := by
    apply biproduct.hom_ext
    intro k
    obtain ⟨h, rfl⟩ := (Group.mulLeft_bijective g).surjective k
    dsimp only [induction]
    simp only [Category.assoc]
    rw [A.inductionIso_π, ← Functor.map_comp_assoc, biproduct.lift_π,
      Functor.map_comp, Category.assoc]
    erw [(A.mulIso g h).hom.naturality f]
    have hm := (X.structureIso g).hom ≫=
      Equivariant.structureIso_inv_mul A X g h =≫ (A.mulIso g h).hom.app X.obj
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_app,
      Category.comp_id] at hm
    rw [← Category.assoc, hm]
    simp

omit [Linear ℂ C] [∀ g : G, (A.ρ g).Linear ℂ] in
/-- Restricting coextension to the identity projection recovers its
underlying map. -/
@[simp]
theorem coinductionHom_projection {X : A.Equivariant} {Z : C} (f : X.obj ⟶ Z) :
    (A.coinductionHom f).hom ≫ (A.inductionRetract Z).r = f := by
  change biproduct.lift (fun g : G => (X.structureIso g).inv ≫ (A.ρ g).map f) ≫
    biproduct.π (fun g : G => (A.ρ g).obj Z) 1 ≫ (A.unitIso.app Z).hom = f
  rw [biproduct.lift_π_assoc]
  have hu : (X.structureIso 1).inv = (A.unitIso.app X.obj).inv := by
    exact congrArg Iso.inv (Iso.ext X.unit : X.structureIso 1 = A.unitIso.app X.obj)
  rw [hu, Category.assoc]
  erw [A.unitIso.hom.naturality f]
  simp

omit [Linear ℂ C] [∀ g : G, (A.ρ g).Linear ℂ] in
/-- Coextension commutes with actual equivariant maps. -/
theorem comp_coinductionHom {X Y : A.Equivariant} {Z : C}
    (f : X ⟶ Y) (h : Y.obj ⟶ Z) :
    f ≫ A.coinductionHom h = A.coinductionHom (f.hom ≫ h) := by
  apply Equivariant.Hom.ext
  apply biproduct.hom_ext
  intro g
  dsimp only [coinductionHom, Equivariant.comp_hom]
  rw [Category.assoc, biproduct.lift_π, biproduct.lift_π, Functor.map_comp]
  have hf : f.hom ≫ (Y.structureIso g).inv =
      (X.structureIso g).inv ≫ (A.ρ g).map f.hom := by
    apply (cancel_mono (Y.structureIso g).hom).mp
    simp [Category.assoc, f.comm]
  rw [← Category.assoc, hf, Category.assoc]

/-- A monomorphism of actual equivariant objects is an underlying
monomorphism, proved using universal induction maps. -/
instance underlying_mono {X Y : A.Equivariant} (f : X ⟶ Y) [Mono f] : Mono f.hom :=
  ⟨fun {Z} a b hab => by
    have he : A.inductionHom a ≫ f = A.inductionHom b ≫ f := by
      rw [A.inductionHom_comp, A.inductionHom_comp, hab]
    have hc := (cancel_mono f).mp he
    have hh := congrArg (fun k => (A.inductionRetract Z).i ≫ k.hom) hc
    simpa only [A.inductionHom_inclusion] using hh⟩

/-- An epimorphism of actual equivariant objects is an underlying
epimorphism, proved using universal coinduction maps. -/
instance underlying_epi {X Y : A.Equivariant} (f : X ⟶ Y) [Epi f] : Epi f.hom :=
  ⟨fun {Z} a b hab => by
    have he : f ≫ A.coinductionHom a = f ≫ A.coinductionHom b := by
      rw [A.comp_coinductionHom, A.comp_coinductionHom, hab]
    have hc := (cancel_epi f).mp he
    have hh := congrArg (fun k => k.hom ≫ (A.inductionRetract Z).r) hc
    simpa only [A.coinductionHom_projection] using hh⟩

section Semisimple
variable [HasKernels C] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type t} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- Every equivariant monomorphism splits, by actual underlying
semisimplicity followed by characteristic-zero averaging. -/
def equivariantSplitMono {X Y : A.Equivariant} (f : X ⟶ Y) [Mono f] : SplitMono f :=
  Equivariant.splitMonoOfUnderlyingRetraction A f (S.splitMono f.hom).retraction
    (S.splitMono f.hom).id

/-- Every equivariant epimorphism splits by the dual construction. -/
def equivariantSplitEpi {X Y : A.Equivariant} (f : X ⟶ Y) [Epi f] : SplitEpi f :=
  Equivariant.splitEpiOfUnderlyingSection A f (S.splitEpi f.hom).section_
    (S.splitEpi f.hom).id

end Semisimple
end Paper18.Category.WeakAction
