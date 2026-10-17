import Paper18.Category.FixedBoundaryCrossedFunctor
import Paper18.Category.ModuleFunctorFiniteContraction

/-! # Genuine crossed maps force equivariance of the monoidal comparison

Crossed preservation, naturality and the actual monoidal comparison give
the translation comparison after tensoring with a genuine odd simple.
The crossed quotient is epimorphic. Normalized rigid contraction removes
the remaining simple tensor factor, so no scalar action-defect premise is
needed.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj Obj
universe v u v' u' w
namespace Paper18.Category
open RelativeTensor FixedBoundary
variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℂ A]
  [MonoidalCategory A] [BraidedCategory A]
  {N : Type u'} [Category.{v'} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N]
  [RightRigidCategory N] [HasCoequalizers N]
  {i : A ⥤ N} [i.Braided] (P : BoundaryAutoequivalence i) (R : A)
  [MonObj R] [IsCommMonObj R] (t : R ≅ R) [IsMonHom t.hom]
  [Preadditive (Mod_ N (i.obj R))] [Linear ℂ (Mod_ N (i.obj R))]
  [MonoidalPreadditive (Mod_ N (i.obj R))] [MonoidalLinear ℂ (Mod_ N (i.obj R))]
  [HasKernels (Mod_ N (i.obj R))] [HasFiniteBiproducts (Mod_ N (i.obj R))]
  [RightRigidCategory (Mod_ N (i.obj R))] [Simple (𝟙_ (Mod_ N (i.obj R)))]
  [∀ X Y : Mod_ N (i.obj R), FiniteDimensional ℂ (X ⟶ Y)]
  {κ : Type w} [Fintype κ] (SD : FiniteSemisimpleSkeleton (Mod_ N (i.obj R)) κ)
  (β : P.moduleFunctor R ≅ 𝟭 (Mod_ N (i.obj R))) [NatTrans.IsMonoidal β.hom]

local instance actionComparison_imageAlgebraTranslation : IsMonHom (i.mapIso t).hom := by
  change IsMonHom (i.map t.hom)
  infer_instance

include SD in
/-- Every actual monoidal comparison commutes with the actual translation
if one genuine simple has the corresponding crossed degree. -/
theorem BoundaryAutoequivalence.moduleComparison_comap_of_crossed
    (n : Mod_ N (i.obj R)) [Simple n]
    (hn : (doubleBraiding (i.obj R) n.X).hom = i.map t.hom ▷ n.X)
    (M : Mod_ N (i.obj R)) :
    (P.moduleComapComparison R t.hom).hom.app M ≫
        (Mod_.comap (i.map t.hom)).map (β.hom.app M) =
      β.hom.app ((Mod_.comap (i.map t.hom)).obj M) := by
  let F : Mod_ N (i.obj R) ⥤ Mod_ N (i.obj R) := P.moduleFunctor R
  let T : Mod_ N (i.obj R) ⥤ Mod_ N (i.obj R) := Mod_.comap (i.map t.hom)
  let k := P.moduleComapComparison R t.hom
  let c := translatedBraidingHom (i.mapIso t) M n hn
  let hFn := P.moduleFunctor_translated_monodromy R t n hn
  let cF := translatedBraidingHom (i.mapIso t) (F.obj M) (F.obj n) hFn
  have hp := P.moduleFunctor_translatedBraiding R t M n hn
  change Functor.LaxMonoidal.μ F M n ≫ F.map c =
    cF ≫ (F.obj n ◁ k.inv.app M) ≫ Functor.LaxMonoidal.μ F n (T.obj M) at hp
  have hβ := β.hom.naturality c
  change F.map c ≫ β.hom.app (n ⊗ T.obj M) = β.hom.app (M ⊗ n) ≫ c at hβ
  have hcross : cF ≫ (F.obj n ◁ T.map (β.hom.app M)) ≫ (β.hom.app n ▷ T.obj M) =
      (β.hom.app M ⊗ₘ β.hom.app n) ≫ c := by
    rw [MonoidalCategory.tensorHom_def]
    have hright := translatedBraiding_naturality_right (i.mapIso t) M
      (β.hom.app n) hFn hn
    have hleft := translatedBraiding_naturality_left (i.mapIso t) (β.hom.app M) (F.obj n) hFn
    change (M ◁ β.hom.app n) ≫ c =
      translatedBraidingHom (i.mapIso t) M (F.obj n) hFn ≫ (β.hom.app n ▷ T.obj M) at hright
    change (β.hom.app M ▷ F.obj n) ≫ translatedBraidingHom (i.mapIso t) M (F.obj n) hFn =
      cF ≫ (F.obj n ◁ T.map (β.hom.app M)) at hleft
    simp only [Functor.id_obj]
    erw [Category.assoc, hright, ← Category.assoc]
    simpa only [Category.assoc] using
      (congrArg (fun k => k ≫ (β.hom.app n ▷ T.obj M)) hleft).symm

  have h := congrArg (fun f => f ≫ β.hom.app (n ⊗ T.obj M)) hp
  simp only [Category.assoc] at h
  rw [hβ, ← Category.assoc (Functor.LaxMonoidal.μ F M n),
    NatTrans.IsMonoidal.tensor] at h
  rw [NatTrans.IsMonoidal.tensor] at h
  change (((β.hom.app M ⊗ₘ β.hom.app n) ≫ 𝟙 _) ≫ c) =
    cF ≫ (F.obj n ◁ k.inv.app M) ≫ (β.hom.app n ⊗ₘ β.hom.app (T.obj M)) ≫ 𝟙 _ at h
  simp only [Category.comp_id] at h
  change (β.hom.app M ⊗ₘ β.hom.app n) ≫ c =
    cF ≫ (F.obj n ◁ k.inv.app M) ≫ (β.hom.app n ⊗ₘ β.hom.app (T.obj M)) at h
  rw [← hcross, MonoidalCategory.tensorHom_def'] at h
  have h' := (cancel_epi cF).mp h
  have h'' : (F.obj n ◁ T.map (β.hom.app M)) =
      (F.obj n ◁ k.inv.app M) ≫ (F.obj n ◁ β.hom.app (T.obj M)) := by
    apply (cancel_mono (β.hom.app n ▷ T.obj M)).mp
    simpa only [Category.assoc, Functor.id_obj] using h' 
  haveI : Simple ((𝟭 (Mod_ N (i.obj R))).obj n) := ‹Simple n›
  haveI : Simple (F.obj n) := Simple.of_iso (β.app n)
  have he : T.map (β.hom.app M) = k.inv.app M ≫ β.hom.app (T.obj M) := by
    have hh := congrArg (ModuleFunctor.simpleLeftContraction SD (F.obj n)) h''
    simpa only [← whiskerLeft_comp, ModuleFunctor.simpleLeftContraction_whiskerLeft] using hh
  change k.hom.app M ≫ T.map (β.hom.app M) = β.hom.app (T.obj M)
  rw [he, ← Category.assoc, k.hom_inv_id_app, Category.id_comp]

end Paper18.Category
