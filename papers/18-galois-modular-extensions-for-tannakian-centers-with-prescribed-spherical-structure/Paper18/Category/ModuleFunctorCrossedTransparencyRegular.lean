import Paper18.Category.ModuleFunctorCrossedTransparencyTranslation
import Paper18.Category.FixedBoundaryCrossedMonodromy
import Paper18.Category.FixedBoundaryRegularMonoidal

/-! # Genuine transparency for the actual C₂ regular-algebra representative

The actual C₂ constants/sign resolution computes the regular-algebra
monodromy on every actual odd module. Both crossing identities needed by
the boundary graph are therefore derived from the actual degrees.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj Obj MonoidalLeftAction
universe v u w v' u' w'
namespace Paper18.Category.FixedBoundary
variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℂ A]
  [MonoidalCategory A] [BraidedCategory A] [MonoidalPreadditive A] [MonoidalLinear ℂ A]
  [HasKernels A] [HasFiniteBiproducts A] [RightRigidCategory A] [HasCoequalizers A]
  [∀ X Y : A, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (SA : FiniteSemisimpleSkeleton A ι)
  (F0 : FDRep ℂ RepresentationZ2.H ⥤ A) [F0.Braided] [F0.Additive] [F0.Linear ℂ]
  {N : Type u'} [Category.{v'} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N] [MonoidalPreadditive N] [MonoidalLinear ℂ N]
  [RightRigidCategory N] [HasCoequalizers N] [HasKernels N] [HasFiniteBiproducts N]
  (i : A ⥤ N) [i.Braided] [i.Full] [i.Faithful] [i.Additive] [i.Linear ℂ]
  (P : BoundaryAutoequivalence i)
variable (R : A) [MonObj R] [IsCommMonObj R]
  (qR : R ≅ regularAlgebra F0) [IsMonHom qR.hom]
  (B : TensorInverse (i.obj (F0.obj RepresentationZ2.signRep)))
  (himage : ∀ X : A, Centralizes (i.obj (F0.obj RepresentationZ2.signRep)) (i.obj X))
  (s : SeparableAlgebra R)
  (hfull : ∀ Y : N, Centralizes (i.obj (F0.obj RepresentationZ2.signRep)) Y →
    ∃ X : A, Nonempty (i.obj X ≅ Y))
  (hR : R ∈ mugerCenter (C := A))
  (e : P.functor.obj (i.obj (F0.obj RepresentationZ2.signRep)) ≅
    i.obj (F0.obj RepresentationZ2.signRep))
  [modRigid : RightRigidCategory (Mod_ N (i.obj R))] [modUnit : Simple (𝟙_ (Mod_ N (i.obj R)))]
  [modFinite : ∀ X Y : Mod_ N (i.obj R), FiniteDimensional ℂ (X ⟶ Y)]
  {κ : Type w'} [Fintype κ]
  (SD : FiniteSemisimpleSkeleton (Mod_ N (i.obj R)) κ)

local notation "chi" => neutralModuleCharacter i R B himage
local notation "Pos" => SignKernel.Positive chi
local notation "Odd" => HomogeneousCategory chi 1
local notation "G" => oddBoundaryModuleEnd SA i P R B himage s hfull e
local notation "Alpha" => ModuleAlphaInduction.negative Pos Odd

include SD hR qR modRigid modUnit modFinite in
/-- Every actual alpha representative of the actual specified-boundary
odd functor is transparent in the actual neutral braided category.
There is no regular-monodromy or crossed-coherence premise. -/
theorem regularOddBoundaryRepresentative_transparent (Z : Pos) :
    letI := neutralModuleBraided i R B himage s hfull hR
    ∀ (b : (Alpha).obj Z ≅ G) (n : Odd) [Simple n.obj], Z ∈ mugerCenter := by
  letI := neutralModuleBraided i R B himage s hfull hR
  intro b n hSimple
  let t : R ≅ R := qR ≪≫ regularTranslationIso F0 (Multiplicative.ofAdd (1 : ZMod 2)) ≪≫ qR.symm
  letI : IsMonHom t.hom := inferInstanceAs
    (IsMonHom (qR.hom ≫ (regularTranslationIso F0 (Multiplicative.ofAdd (1 : ZMod 2))).hom ≫ qR.inv))
  have hn (m : Odd) :
      (doubleBraiding (i.obj R) m.obj.X).hom = i.map t.hom ▷ m.obj.X := by
    have hm := congrArg (fun f : m.obj ⟶ m.obj => f.hom) m.property
    have hx : Homogeneous B.monodromyCharacter 1 m.obj.X := hm
    have h : (doubleBraiding (i.obj (regularAlgebra F0)) m.obj.X).hom =
        i.map (F0.map (Representation.rightTranslation (Multiplicative.ofAdd (1 : ZMod 2)))) ▷ m.obj.X :=
      regular_doubleBraiding_eq_degreeTranslation (F0 ⋙ i) B 1 m.obj.X hx
    apply (cancel_mono (i.map qR.hom ▷ m.obj.X)).mp
    rw [← doubleBraiding_naturality_left, h]
    dsimp only [t, Iso.trans_hom, Iso.symm_hom, regularTranslationIso,
      Functor.mapIso_hom, degreeTranslation]
    have hqi : i.map qR.inv ▷ m.obj.X ≫ i.map qR.hom ▷ m.obj.X = 𝟙 _ := by
      rw [← comp_whiskerRight, ← i.map_comp, qR.inv_hom_id, i.map_id, id_whiskerRight]
    simp only [Functor.map_comp, comp_whiskerRight, Category.assoc, hqi, Category.comp_id]
    rfl
  letI rr : RightRigidCategory (Mod_ N (i.obj R)) := modRigid
  letI hu : Simple (𝟙_ (Mod_ N (i.obj R))) := modUnit
  letI hf (X Y : Mod_ N (i.obj R)) : FiniteDimensional ℂ (X ⟶ Y) := modFinite X Y
  exact oddBoundaryRepresentative_mem_mugerCenter SA i P R B himage s hfull hR e SD
    t Z b n (hn n) (hn (((Alpha).obj Z).toFunctor.obj n))

end Paper18.Category.FixedBoundary
