import Paper18.Category.ModuleFunctorCrossedTransparency
import Paper18.Category.FixedBoundaryOddRepresentation
import Paper18.Category.FixedBoundaryCrossedNeutralComparison
import Paper18.Category.FixedBoundaryCrossedHexagon
import Paper18.Category.FixedBoundaryNeutralBraidedEquivalence
import Paper18.Category.FixedBoundaryLocalCrossing

/-! # The actual boundary representative and the genuine crossed maps

The only crossing hypotheses below are actual regular-algebra monodromy
identities on the two specified objects. The actual descended crossing,
its naturality, its tensor identity, and the two boundary-preservation
squares are constructed and proved in the imported modules.
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
  {N : Type u'} [Category.{v'} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N] [MonoidalPreadditive N] [MonoidalLinear ℂ N]
  [RightRigidCategory N] [HasCoequalizers N] [HasKernels N] [HasFiniteBiproducts N]
  (i : A ⥤ N) [i.Braided] [i.Full] [i.Faithful] [i.Additive] [i.Linear ℂ]
  (P : BoundaryAutoequivalence i) (R : A) [MonObj R] [IsCommMonObj R]
  {T : N} (B : TensorInverse T)
  (himage : ∀ X : A, Centralizes T (i.obj X))
  (s : SeparableAlgebra R)
  (hfull : ∀ Y : N, Centralizes T Y → ∃ X : A, Nonempty (i.obj X ≅ Y))
  (hR : R ∈ mugerCenter (C := A)) (e : P.functor.obj T ≅ T)

local notation "chi" => neutralModuleCharacter i R B himage
local notation "Pos" => SignKernel.Positive chi
local notation "Odd" => HomogeneousCategory chi 1
local notation "G" => oddBoundaryModuleEnd SA i P R B himage s hfull e
local notation "a" => neutralComparisonUnderlying i P R B himage s hfull e
local notation "F" => P.moduleFunctor R
local notation "Alpha" => ModuleAlphaInduction.negative Pos Odd
local notation "L" => neutralCenterFunctor i R B himage s hfull hR

/-- The actual right lineator obtained from the specified neutral
comparison and the genuine relative-tensor functor tensorator. -/
def oddBoundaryRightLineator (V : Pos) (n : Odd) :
    (homogeneousRightTensor chi 1 V).obj ((G).toFunctor.obj n) ≅
      (G).toFunctor.obj ((homogeneousRightTensor chi 1 V).obj n) :=
  ObjectProperty.isoMk _
    (whiskerLeftIso ((F).obj n.obj) ((a).app V).symm ≪≫
      Functor.Monoidal.μIso F n.obj V.obj)

@[simp] lemma oddBoundaryRightLineator_hom (V : Pos) (n : Odd) :
    (oddBoundaryRightLineator SA i P R B himage s hfull e V n).hom =
      (show ((F).obj n.obj) ⊗ V.obj ⟶ (F).obj (n.obj ⊗ V.obj) from
        ((F).obj n.obj ◁ (a).inv.app V) ≫ Functor.LaxMonoidal.μ F n.obj V.obj) := rfl

variable [RightRigidCategory (Mod_ N (i.obj R))] [Simple (𝟙_ (Mod_ N (i.obj R)))]
  [∀ X Y : Mod_ N (i.obj R), FiniteDimensional ℂ (X ⟶ Y)]
  {κ : Type w'} [Fintype κ]
  (SD : FiniteSemisimpleSkeleton (Mod_ N (i.obj R)) κ)

include SD hR in
/-- The actual boundary representative centralizes the actually
translated neutral object. No crossing coherence or preservation square
is an input: both are applied from the actual quotient construction. -/
theorem oddBoundaryRepresentative_centralizes_translated
    (t : R ≅ R) [IsMonHom t.hom]
    (Z X : Pos) :
    letI := neutralModuleBraided i R B himage s hfull hR
    ∀ (b : (Alpha).obj Z ≅ G) (n : Odd) [Simple n.obj],
    (doubleBraiding (i.obj R) n.obj.X).hom = i.map t.hom ▷ n.obj.X →
    ( (doubleBraiding (i.obj R) (Z.obj ⊗ n.obj).X).hom =
      i.map t.hom ▷ (Z.obj ⊗ n.obj).X) →
    Centralizes Z ((neutralModuleComap i R B himage t.hom).obj X) := by
  letI := neutralModuleBraided i R B himage s hfull hR
  intro b n hSimple hn hZn
  letI : IsMonHom (i.mapIso t).hom := inferInstanceAs (IsMonHom (i.map t.hom))
  let V := (neutralModuleComap i R B himage t.hom).obj X
  let c : X ⊙ₗ n ⟶ (homogeneousRightTensor chi 1 V).obj n :=
    translatedBraidingHom (i.mapIso t) X.obj n.obj hn
  let cZ : X ⊙ₗ (((Alpha).obj Z).toFunctor.obj n) ⟶
      (homogeneousRightTensor chi 1 V).obj (((Alpha).obj Z).toFunctor.obj n) :=
    translatedBraidingHom (i.mapIso t) X.obj (Z.obj ⊗ n.obj) hZn
  let cG : X ⊙ₗ (G).toFunctor.obj n ⟶
      (homogeneousRightTensor chi 1 V).obj ((G).toFunctor.obj n) :=
    translatedBraidingHom (i.mapIso t) X.obj ((F).obj n.obj)
      (P.moduleFunctor_translated_monodromy R t n.obj hn)
  let r := (oddBoundaryRightLineator SA i P R B himage s hfull e V n).hom
  haveI : Epi c := by
    apply (ObjectProperty.ι (Homogeneous chi 1)).epi_of_epi_map
    exact inferInstanceAs (Epi (translatedBraidingHom (i.mapIso t) X.obj n.obj hn))
  apply representative_centralizes_of_crossed_square SD chi 1 L (Iso.refl _)
    (neutralNegativeCentralCompatibility i R B himage s hfull hR)
    G Z X V b n c cZ cG r
  · exact translatedBraiding_naturality_right (i.mapIso t) X.obj
      (show Z.obj ⊗ n.obj ⟶ (F).obj n.obj from b.hom.val.app n) hZn _
  · rw [ModuleAlphaInduction.negative_μ]
    have h := translatedBraiding_hexagon (i.mapIso t) X.obj Z.obj n.obj
      (neutralModule_local i R B himage s hfull hR Z) hn hZn
    have hb : localBraidingHom X.obj Z.obj
        (neutralModule_local i R B himage s hfull hR Z) =
        (show X.obj ⊗ Z.obj ⟶ Z.obj ⊗ X.obj from (β_ X Z).hom) := by
      apply RelativeTensor.module_hom_ext
      rw [π_localBraidingHom]
      exact (π_neutralBraiding i R B himage s hfull hR X Z).symm
    rw [hb] at h
    simpa only [Category.assoc] using h
  · change ((a).inv.app X ▷ (F).obj n.obj ≫
        Functor.LaxMonoidal.μ F X.obj n.obj) ≫
        (F).map (translatedBraidingHom (i.mapIso t) X.obj n.obj hn) =
      translatedBraidingHom (i.mapIso t) X.obj ((F).obj n.obj)
        (P.moduleFunctor_translated_monodromy R t n.obj hn) ≫
        ((F).obj n.obj ◁ (a).inv.app V ≫ Functor.LaxMonoidal.μ F n.obj V.obj)
    simpa only [Category.assoc] using
      neutralComparison_translatedBraiding i P R B himage s hfull e t X n.obj hn
  · have h := P.moduleFunctor_localHalfBraiding_boundary R (s.map i) V.obj n.obj
      (neutralModule_local i R B himage s hfull hR V) ((a).app V)
    have hc (m : Odd) :
        (neutralHalfCross chi 1 L (Iso.refl _) V m).hom =
        (show V.obj ⊗ m.obj ⟶ m.obj ⊗ V.obj from
          (((s.map i).localHalfBraiding V.obj
            (neutralModule_local i R B himage s hfull hR V)).β m.obj).hom) := by
      change ((ModuleFunctor.transportCenter ((L).obj V) (Iso.refl _)).2.β m.obj).hom = _
      rw [ModuleFunctor.transportCenter_refl_β]
      rfl
    rw [hc, hc]
    change ((a).inv.app V ▷ (F).obj n.obj ≫
        Functor.LaxMonoidal.μ F V.obj n.obj) ≫
        (F).map (((s.map i).localHalfBraiding V.obj
          (neutralModule_local i R B himage s hfull hR V)).β n.obj).hom =
      (((s.map i).localHalfBraiding V.obj
        (neutralModule_local i R B himage s hfull hR V)).β ((F).obj n.obj)).hom ≫
        ((F).obj n.obj ◁ (a).inv.app V ≫ Functor.LaxMonoidal.μ F n.obj V.obj)
    simpa only [Iso.app_inv, Category.assoc] using h

end Paper18.Category.FixedBoundary
