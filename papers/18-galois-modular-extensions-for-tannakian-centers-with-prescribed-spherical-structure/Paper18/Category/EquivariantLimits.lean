import Paper18.Category.EquivariantKernels
import Paper18.Category.EquivariantBiproducts
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-!
# Cokernels in a weak equivariantization

The construction is dual to the actual kernel construction. The underlying
cokernel acquires its equivariant structure from preservation by translation
and the universal map of the equivariant square.
-/

noncomputable section
open Classical CategoryTheory CategoryTheory.Limits
universe v u w
namespace Paper18.Category.WeakAction
variable {G : Type w} [Group G] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear ℂ C] [HasCokernels C]
  (A : WeakAction G C) [∀ g : G, (A.ρ g).Additive] [∀ g : G, (A.ρ g).Linear ℂ]
  {X Y : A.Equivariant} (f : X ⟶ Y)

/-- The coherent cokernel structure is induced by the actual action
isomorphisms and the equivariant commutative square. -/
def cokernelStructureIso (g : G) : (A.ρ g).obj (cokernel f.hom) ≅ cokernel f.hom :=
  PreservesCokernel.iso (A.ρ g) f.hom ≪≫
    cokernel.mapIso ((A.ρ g).map f.hom) f.hom
      (X.structureIso g) (Y.structureIso g) (f.comm g)

omit [Linear ℂ C] [∀ g : G, (A.ρ g).Linear ℂ] in
@[reassoc (attr := simp)]
theorem π_cokernelStructureIso (g : G) :
    (A.ρ g).map (cokernel.π f.hom) ≫ (A.cokernelStructureIso f g).hom =
      (Y.structureIso g).hom ≫ cokernel.π f.hom := by
  simp only [cokernelStructureIso, Iso.trans_hom, ← Category.assoc,
    PreservesCokernel.π_iso_hom, cokernel.mapIso_hom, cokernel.map,
    cokernel.π_desc]

/-- The underlying cokernel equipped with its induced coherent action. -/
def equivariantCokernelObj : A.Equivariant where
  obj := cokernel f.hom
  structureIso := A.cokernelStructureIso f
  unit := by
    apply (cancel_epi ((A.ρ 1).map (cokernel.π f.hom))).mp
    rw [A.π_cokernelStructureIso, Y.unit]
    exact (A.unitIso.hom.naturality (cokernel.π f.hom)).symm
  mul g h := by
    apply (cancel_epi ((A.ρ g).map ((A.ρ h).map (cokernel.π f.hom)))).mp
    rw [← Category.assoc, ← Functor.map_comp, A.π_cokernelStructureIso,
      Functor.map_comp, Category.assoc, A.π_cokernelStructureIso,
      ← Category.assoc, Y.mul]
    have hn := (A.mulIso g h).hom.naturality (cokernel.π f.hom)
    simp only [Functor.comp_map] at hn
    rw [← Category.assoc, hn]
    simp only [Category.assoc, A.π_cokernelStructureIso]

/-- The underlying cokernel projection is equivariant. -/
def equivariantCokernelπ : Y ⟶ A.equivariantCokernelObj f :=
  ⟨cokernel.π f.hom, fun g => A.π_cokernelStructureIso f g⟩

omit [Linear ℂ C] [∀ g : G, (A.ρ g).Linear ℂ] in
@[simp] theorem equivariantCokernelπ_hom :
    (A.equivariantCokernelπ f).hom = cokernel.π f.hom := rfl

@[reassoc (attr := simp)]
theorem equivariantCokernelπ_condition : f ≫ A.equivariantCokernelπ f = 0 := by
  apply Equivariant.Hom.ext
  exact cokernel.condition f.hom

/-- The underlying universal cokernel descent is equivariant, by its
uniqueness after precomposition with the translated cokernel projection. -/
def equivariantCokernelDesc {Z : A.Equivariant} (k : Y ⟶ Z) (hk : f ≫ k = 0) :
    A.equivariantCokernelObj f ⟶ Z where
  hom := cokernel.desc f.hom k.hom (by simpa using congrArg Equivariant.Hom.hom hk)
  comm g := by
    apply (cancel_epi ((A.ρ g).map (cokernel.π f.hom))).mp
    dsimp only [equivariantCokernelObj]
    rw [← Category.assoc, ← Functor.map_comp, cokernel.π_desc,
      ← Category.assoc, A.π_cokernelStructureIso]
    simpa only [Category.assoc, cokernel.π_desc] using k.comm g

@[reassoc (attr := simp)]
theorem equivariantCokernelπ_desc {Z : A.Equivariant} (k : Y ⟶ Z) (hk : f ≫ k = 0) :
    A.equivariantCokernelπ f ≫ A.equivariantCokernelDesc f k hk = k := by
  apply Equivariant.Hom.ext
  exact cokernel.π_desc _ _ _

instance equivariantCokernelπ_epi : Epi (A.equivariantCokernelπ f) :=
  A.forget.epi_of_epi_map (inferInstance : Epi (cokernel.π f.hom))

/-- The constructed actual cokernel cofork satisfies its universal property
inside the equivariant category. -/
def equivariantCokernelIsColimit :
    IsColimit (CokernelCofork.ofπ (A.equivariantCokernelπ f)
      (A.equivariantCokernelπ_condition f)) :=
  CokernelCofork.IsColimit.ofπ' _ _ (fun k hk =>
    ⟨A.equivariantCokernelDesc f k hk, A.equivariantCokernelπ_desc f k hk⟩)

instance equivariant_hasCokernel : HasCokernel f where
  exists_colimit := ⟨⟨CokernelCofork.ofπ (A.equivariantCokernelπ f)
    (A.equivariantCokernelπ_condition f), A.equivariantCokernelIsColimit f⟩⟩

instance equivariant_hasCokernels : HasCokernels A.Equivariant where
  has_colimit f := A.equivariant_hasCokernel f

/-- The forgetful functor preserves the actual cokernel just constructed. -/
instance forget_preservesCokernel : PreservesColimit (parallelPair f 0) A.forget := by
  apply preservesColimit_of_preserves_colimit_cocone (A.equivariantCokernelIsColimit f)
  exact (CokernelCofork.isColimitMapCoconeEquiv
    (CokernelCofork.ofπ (A.equivariantCokernelπ f) (A.equivariantCokernelπ_condition f))
      A.forget).symm (cokernelIsCokernel f.hom)

end Paper18.Category.WeakAction

namespace Paper18.Category.WeakAction
variable {G : Type w} [Group G] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear ℂ C] [HasFiniteBiproducts C]
  (A : WeakAction G C) [∀ g : G, (A.ρ g).Additive] [∀ g : G, (A.ρ g).Linear ℂ]

/-- Actual kernels and finite biproducts yield all finite limits in the
equivariantization. -/
instance equivariant_hasFiniteLimits [HasKernels C] : HasFiniteLimits A.Equivariant := by
  letI : HasEqualizers A.Equivariant := Preadditive.hasEqualizers_of_hasKernels
  exact hasFiniteLimits_of_hasEqualizers_and_finite_products

/-- Dually, actual cokernels and finite biproducts yield all finite colimits
in the equivariantization. -/
instance equivariant_hasFiniteColimits [HasCokernels C] : HasFiniteColimits A.Equivariant := by
  letI : HasCoequalizers A.Equivariant := Preadditive.hasCoequalizers_of_hasCokernels
  exact hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts

end Paper18.Category.WeakAction
