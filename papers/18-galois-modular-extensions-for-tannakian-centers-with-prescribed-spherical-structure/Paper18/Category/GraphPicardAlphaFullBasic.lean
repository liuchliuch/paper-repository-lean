import Paper18.Category.GraphPicardImageCommutant
import Paper18.Category.GraphPicardMoritaImageCentral

/-! # Actual fullness from the genuine image commutant -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u v' u' v'' u''
namespace Paper18.Category.GraphPicard

section Precompose
variable {C : Type u} [Category.{v} C]
  {D : Type u'} [Category.{v'} D] {E : Type u''} [Category.{v''} E]

/-- Fullness after an actual equivalence of the source gives actual
fullness before that reindexing. -/
def fullOfEquivalencePrecompose (F : C ⥤ D) [F.IsEquivalence] (G : D ⥤ E)
    [(F ⋙ G).Full] : G.Full := by
  let e : G ≅ F.inv ⋙ (F ⋙ G) :=
    (Functor.leftUnitor G).symm ≪≫
      Functor.isoWhiskerRight F.asEquivalence.counitIso.symm G
  exact Functor.Full.of_iso e.symm
end Precompose

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasFiniteBiproducts C] [MonoidalCategory C]
  {E : Type u'} [Category.{v'} E] [Preadditive E] [Linear ℂ E]
  [HasFiniteBiproducts E] [MonoidalCategory E]
  [MonoidalPreadditive E] [MonoidalLinear ℂ E]
  (A : C ⥤ Center E) [A.Monoidal] [A.Additive] [A.Linear ℂ]
  (B : C ⥤ Center E)

/-- Every actual underlying morphism is a genuine central morphism on
the actual image category, by the proved opposite-action commutant. -/
def commutantCentralCoreHom
    (e : B ⋙ Center.forget E ≅ A ⋙ Center.forget E)
    (hc : ∀ X Y : C, Centralizes (A.obj X) (B.obj Y))
    {X Y : C} (f : (A.obj X).1 ⟶ (A.obj Y).1) :
    (MoritaImage.centralCore A).obj X ⟶ (MoritaImage.centralCore A).obj Y where
  f := f
  comm V := by
    obtain ⟨Z, ⟨r⟩⟩ := V.property
    exact image_retract_commutant A B e hc f Z r

/-- Actual fullness of the genuine restricted central lift supplies
actual underlying fullness. The morphism centrality is derived, rather
than assumed for the original ambient maps. -/
def fullUnderlyingOfCentralCore
    (e : B ⋙ Center.forget E ≅ A ⋙ Center.forget E)
    (hc : ∀ X Y : C, Centralizes (A.obj X) (B.obj Y))
    [(MoritaImage.centralCore A).Full] : (A ⋙ Center.forget E).Full where
  map_surjective {X Y} f := by
    let q := commutantCentralCoreHom A B e hc f
    refine ⟨(MoritaImage.centralCore A).preimage q, ?_⟩
    exact congrArg Center.Hom.f ((MoritaImage.centralCore A).map_preimage q)

end Paper18.Category.GraphPicard
