import Paper18.Category.CrossedBraidedGauging
import Paper18.Category.FixedBoundaryEquivariantMonoidal
import Paper18.Category.EquivariantBraided

/-! # Genuine neutral action embeddings remain braided after gauging -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits Functor.LaxMonoidal
open Paper18.Category.CrossedBraidedGauging
universe v u v' u' w
namespace Paper18.Category.FixedBoundary.MinimalExistence
variable {G : Type w} [Group G] [Fintype G]
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [BraidedCategory C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [MonoidalCategory D] [MonoidalPreadditive D] [HasKernels D] [HasFiniteBiproducts D]
  {A : WeakAction G C} {H : WeakAction G D}
  [∀ g : G, (A.ρ g).Monoidal] [A.IsMonoidal] [A.IsBraided]
  [∀ g : G, (H.ρ g).Monoidal] [H.IsMonoidal]
  [∀ g : G, (A.ρ g).Additive] [∀ g : G, (A.ρ g).Linear ℂ]
  [∀ g : G, (H.ρ g).Additive] [∀ g : G, (H.ρ g).Linear ℂ]
  (F : A.Intertwiner H) [F.functor.Monoidal] [F.IsMonoidal]

instance intertwinerEquivariantAdditive [F.functor.Additive] : F.equivariantFunctor.Additive where
  map_add := by
    intro X Y f g
    apply WeakAction.Equivariant.Hom.ext
    exact F.functor.map_add

instance intertwinerEquivariantLinear [F.functor.Linear ℂ] : F.equivariantFunctor.Linear ℂ where
  map_smul f c := by
    apply WeakAction.Equivariant.Hom.ext
    exact F.functor.map_smul c f.hom

variable {P : Grading G D} {Q : GradedAction P H} (B : CrossedBraiding P H Q)

/-- Compatibility with the actual neutral crossing, together with actual
monoidal action coherence, proves preservation of the gauged braiding. -/
def equivariantEmbeddingBraided
    (hdeg : ∀ X : C, P.Homogeneous 1 (F.functor.obj X))
    (hβ : ∀ X Y : C, μ F.functor X Y ≫ F.functor.map (β_ X Y).hom =
      (B.neutralIso (F.functor.obj X) (hdeg X) (F.functor.obj Y)).hom ≫ μ F.functor Y X) :
    letI := B.equivariantBraidedCategory
    F.equivariantFunctor.Braided := by
  letI := B.equivariantBraidedCategory
  refine { toMonoidal := inferInstance, braided := ?_ }
  intro X Y
  apply WeakAction.Equivariant.Hom.ext
  change μ F.functor X.obj Y.obj ≫ F.functor.map (β_ X.obj Y.obj).hom =
    (B.halfSwapIso (F.functor.obj X.obj) (F.equivariantFunctor.obj Y)).hom ≫
      μ F.functor Y.obj X.obj
  rw [B.halfSwapIso_homogeneous 1 _ (hdeg X.obj), ← B.neutralIso_eq_block]
  exact hβ X.obj Y.obj

end Paper18.Category.FixedBoundary.MinimalExistence
