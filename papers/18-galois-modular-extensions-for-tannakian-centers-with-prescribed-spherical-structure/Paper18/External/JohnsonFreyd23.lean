import Paper18.Category.GaloisBraidedExtension
import Paper18.Category.TannakianBasic

/-!
# Explicit external input: Johnson--Freyd Proposition 2.3

Source: T. Johnson--Freyd, *Schopieray's Galois-modular extension
conjecture*, arXiv:2601.23192v1 (2026), Proposition 2.3, labelled
`prop:summarytannakian` in the original TeX source. Its statement is:
every complex braided fusion category with Tannakian center admits a
nondegenerate braided extension with integral centralizer.

`JohnsonFreyd23` states that published result as an explicit hypothesis.
This module supplies no inhabitant, axiom, or placeholder proof. In
particular neither pivotal data nor spherical compatibility is included
in this external input. Those are the subject of the present paper.
The skeleton is a presentation of fusion finiteness; the displayed
universe bounds are bookkeeping for an essentially small realization.
-/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u w vOut uOut wOut
namespace Paper18.External

/-- The published JF Proposition 2.3, retained as an explicit external
input over every actual braided fusion category at the indicated sizes.
There is deliberately no instance or theorem asserting this proposition. -/
def JohnsonFreyd23At : Prop :=
  ∀ {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
    [HasKernels C] [HasFiniteBiproducts C]
    [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    [RightRigidCategory C] [Simple (𝟙_ C)] [BraidedCategory C]
    {ι : Type w} [Fintype ι] (_S : Category.FiniteSemisimpleSkeleton C ι)
    {G : Type} [Group G],
    Category.TannakianCenter C G →
      Nonempty (Category.GaloisBraidedExtension.{v,u,vOut,uOut,wOut} C)

/-- The canonical size choice used in the original standalone JF contract.
`JohnsonFreyd23At` also allows the same essentially small target size to be
retained when the published theorem is applied a second time to a full
fusion subcategory. This avoids an artificial universe increase. -/
abbrev JohnsonFreyd23 : Prop :=
  JohnsonFreyd23At.{v,u,w,max u v,max u (v+1),max (max u v) w}

end Paper18.External
