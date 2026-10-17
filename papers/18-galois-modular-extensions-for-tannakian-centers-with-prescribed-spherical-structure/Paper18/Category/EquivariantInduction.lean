import Paper18.Category.EquivariantBasic

/-!
# Induction for a finite weak categorical group action

The equivariant induction of `X` has underlying object `⨁ g, ρ(g) X`.
Its equivariant structure is constructed from the action multiplication
isomorphisms and the permutations of the finite group by left translation.
The underlying identity summand exhibits `X` as an actual retract of its
induction. Thus dominance of the forgetful functor is proved categorically.
-/

noncomputable section
open Classical CategoryTheory CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category

section MapBiproduct
/-- Additivity preserves a finite biproduct also when its finite indexing
type lies in an arbitrary universe. -/
theorem additive_preservesBiproductsOfFiniteShape
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] (J : Type*) [Finite J] :
    PreservesBiproductsOfShape J F := by
  letI := Fintype.ofFinite J
  exact
    { preserves :=
      { preserves := fun hb =>
          ⟨isBilimitOfTotal _ (by
            simp_rw [Functor.mapBicone_π, Functor.mapBicone_ι, ← Functor.map_comp]
            erw [← F.map_sum, ← F.map_id, IsBilimit.total hb])⟩ } }

attribute [local instance] additive_preservesBiproductsOfFiniteShape

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  (F : C ⥤ D) [F.Additive] {J : Type*} [Fintype J] (f : J → C) [HasBiproduct f]

@[reassoc (attr := simp)]
theorem map_biproduct_ι (j : J) :
    F.map (biproduct.ι f j) ≫ (F.mapBiproduct f).hom =
      biproduct.ι (fun j => F.obj (f j)) j := by
  apply biproduct.hom_ext
  intro k
  erw [Functor.mapBiproduct_hom, Category.assoc,
    biproduct.lift_π (fun j => F.map (biproduct.π f j)) k,
    ← F.map_comp, biproduct.ι_π f j k, biproduct.ι_π (F.obj ∘ f) j k]
  split_ifs with h
  · subst k; simp
  · simp


/-- An additive functor sends biproduct inclusions to a jointly epic family. -/
theorem map_biproduct_hom_ext {Z : D} (p q : F.obj (⨁ f) ⟶ Z)
    (h : ∀ j, F.map (biproduct.ι f j) ≫ p = F.map (biproduct.ι f j) ≫ q) : p = q := by
  apply (cancel_epi (F.mapBiproduct f).inv).mp
  apply biproduct.hom_ext'
  intro j
  simpa [Functor.mapBiproduct_inv] using h j
end MapBiproduct

attribute [local instance] additive_preservesBiproductsOfFiniteShape

namespace WeakAction
variable {G : Type w} [Group G] [Fintype G]
  {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (A : WeakAction G C) [∀ g : G, (A.ρ g).Additive]

/-- The finite sum of the translates of an object. -/
def inductionObj (X : C) : C := ⨁ fun h : G => (A.ρ h).obj X

/-- Translation permutes the summands of induction via the actual weak
multiplication isomorphisms of the action. -/
def inductionIso (X : C) (g : G) : (A.ρ g).obj (A.inductionObj X) ≅ A.inductionObj X :=
  (A.ρ g).mapBiproduct (fun h : G => (A.ρ h).obj X) ≪≫
    biproduct.whiskerEquiv (Equiv.mulLeft g) (fun h => ((A.mulIso g h).app X).symm)

@[reassoc (attr := simp)]
theorem map_ι_inductionIso (X : C) (g h : G) :
    (A.ρ g).map (biproduct.ι (fun k : G => (A.ρ k).obj X) h) ≫
      (A.inductionIso X g).hom =
        (A.mulIso g h).hom.app X ≫ biproduct.ι (fun k : G => (A.ρ k).obj X) (g * h) := by
  dsimp only [inductionIso, Iso.trans_hom]
  rw [← Category.assoc, map_biproduct_ι]
  simp [biproduct.whiskerEquiv_hom]

/-- The induction structure obeys the weak-action unit condition. -/
theorem inductionIso_unit (X : C) :
    (A.inductionIso X 1).hom = A.unitIso.hom.app (A.inductionObj X) := by
  apply map_biproduct_hom_ext (A.ρ 1) (fun h : G => (A.ρ h).obj X)
  intro h
  rw [A.map_ι_inductionIso]
  calc
    _ = A.unitIso.hom.app ((A.ρ h).obj X) ≫
        biproduct.ι (fun k : G => (A.ρ k).obj X) h := by
      have hu := A.one_mul h X
      have hu' := hu =≫ biproduct.ι (fun k : G => (A.ρ k).obj X) h
      rw [Category.assoc, biproduct.eqToHom_comp_ι (fun k : G => (A.ρ k).obj X) (_root_.one_mul h)] at hu'
      exact hu' 
    _ = _ := (A.unitIso.hom.naturality _).symm

/-- The induction structure obeys the multiplication condition. This uses
the full coherence axiom of the weak action. -/
theorem inductionIso_mul (X : C) (g h : G) :
    (A.ρ g).map ((A.inductionIso X h).hom) ≫ (A.inductionIso X g).hom =
      (A.mulIso g h).hom.app (A.inductionObj X) ≫ (A.inductionIso X (g * h)).hom := by
  apply map_biproduct_hom_ext (A.ρ h ⋙ A.ρ g) (fun k : G => (A.ρ k).obj X)
  intro k
  change (A.ρ g).map ((A.ρ h).map (biproduct.ι _ k)) ≫ _ = _
  rw [← Functor.map_comp_assoc, A.map_ι_inductionIso, Functor.map_comp,
    Category.assoc, A.map_ι_inductionIso]
  conv_rhs =>
    erw [← Category.assoc, (A.mulIso g h).hom.naturality (biproduct.ι (fun k : G => (A.ρ k).obj X) k), Category.assoc,
      A.map_ι_inductionIso]
  have hc := A.assoc g h k X
  have hc' := hc =≫ biproduct.ι (fun t : G => (A.ρ t).obj X) (g * (h * k))
  simp only [Category.assoc] at hc'
  rw [biproduct.eqToHom_comp_ι (fun t : G => (A.ρ t).obj X) (mul_assoc g h k)] at hc'
  exact hc' 

/-- The actual equivariant object induced from an arbitrary object. -/
def induction (X : C) : A.Equivariant where
  obj := A.inductionObj X
  structureIso := A.inductionIso X
  unit := A.inductionIso_unit X
  mul := A.inductionIso_mul X

/-- The identity summand in induction, transported by the action unit
isomorphism, gives actual inclusion and projection maps for `X`. -/
def inductionRetract (X : C) : Retract X (A.forget.obj (A.induction X)) where
  i := (A.unitIso.app X).inv ≫ biproduct.ι (fun h : G => (A.ρ h).obj X) 1
  r := biproduct.π (fun h : G => (A.ρ h).obj X) 1 ≫ (A.unitIso.app X).hom
  retract := by simp

/-- Categorical retract dominance of the forgetful functor follows from
induction. It is not an assumption on the action. -/
theorem forget_retract_dominant (X : C) :
    ∃ Y : A.Equivariant, Nonempty (Retract X (A.forget.obj Y)) :=
  ⟨A.induction X, ⟨A.inductionRetract X⟩⟩

end WeakAction
end Paper18.Category
