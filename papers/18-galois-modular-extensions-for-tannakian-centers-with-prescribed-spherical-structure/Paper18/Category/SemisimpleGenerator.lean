import Paper18.Category.SemisimpleExistence

/-! # Finite skeletons from actual finite generators

Decomposing finitely many generating objects and quotienting their actual
simple summands by categorical isomorphism produces a complete finite
semisimple skeleton. No numerical multiplicity laws enter the construction.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category
variable (C : Type u) [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

/-- Actual finite simple decompositions, without a prior finite list of
all isomorphism classes. -/
structure SimpleDecompositions where
  length : C → ℕ
  family : ∀ X, Fin (length X) → C
  simple : ∀ X i, Simple (family X i)
  iso : ∀ X, X ≅ ⨁ family X

/-- A finite family covers the actual simples when every simple is an
actual categorical retract of one of its members. -/
structure FiniteSimpleGenerator (J : Type w) [Fintype J] where
  obj : J → C
  covers : ∀ X : C, Simple X → ∃ j, Nonempty (Retract X (obj j))

variable {C} [Linear ℂ C] [HasKernels C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]

/-- Endomorphism-dimension descent constructs actual decomposition data. -/
def SimpleDecompositions.ofSplitMonos
    (split : ∀ {X Y : C} (f : X ⟶ Y) [Mono f], SplitMono f) :
    SimpleDecompositions C where
  length X := Classical.choose (exists_simple_biproduct_of_splitMonos split X)
  family X := Classical.choose (Classical.choose_spec (exists_simple_biproduct_of_splitMonos split X))
  simple X := (Classical.choose_spec (Classical.choose_spec
    (exists_simple_biproduct_of_splitMonos split X))).1
  iso X := Classical.choice (Classical.choose_spec (Classical.choose_spec
    (exists_simple_biproduct_of_splitMonos split X))).2

namespace SimpleDecompositions
variable (D : SimpleDecompositions C) {J : Type w} [Fintype J]
  (G : FiniteSimpleGenerator C J)

/-- The finite family of actual simple summands of the generating objects. -/
def GeneratorIndex := Σ j : J, Fin (D.length (G.obj j))
instance : Fintype (D.GeneratorIndex G) := inferInstanceAs (Fintype (Σ j : J, Fin (D.length (G.obj j))))
def generatorSimple (a : D.GeneratorIndex G) : C := D.family (G.obj a.1) a.2
instance (a : D.GeneratorIndex G) : Simple (D.generatorSimple G a) := D.simple _ _

theorem generatorSimple_covers (X : C) [Simple X] :
    ∃ a : D.GeneratorIndex G, Nonempty (X ≅ D.generatorSimple G a) := by
  obtain ⟨j, ⟨r⟩⟩ := G.covers X inferInstance
  have hn : r.i ≠ 0 := by
    intro hz
    apply CategoryTheory.id_nonzero X
    rw [← r.retract, hz, zero_comp]
  have hp : 0 < Module.finrank ℂ (X ⟶ G.obj j) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨r.i, hn⟩
  rw [finrank_hom_iso (Iso.refl X) (D.iso (G.obj j)), finrank_hom_biproduct] at hp
  obtain ⟨a, _, ha⟩ := Finset.sum_pos_iff.mp hp
  letI := D.simple (G.obj j) a
  refine ⟨⟨j, a⟩, ?_⟩
  by_contra he
  have hzero : Module.finrank ℂ (X ⟶ D.family (G.obj j) a) = 0 :=
    CategoryTheory.finrank_hom_simple_simple_eq_zero_of_not_iso ℂ (fun e => he ⟨e⟩)
  omega

def generatorSetoid : Setoid (D.GeneratorIndex G) where
  r a b := Nonempty (D.generatorSimple G a ≅ D.generatorSimple G b)
  iseqv :=
    { refl := fun _ => ⟨Iso.refl _⟩
      symm := fun h => h.map Iso.symm
      trans := fun ⟨e⟩ ⟨f⟩ => ⟨e ≪≫ f⟩ }

/-- A finite quotient of actual simple summands by actual isomorphism. -/
def SimpleIndex := Quotient (D.generatorSetoid G)
instance : Fintype (D.SimpleIndex G) := by
  change Fintype (Quotient (D.generatorSetoid G))
  infer_instance

def representative (q : D.SimpleIndex G) : C := D.generatorSimple G (Quotient.out q)
instance (q : D.SimpleIndex G) : Simple (D.representative G q) := by
  unfold representative
  infer_instance

omit [HasKernels C] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] in
theorem representative_iso_injective (q r : D.SimpleIndex G)
    (h : Nonempty (D.representative G q ≅ D.representative G r)) : q = r := by
  have he : Quotient.mk (D.generatorSetoid G) (Quotient.out q) =
      Quotient.mk (D.generatorSetoid G) (Quotient.out r) := Quotient.sound h
  simpa only [Quotient.out_eq] using he

theorem representative_covers (X : C) [Simple X] :
    ∃ q : D.SimpleIndex G, Nonempty (X ≅ D.representative G q) := by
  obtain ⟨a, ⟨e⟩⟩ := D.generatorSimple_covers G X
  let q : D.SimpleIndex G := Quotient.mk _ a
  have hrel : Nonempty (D.representative G q ≅ D.generatorSimple G a) :=
    Quotient.exact (Quotient.out_eq q)
  exact ⟨q, hrel.map (fun f => e ≪≫ f.symm)⟩

def label (X : C) (a : Fin (D.length X)) : D.SimpleIndex G := by
  letI := D.simple X a
  exact Classical.choose (D.representative_covers G (D.family X a))

def summandIso (X : C) (a : Fin (D.length X)) :
    D.family X a ≅ D.representative G (D.label G X a) := by
  letI := D.simple X a
  exact Classical.choice (Classical.choose_spec (D.representative_covers G (D.family X a)))

/-- The actual finite semisimple skeleton derived from decompositions and
a finite categorical generating family. -/
def skeleton : FiniteSemisimpleSkeleton C (D.SimpleIndex G) where
  simpleObject := D.representative G
  simple := fun _ => inferInstance
  iso_injective := D.representative_iso_injective G
  length := D.length
  label := D.label G
  decomposition X := D.iso X ≪≫ biproduct.mapIso (D.summandIso G X)

end SimpleDecompositions
end Paper18.Category
