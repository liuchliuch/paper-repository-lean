import Paper18.Category.EquivariantAdjunction
import Paper18.Category.EquivariantKernels
import Paper18.Category.SemisimpleExistence

/-!
# The actual finite semisimple skeleton of an equivariantization

Every object decomposes into actual simple objects by characteristic-zero
splitting and finite-dimensional End descent. Every equivariant simple is
then detected by one of the finitely many induced underlying simple
representatives. Taking the finite quotient by actual isomorphism gives a
finite family of pairwise nonisomorphic representatives and actual
biproduct decompositions, as required by `FiniteSemisimpleSkeleton`.
-/

noncomputable section
open Classical CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped BigOperators
universe v u w t
namespace Paper18.Category.WeakAction
variable {G : Type w} [Group G] [Fintype G] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  (A : WeakAction G C) [∀ g : G, (A.ρ g).Additive] [∀ g : G, (A.ρ g).Linear ℂ]
  {ι : Type t} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

include S

private theorem simpleDecomposition_exists (Y : A.Equivariant) :
    ∃ (n : ℕ) (f : Fin n → A.Equivariant), (∀ i, Simple (f i)) ∧ Nonempty (Y ≅ ⨁ f) :=
  exists_simple_biproduct_of_splitMonos (fun f => A.equivariantSplitMono S f) Y

/-- The number of actual equivariant simple summands chosen by End descent. -/
def simpleDecompositionLength (Y : A.Equivariant) : ℕ :=
  Classical.choose (A.simpleDecomposition_exists S Y)

/-- The actual equivariant simple objects in a chosen decomposition. -/
def simpleDecompositionFamily (Y : A.Equivariant) :
    Fin (A.simpleDecompositionLength S Y) → A.Equivariant :=
  Classical.choose (Classical.choose_spec (A.simpleDecomposition_exists S Y))

theorem simpleDecompositionFamily_simple (Y : A.Equivariant)
    (a : Fin (A.simpleDecompositionLength S Y)) : Simple (A.simpleDecompositionFamily S Y a) :=
  (Classical.choose_spec (Classical.choose_spec (A.simpleDecomposition_exists S Y))).1 a

/-- The chosen decomposition is an actual categorical isomorphism. -/
def simpleDecompositionIso (Y : A.Equivariant) : Y ≅ ⨁ A.simpleDecompositionFamily S Y :=
  Classical.choice
    (Classical.choose_spec (Classical.choose_spec (A.simpleDecomposition_exists S Y))).2

/-- A finite indexing type for the actual simple summands of the induction
objects of underlying simple representatives. -/
def GeneratorIndex := Σ i : ι, Fin (A.simpleDecompositionLength S (A.induction (S.simpleObject i)))

instance generatorIndex_fintype : Fintype (A.GeneratorIndex S) :=
  inferInstanceAs (Fintype (Σ i : ι,
    Fin (A.simpleDecompositionLength S (A.induction (S.simpleObject i)))))

/-- An actual simple summand of an induced underlying simple. -/
def generatorSimple (a : A.GeneratorIndex S) : A.Equivariant :=
  A.simpleDecompositionFamily S (A.induction (S.simpleObject a.1)) a.2

instance generatorSimple_simple (a : A.GeneratorIndex S) : Simple (A.generatorSimple S a) :=
  A.simpleDecompositionFamily_simple S _ _

/-- Every actual equivariant simple is isomorphic to a summand of one of the
finitely many induced underlying simple representatives. -/
theorem generatorSimple_covers (Y : A.Equivariant) [Simple Y] :
    ∃ a : A.GeneratorIndex S, Nonempty (Y ≅ A.generatorSimple S a) := by
  have hid : 𝟙 Y.obj ≠ 0 := by
    intro hz
    apply CategoryTheory.id_nonzero Y
    apply Equivariant.Hom.ext
    exact hz
  have hp : 0 < Module.finrank ℂ (Y.obj ⟶ Y.obj) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨𝟙 _, hid⟩
  rw [S.finrank_hom_eq_sum] at hp
  obtain ⟨i, hi, hp⟩ := Finset.sum_pos_iff.mp hp
  have hm : 0 < S.multiplicity Y.obj i := pos_of_mul_pos_right hp (Nat.zero_le _)
  obtain ⟨f, hf⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hm
  have hn : A.inductionHom f ≠ 0 := by
    intro hz
    apply hf
    have he := congrArg (fun k => (A.inductionRetract (S.simpleObject i)).i ≫ k.hom) hz
    simpa only [A.inductionHom_inclusion, Equivariant.zero_hom, comp_zero] using he
  have hpos : 0 < Module.finrank ℂ (A.induction (S.simpleObject i) ⟶ Y) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hn⟩
  rw [finrank_hom_iso (A.simpleDecompositionIso S (A.induction (S.simpleObject i))) (Iso.refl Y),
    finrank_biproduct_hom] at hpos
  obtain ⟨a, ha, hp⟩ := Finset.sum_pos_iff.mp hpos
  letI := A.simpleDecompositionFamily_simple S (A.induction (S.simpleObject i)) a
  refine ⟨⟨i, a⟩, ?_⟩
  by_contra hz
  have hzero : Module.finrank ℂ
      (A.simpleDecompositionFamily S (A.induction (S.simpleObject i)) a ⟶ Y) = 0 :=
    CategoryTheory.finrank_hom_simple_simple_eq_zero_of_not_iso ℂ (fun e => hz ⟨e.symm⟩)
  omega

/-- The actual isomorphism relation on the finite family of generator
summands. -/
def generatorSetoid : Setoid (A.GeneratorIndex S) where
  r a b := Nonempty (A.generatorSimple S a ≅ A.generatorSimple S b)
  iseqv :=
    { refl := fun _ => ⟨Iso.refl _⟩
      symm := fun h => h.map Iso.symm
      trans := fun ⟨e⟩ ⟨f⟩ => ⟨e ≪≫ f⟩ }

/-- Actual simple isomorphism classes, obtained as a finite quotient of
actual induced-generator summands. -/
def SimpleIndex := Quotient (A.generatorSetoid S)

instance simpleIndex_fintype : Fintype (A.SimpleIndex S) := by
  change Fintype (Quotient (A.generatorSetoid S))
  infer_instance

/-- An actual chosen simple object for each quotient label. -/
def simpleRepresentative (q : A.SimpleIndex S) : A.Equivariant :=
  A.generatorSimple S (Quotient.out q)

instance simpleRepresentative_simple (q : A.SimpleIndex S) : Simple (A.simpleRepresentative S q) :=
  A.generatorSimple_simple S _

/-- Distinct quotient labels have nonisomorphic actual representatives. -/
theorem simpleRepresentative_iso_injective (q r : A.SimpleIndex S)
    (h : Nonempty (A.simpleRepresentative S q ≅ A.simpleRepresentative S r)) : q = r := by
  have he : Quotient.mk (A.generatorSetoid S) (Quotient.out q) =
      Quotient.mk (A.generatorSetoid S) (Quotient.out r) := Quotient.sound h
  simpa only [Quotient.out_eq] using he

/-- The quotient representatives cover every actual categorical simple. -/
theorem simpleRepresentative_covers (Y : A.Equivariant) [Simple Y] :
    ∃ q : A.SimpleIndex S, Nonempty (Y ≅ A.simpleRepresentative S q) := by
  obtain ⟨a, ⟨e⟩⟩ := A.generatorSimple_covers S Y
  let q : A.SimpleIndex S := Quotient.mk _ a
  have hrel : Nonempty (A.simpleRepresentative S q ≅ A.generatorSimple S a) :=
    Quotient.exact (Quotient.out_eq q)
  exact ⟨q, hrel.map (fun f => e ≪≫ f.symm)⟩

/-- A quotient label for each simple summand in an arbitrary decomposition. -/
def equivariantLabel (Y : A.Equivariant) (a : Fin (A.simpleDecompositionLength S Y)) : A.SimpleIndex S := by
  letI := A.simpleDecompositionFamily_simple S Y a
  exact Classical.choose (A.simpleRepresentative_covers S (A.simpleDecompositionFamily S Y a))

/-- Each chosen decomposition summand is identified with its actual
quotient representative. -/
def equivariantSummandIso (Y : A.Equivariant) (a : Fin (A.simpleDecompositionLength S Y)) :
    A.simpleDecompositionFamily S Y a ≅ A.simpleRepresentative S (A.equivariantLabel S Y a) := by
  letI := A.simpleDecompositionFamily_simple S Y a
  exact Classical.choice
    (Classical.choose_spec (A.simpleRepresentative_covers S (A.simpleDecompositionFamily S Y a)))

/-- Finite semisimplicity of the actual equivariantization, with numerical
multiplicities subsequently derived from its Hom spaces. -/
def equivariantSkeleton : FiniteSemisimpleSkeleton A.Equivariant (A.SimpleIndex S) where
  simpleObject := A.simpleRepresentative S
  simple := A.simpleRepresentative_simple S
  iso_injective := A.simpleRepresentative_iso_injective S
  length := A.simpleDecompositionLength S
  label := A.equivariantLabel S
  decomposition Y := A.simpleDecompositionIso S Y ≪≫
    biproduct.mapIso (A.equivariantSummandIso S Y)

omit S

omit [HasKernels C] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] in
/-- Simplicity of an actual underlying object implies simplicity in the
finite equivariantization. -/
theorem simple_of_underlying_simple (Y : A.Equivariant) [Simple Y.obj] : Simple Y where
  mono_isIso_iff_nonzero {X} f _ := by
    constructor
    · intro hf hz
      letI := hf
      haveI : IsIso f.hom := by change IsIso (A.forget.map f); infer_instance
      have hn := (Simple.mono_isIso_iff_nonzero f.hom).mp (by infer_instance)
      apply hn
      simpa only [Equivariant.zero_hom] using congrArg Equivariant.Hom.hom hz
    · intro hf
      have hn : f.hom ≠ 0 := by
        intro hz
        apply hf
        exact Equivariant.Hom.ext hz
      letI := isIso_of_mono_of_nonzero hn
      letI : IsIso (A.forget.map f) := by
        change IsIso f.hom
        infer_instance
      exact isIso_of_reflects_iso f A.forget

/-- The actual equivariant tensor unit is simple whenever the original
fusion-category unit is simple. -/
instance equivariant_simple_unit [MonoidalCategory C]
    [∀ g : G, (A.ρ g).Monoidal] [A.IsMonoidal] [Simple (𝟙_ C)] :
    Simple (𝟙_ A.Equivariant) := by
  haveI : Simple ((𝟙_ A.Equivariant).obj) := by
    change Simple (𝟙_ C)
    infer_instance
  exact A.simple_of_underlying_simple _

end Paper18.Category.WeakAction
