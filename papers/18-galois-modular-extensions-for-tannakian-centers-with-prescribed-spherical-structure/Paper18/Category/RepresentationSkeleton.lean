import Paper18.Category.RepresentationSemisimple
import Mathlib.RingTheory.Finiteness.Finsupp

/-!
# Finitely many genuine irreducible representations

The regular representation is finite dimensional and semisimple. Its simple
summands contain a representative of every actual simple object, because a
nonzero vector defines a nonzero map from the regular representation.
-/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators
namespace Paper18.Category.Representation
variable {G : Type} [Group G] [Fintype G]

/-- The actual finite regular representation, obtained from left
multiplication on the complex group algebra. -/
def regular : FDRep ℂ G := ofModule (G := G) (MonoidAlgebra ℂ G)

omit [Fintype G] in
/-- A categorically simple finite representation has a nonzero vector. -/
theorem exists_nonzero_vector (V : FDRep ℂ G) [Simple V] :
    ∃ v : _root_.Representation.asModule V.ρ, v ≠ 0 := by
  by_contra hn
  push_neg at hn
  apply id_nonzero V
  apply (toGroupAlgebra (G := G)).map_injective
  simp only [Functor.map_zero]
  apply ModuleCat.hom_ext
  ext v
  exact hn v

/-- Every simple representation receives a nonzero morphism from the actual
regular representation. -/
theorem exists_nonzero_regular_hom (V : FDRep ℂ G) [Simple V] :
    ∃ f : regular (G := G) ⟶ V, f ≠ 0 := by
  obtain ⟨v, hv⟩ := exists_nonzero_vector V
  let F := toGroupAlgebra (G := G)
  let e := toGroupAlgebra_ofModuleIso (G := G) (MonoidAlgebra ℂ G)
  let f := F.preimage (e.hom ≫ ModuleCat.ofHom
    (LinearMap.toSpanSingleton (MonoidAlgebra ℂ G) (_root_.Representation.asModule V.ρ) v))
  refine ⟨f, ?_⟩
  intro hf
  have hm := congrArg F.map hf
  simp only [f, Functor.map_preimage, Functor.map_zero] at hm
  have hm' : ModuleCat.ofHom
      (LinearMap.toSpanSingleton (MonoidAlgebra ℂ G) (_root_.Representation.asModule V.ρ) v) = 0 := by
    apply (cancel_epi e.hom).mp
    simpa using hm
  have hlin := congrArg ModuleCat.Hom.hom hm'
  exact hv (by simpa using LinearMap.congr_fun hlin 1)

/-- A finite family of actual simple representations is complete: every
actual categorical simple is isomorphic to a member. Duplicates will be
removed when choosing the skeleton. -/
theorem exists_finite_complete_simple_family :
    ∃ (n : ℕ) (W : Fin n → FDRep ℂ G), (∀ i, Simple (W i)) ∧
      ∀ V : FDRep ℂ G, Simple V → ∃ i, Nonempty (V ≅ W i) := by
  obtain ⟨n, W, hs, ⟨e⟩⟩ := exists_simple_biproduct (regular (G := G))
  refine ⟨n, W, hs, ?_⟩
  intro V hV
  letI := hV
  obtain ⟨f, hf⟩ := exists_nonzero_regular_hom V
  have hex : ∃ i, biproduct.ι W i ≫ e.inv ≫ f ≠ 0 := by
    by_contra hn
    push_neg at hn
    have hg : e.inv ≫ f = 0 := by
      apply biproduct.hom_ext'
      intro i
      simpa only [comp_zero, Category.assoc] using hn i
    apply hf
    calc
      f = e.hom ≫ (e.inv ≫ f) := by simp
      _ = 0 := by rw [hg, comp_zero]
  obtain ⟨i, hi⟩ := hex
  letI := hs i
  letI : IsIso (biproduct.ι W i ≫ e.inv ≫ f) := isIso_of_hom_simple hi
  exact ⟨i, ⟨(asIso (biproduct.ι W i ≫ e.inv ≫ f)).symm⟩⟩

end Paper18.Category.Representation

namespace Paper18.Category.Representation
variable {G : Type} [Group G] [Fintype G] {n : ℕ}

/-- Isomorphism of members of a finite family of actual representations. -/
def isoSetoid (W : Fin n → FDRep ℂ G) : Setoid (Fin n) where
  r i j := Nonempty (W i ≅ W j)
  iseqv := ⟨fun _ => ⟨Iso.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩,
    fun ⟨e⟩ ⟨f⟩ => ⟨e ≪≫ f⟩⟩

/-- Finite labels obtained by removing isomorphic duplicates from a finite
family, using actual categorical isomorphisms. -/
abbrev IsoLabels (W : Fin n → FDRep ℂ G) := Quotient (isoSetoid W)

/-- Chosen actual representative of an isomorphism class. -/
def isoRepresentative (W : Fin n → FDRep ℂ G) (i : IsoLabels W) : FDRep ℂ G := W i.out

omit [Fintype G] in
lemma isoRepresentative_injective (W : Fin n → FDRep ℂ G)
    (i j : IsoLabels W) (h : Nonempty (isoRepresentative W i ≅ isoRepresentative W j)) :
    i = j := by
  have he : Quotient.mk (isoSetoid W) i.out = Quotient.mk (isoSetoid W) j.out :=
    Quotient.sound h
  simpa only [Quotient.out_eq] using he

omit [Fintype G] in
lemma isoRepresentative_mk (W : Fin n → FDRep ℂ G) (i : Fin n) :
    Nonempty (W i ≅ isoRepresentative W (Quotient.mk (isoSetoid W) i)) := by
  have he : Quotient.mk (isoSetoid W) (Quotient.mk (isoSetoid W) i).out =
      Quotient.mk (isoSetoid W) i := Quotient.out_eq _
  obtain ⟨e⟩ := Quotient.exact he
  exact ⟨e.symm⟩

/-- Construct the actual finite semisimple skeleton from a proved finite
complete family and Maschke's actual biproduct decompositions. -/
def skeletonOfCompleteFamily (W : Fin n → FDRep ℂ G) (hs : ∀ i, Simple (W i))
    (hc : ∀ V : FDRep ℂ G, Simple V → ∃ i, Nonempty (V ≅ W i)) :
    FiniteSemisimpleSkeleton (FDRep ℂ G) (IsoLabels W) := by
  choose len Z hZ hdec using exists_simple_biproduct (G := G)
  choose idx hiso using fun (V : FDRep ℂ G) (a : Fin (len V)) => hc (Z V a) (hZ V a)
  exact {
    simpleObject := isoRepresentative W
    simple := fun i => hs i.out
    iso_injective := isoRepresentative_injective W
    length := len
    label := fun V a => Quotient.mk (isoSetoid W) (idx V a)
    decomposition := fun V => (Classical.choice (hdec V)) ≪≫
      biproduct.mapIso (fun a => (Classical.choice (hiso V a)) ≪≫
        Classical.choice (isoRepresentative_mk W (idx V a))) }

/-- Existence of a complete finite semisimple skeleton for the actual
category of finite-dimensional complex representations of a finite group. -/
theorem exists_finite_semisimple_skeleton :
    ∃ (ι : Type) (_ : Fintype ι), Nonempty (FiniteSemisimpleSkeleton (FDRep ℂ G) ι) := by
  obtain ⟨n, W, hs, hc⟩ := exists_finite_complete_simple_family (G := G)
  exact ⟨IsoLabels W, inferInstance, ⟨skeletonOfCompleteFamily W hs hc⟩⟩

end Paper18.Category.Representation

namespace Paper18.Category.Representation
variable (G : Type) [Group G] [Fintype G]

/-- A chosen finite type of labels for actual irreducible representations. -/
def SimpleIndex : Type := Classical.choose (exists_finite_semisimple_skeleton (G := G))

instance simpleIndexFintype : Fintype (SimpleIndex G) :=
  Classical.choose (Classical.choose_spec (exists_finite_semisimple_skeleton (G := G)))

/-- A canonical choice from the proved existence of the actual finite
semisimple representation skeleton. -/
def skeleton : FiniteSemisimpleSkeleton (FDRep ℂ G) (SimpleIndex G) :=
  Classical.choice (Classical.choose_spec
    (Classical.choose_spec (exists_finite_semisimple_skeleton (G := G))))

end Paper18.Category.Representation
