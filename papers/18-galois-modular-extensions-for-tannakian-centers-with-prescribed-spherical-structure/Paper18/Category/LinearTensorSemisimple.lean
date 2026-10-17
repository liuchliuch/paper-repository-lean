import Paper18.Category.LinearTensorSemisimpleCoordinates
import Paper18.Category.SemisimpleAbelian

/-!
# Actual finite semisimplicity of the linear tensor product

The Hom-coordinate equivalence transports componentwise equalizers, giving
actual kernels. Pair objects are proved simple using their one-dimensional
endomorphism spaces and actual splittings. Their actual finite presentations
then form a complete finite semisimple skeleton.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Limits
universe v u w v' u' w' z
namespace Paper18.Category

/-- Equalizers of families of finite-dimensional vector spaces are formed
componentwise, with their actual universal property. -/
def gradedFiniteVectorHasEqualizers (α : Type w) :
    HasEqualizers (GradedObject α (FGModuleCat.{z} ℂ)) := by
  refine @hasEqualizers_of_hasLimit_parallelPair _ _ ?_
  intro X Y f g
  let E : GradedObject α (FGModuleCat.{z} ℂ) := fun p => equalizer (f p) (g p)
  let e : E ⟶ X := fun p => equalizer.ι (f p) (g p)
  have he : e ≫ f = e ≫ g := by
    funext p
    exact equalizer.condition (f p) (g p)
  exact HasLimit.mk
    { cone := Fork.ofι e he
      isLimit := Fork.IsLimit.mk _
        (fun s p => equalizer.lift (s.ι p) (congrFun s.condition p))
        (fun s => by
          funext p
          exact equalizer.lift_ι (s.ι p) (congrFun s.condition p))
        (fun s m hm => by
          funext p
          apply (cancel_mono (equalizer.ι (f p) (g p))).mp
          exact (congrFun hm p).trans (equalizer.lift_ι (s.ι p) (congrFun s.condition p)).symm) }

namespace DeligneProduct
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)

/-- Actual kernels are transported through the proved Hom-coordinate equivalence. -/
def hasKernels : HasKernels (DeligneProduct C D) := by
  letI := gradedFiniteVectorHasEqualizers.{max w w', max v v'} (ι × κ)
  letI : HasEqualizers (DeligneProduct C D) :=
    Adjunction.hasLimitsOfShape_of_equivalence (coordinates S T)
  infer_instance

/-- Actual monomorphisms split, by representing linear left inverses of all
pair Hom maps. -/
def splitMono {X Y : DeligneProduct C D} (f : X ⟶ Y) [Mono f] : SplitMono f := by
  let L (p : ι × κ) := CategoryTheory.Linear.rightComp ℂ (pairObject S T p.1 p.2) f
  have hinj (p : ι × κ) : Function.Injective (L p) := by
    intro a b h
    exact (cancel_mono f).mp h
  let φ : ∀ p : ι × κ, (pairObject S T p.1 p.2 ⟶ Y) →ₗ[ℂ]
      (pairObject S T p.1 p.2 ⟶ X) := fun p =>
    Classical.choose ((L p).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr (hinj p)))
  have hφ (p : ι × κ) (g : pairObject S T p.1 p.2 ⟶ X) : φ p (g ≫ f) = g :=
    LinearMap.congr_fun (Classical.choose_spec
      ((L p).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr (hinj p)))) g
  refine ⟨homFromPairFamily S T φ, ?_⟩
  apply hom_ext_pairs S T
  intro p g
  rw [← Category.assoc, comp_homFromPairFamily, Category.comp_id, hφ]

/-- The embedded pair of two actual simples is an actual simple object. -/
instance pairObject_simple (i : ι) (j : κ) : Simple (pairObject S T i j) where
  mono_isIso_iff_nonzero {X} f _ := by
    constructor
    · intro hf hz
      letI := hf
      exact pair_id_ne_zero S T (i, j) (by
        have h := IsIso.inv_hom_id f
        simpa [hz] using h.symm)
    · intro hf
      let s := splitMono S T f
      obtain ⟨c, hc⟩ := pair_end_eq_smul S T (i, j) (s.retraction ≫ f)
      have hcf : c • f = f := by
        calc
          c • f = f ≫ (c • 𝟙 (pairObject S T i j)) := by simp
          _ = f ≫ s.retraction ≫ f := by rw [hc]
          _ = f := by rw [← Category.assoc, s.id, Category.id_comp]
      have hc1 : c = 1 := (smul_left_injective ℂ hf) (hcf.trans (one_smul ℂ f).symm)
      exact ⟨⟨s.retraction, s.id, by rw [← hc, hc1, one_smul]⟩⟩

/-- Different pair labels cannot be isomorphic, by Hom orthogonality. -/
theorem pairObject_iso_injective (p q : ι × κ)
    (h : Nonempty (pairObject S T p.1 p.2 ≅ pairObject S T q.1 q.2)) : p = q := by
  obtain ⟨e⟩ := h
  by_contra hpq
  have he := pair_hom_eq_zero S T hpq e.hom
  exact pair_id_ne_zero S T p (by simpa [he] using e.hom_inv_id.symm)

/-- The complete finite semisimple skeleton of the actual Deligne product. -/
def skeleton : FiniteSemisimpleSkeleton (DeligneProduct C D) (ι × κ) where
  simpleObject p := pairObject S T p.1 p.2
  simple p := pairObject_simple S T p.1 p.2
  iso_injective := pairObject_iso_injective S T
  length M := Fintype.card (PresentationIndex S T M)
  label M a := presentationLabel S T M ((Fintype.equivFin (PresentationIndex S T M)).symm a)
  decomposition := finitePresentationIso S T

/-- Abelian structure is a consequence of the constructed kernels and the
actual finite semisimple skeleton. -/
def abelian : Abelian (DeligneProduct C D) := by
  letI := hasKernels S T
  exact (skeleton S T).abelian

end DeligneProduct
end Paper18.Category
