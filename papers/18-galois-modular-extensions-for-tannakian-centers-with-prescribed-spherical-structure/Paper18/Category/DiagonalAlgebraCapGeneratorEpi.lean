import Paper18.Category.DiagonalAlgebraCapGenerator

/-! # Actual cap generators detect epimorphisms onto the canonical diagonal

Actual Schur Hom dimensions show that the cap generators span all maps
from actual simple pairs. Rigid retract compatibility then reduces epiness
to the images of any actual retract-dominant functor.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w v' u'
namespace Paper18.Category.DiagonalAlgebra
attribute [local instance 2000] RightRigidCategory.rightDual
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)

/-- The actual simple-pair identification with the actual dual cap pair. -/
def capSimplePairIso (j : ι) :
    DeligneProduct.pairObject S S (S.dualLabel j) j ≅
      DeligneProduct.externalObject (dual D (S.simpleObject j)) (S.simpleObject j) :=
  (Mat_.embedding (LinearTensor D D)).mapIso
    (LinearTensor.isoOfPair (S.dualIso j) (Iso.refl _))

/-- Factoring every actual cap generator through a given map proves its
actual epimorphy. The proof uses actual simple Hom spaces, not assumed
coend or separability properties. -/
theorem epi_of_capGenerators {Q : DeligneProduct D D} (q : Q ⟶ canonicalAlgebra S)
    (hcap : ∀ X : D, ∃ g : DeligneProduct.externalObject (dual D X) X ⟶ Q,
      g ≫ q = capGenerator S X) : Epi q where
  left_cancellation := by
    intro Z f g hfg
    letI := DeligneProduct.hasKernels S S
    apply (DeligneProduct.skeleton S S).hom_ext_simples
    rintro ⟨i,j⟩ t
    by_cases hij : i = S.dualLabel j
    · subst i
      let b := (capSimplePairIso S j).hom ≫ capGenerator S (S.simpleObject j)
      have hb : b ≠ 0 := by
        intro hz
        apply capGenerator_ne_zero S (S.simpleObject j)
        apply (cancel_epi (capSimplePairIso S j).hom).mp
        simpa only [b, comp_zero] using hz
      have hd : Module.finrank ℂ
          (DeligneProduct.pairObject S S (S.dualLabel j) j ⟶ canonicalAlgebra S) = 1 := by
        rw [canonicalAlgebra_multiplicity, if_pos rfl]
      obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hd hb t
      have hbfg : b ≫ f = b ≫ g := by
        obtain ⟨a, ha⟩ := hcap (S.simpleObject j)
        dsimp only [b]
        rw [← ha]
        simp only [assoc]
        rw [hfg]
      rw [← hc]
      simpa only [Linear.smul_comp] using congrArg (fun k => c • k) hbfg
    · have hd : Module.finrank ℂ
          (DeligneProduct.pairObject S S i j ⟶ canonicalAlgebra S) = 0 := by
        rw [canonicalAlgebra_multiplicity, if_neg hij]
      have ht : t = 0 := (Module.finrank_zero_iff.mp hd).elim _ _
      rw [ht]
      simp

/-- Actual retract dominance reduces cap-generation to the actual source
images. The retract is transported through the actual dual evaluation. -/
theorem epi_of_image_capGenerators {C : Type u'} [Category.{v'} C] (F : C ⥤ D)
    (hdom : ∀ Y : D, ∃ X : C, Nonempty (Retract Y (F.obj X)))
    {Q : DeligneProduct D D} (q : Q ⟶ canonicalAlgebra S)
    (hcap : ∀ X : C, ∃ g : DeligneProduct.externalObject (dual D (F.obj X)) (F.obj X) ⟶ Q,
      g ≫ q = capGenerator S (F.obj X)) : Epi q := by
  apply epi_of_capGenerators S q
  intro Y
  obtain ⟨X, ⟨r⟩⟩ := hdom Y
  obtain ⟨g, hg⟩ := hcap X
  refine ⟨capPairMap (dualMap D r.r) r.i ≫ g, ?_⟩
  rw [assoc, hg, capGenerator_retract]

end Paper18.Category.DiagonalAlgebra
