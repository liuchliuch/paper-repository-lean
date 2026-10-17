import Paper18.Category.RepresentationZ2Action
import Paper18.Category.TannakianBasic
import Paper18.Category.InvertibleFunctor

/-! # The actual sign representation and its Tannakian image -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open CategoryTheory.Functor.Monoidal
universe v u
namespace Paper18.Category.RepresentationZ2

/-- The actual one-dimensional representation on which the generator acts by `-1`. -/
def signRep : FDRep ℂ H :=
  actionOfInvolution (𝟙_ (FGModuleCat ℂ)) (-𝟙 _) (by simp)

@[simp] lemma signRep_generator : signRep.ρ generator = -LinearMap.id := by
  change (actionOfInvolution _ _ _).ρ generator = _
  rw [actionOfInvolution_generator]
  rfl

/-- The product of two actual sign representations is the trivial line. -/
def signSquareIso : signRep ⊗ signRep ≅ 𝟙_ (FDRep ℂ H) :=
  Action.mkIso (λ_ (𝟙_ (FGModuleCat ℂ))) (fun g => by
    rcases eq_one_or_generator g with rfl | rfl
    · simp
    · change ((-𝟙 _) ⊗ₘ (-𝟙 _)) ≫ (λ_ (𝟙_ (FGModuleCat ℂ))).hom =
        (λ_ (𝟙_ (FGModuleCat ℂ))).hom ≫ 𝟙 _
      have ht : (-𝟙 (𝟙_ (FGModuleCat ℂ))) ⊗ₘ (-𝟙 (𝟙_ (FGModuleCat ℂ))) =
          𝟙 ((𝟙_ (FGModuleCat ℂ)) ⊗ (𝟙_ (FGModuleCat ℂ))) := by
        apply ModuleCat.hom_ext
        apply TensorProduct.ext
        apply LinearMap.ext
        intro x
        apply LinearMap.ext
        intro y
        change (-x) ⊗ₜ[ℂ] (-y) = x ⊗ₜ[ℂ] y
        rw [TensorProduct.neg_tmul, TensorProduct.tmul_neg, neg_neg]
      rw [ht, id_comp, comp_id])

/-- Actual two-sided tensor inverse data, with the sign line itself as inverse. -/
def signTensorInverse : TensorInverse signRep where
  inverse := signRep
  left := signSquareIso
  right := signSquareIso

/-- The self-braiding on the sign line is the ordinary vector-space symmetry. -/
lemma sign_selfBraiding : (β_ signRep signRep).hom = 𝟙 _ := by
  apply Action.hom_ext
  change (β_ (𝟙_ (FGModuleCat ℂ)) (𝟙_ (FGModuleCat ℂ))).hom = 𝟙 _
  rw [braiding_tensorUnit_left, unitors_equal, Iso.hom_inv_id]

/-- The actual sign representation is not isomorphic to the trivial representation. -/
lemma sign_nonunit : ¬ Nonempty (signRep ≅ 𝟙_ (FDRep ℂ H)) := by
  rintro ⟨e⟩
  have h := e.hom.comm generator
  have hz : e.hom.hom = 0 := by
    have heq : -e.hom.hom = e.hom.hom := by
      simpa [signRep, actionOfInvolution] using h
    have htwo : (2 : ℂ) • e.hom.hom = 0 := by
      rw [two_smul]
      calc
        e.hom.hom + e.hom.hom = -e.hom.hom + e.hom.hom :=
          congrArg (fun f => f + e.hom.hom) heq.symm
        _ = 0 := neg_add_cancel _
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  have hid : (𝟙 signRep : signRep ⟶ signRep) = 0 := by
    rw [← e.hom_inv_id]
    apply Action.hom_ext
    change e.hom.hom ≫ e.inv.hom = 0
    rw [hz, zero_comp]
  have hlin := congrArg (fun f : signRep ⟶ signRep => f.hom.hom (1 : ℂ)) hid
  norm_num [signRep, actionOfInvolution] at hlin

end Paper18.Category.RepresentationZ2

namespace Paper18.Category.TannakianCenter
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] (T : TannakianCenter C RepresentationZ2.H)

/-- The canonical nontrivial transparent generator specified by an actual C₂ center. -/
def c2Generator : C := T.inclusion.obj RepresentationZ2.signRep

def c2GeneratorTensorInverse : TensorInverse T.c2Generator :=
  RepresentationZ2.signTensorInverse.map T.inclusion

def c2GeneratorSquareIso : T.c2Generator ⊗ T.c2Generator ≅ 𝟙_ C :=
  TensorInverse.mapSquare T.inclusion RepresentationZ2.signSquareIso

lemma c2Generator_transparent : T.c2Generator ∈ mugerCenter (C := C) :=
  T.transparent RepresentationZ2.signRep

lemma c2Generator_centralizes (X : C) : Centralizes T.c2Generator X :=
  T.centralizes RepresentationZ2.signRep X

lemma c2Generator_nonunit : ¬ Nonempty (T.c2Generator ≅ 𝟙_ C) := by
  rintro ⟨e⟩
  exact RepresentationZ2.sign_nonunit
    ⟨T.inclusion.preimageIso (e ≪≫ εIso T.inclusion)⟩

lemma c2Generator_selfBraiding : (β_ T.c2Generator T.c2Generator).hom = 𝟙 _ := by
  apply (cancel_mono (μIso T.inclusion RepresentationZ2.signRep
    RepresentationZ2.signRep).hom).mp
  change (β_ (T.inclusion.obj RepresentationZ2.signRep)
    (T.inclusion.obj RepresentationZ2.signRep)).hom ≫
      Functor.LaxMonoidal.μ T.inclusion _ _ = 𝟙 _ ≫ Functor.LaxMonoidal.μ T.inclusion _ _
  rw [← Functor.LaxBraided.braided]
  simp [RepresentationZ2.sign_selfBraiding]

end Paper18.Category.TannakianCenter
