import Paper18.Category.TannakianC2GeneratorBasic
import Paper18.Category.SphericalizationKernelRepresentation
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Actual generation of a C₂ Tannakian center by its sign line -/
noncomputable section
set_option maxHeartbeats 800000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.Functor.Monoidal
open scoped BigOperators
universe v u
namespace Paper18.Category.RepresentationZ2

/-- The actual one-dimensional representation carried by a homogeneous basis vector. -/
def eigenLine (V : FDRep ℂ H) (i : EigenIndex V) : FDRep ℂ H :=
  actionOfInvolution (𝟙_ (FGModuleCat ℂ)) (eigenSign V i • 𝟙 _) (by
    cases i <;> simp [eigenSign])

/-- Homogeneous lines are actual copies of the unit or actual sign representation. -/
def eigenLineIso (V : FDRep ℂ H) (i : EigenIndex V) :
    eigenLine V i ≅ Sum.elim (fun _ => 𝟙_ (FDRep ℂ H)) (fun _ => signRep) i := by
  cases i with
  | inl a =>
      exact Action.mkIso (Iso.refl _) (fun g => by
        rcases eq_one_or_generator g with rfl | rfl <;>
          simp [eigenLine, eigenSign, actionOfInvolution])
  | inr a =>
      exact Action.mkIso (Iso.refl _) (fun g => by
        rcases eq_one_or_generator g with rfl | rfl <;>
          simp [eigenLine, eigenSign, signRep, actionOfInvolution])

def eigenInclusion (V : FDRep ℂ H) (i : EigenIndex V) : eigenLine V i ⟶ V where
  hom := FGModuleCat.ofHom (LinearMap.toSpanSingleton ℂ V (eigenVector V i))
  comm g := by
    rcases eq_one_or_generator g with rfl | rfl
    · simp
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      change ℂ at z
      change (eigenSign V i * z) • eigenVector V i =
        V.ρ generator (z • eigenVector V i)
      rw [map_smul, eigenVector_generator, smul_smul]
      rw [mul_comm]

def eigenProjection (V : FDRep ℂ H) (i : EigenIndex V) : V ⟶ eigenLine V i where
  hom := FGModuleCat.ofHom ((LinearMap.proj i).comp (eigenCoordinates V).toLinearMap)
  comm g := by
    rcases eq_one_or_generator g with rfl | rfl
    · simp
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      change eigenCoordinates V (V.ρ generator z) i =
        eigenSign V i * eigenCoordinates V z i
      exact eigenCoordinates_generator V z i

lemma eigenInclusion_projection_self (V : FDRep ℂ H) (i : EigenIndex V) :
    eigenInclusion V i ≫ eigenProjection V i = 𝟙 _ := by
  apply Action.hom_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change ℂ at z
  change eigenCoordinates V (z • eigenVector V i) i = z
  simp [eigenCoordinates_eigenVector, Pi.smul_apply]

lemma eigenInclusion_projection_ne (V : FDRep ℂ H) (i j : EigenIndex V) (hij : i ≠ j) :
    eigenInclusion V i ≫ eigenProjection V j = 0 := by
  apply Action.hom_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change ℂ at z
  change eigenCoordinates V (z • eigenVector V i) j = 0
  simp [eigenCoordinates_eigenVector, Pi.smul_apply, Ne.symm hij]

def eigenBicone (V : FDRep ℂ H) : Bicone (eigenLine V) where
  pt := V
  π := eigenProjection V
  ι := eigenInclusion V
  ι_π i j := by
    by_cases hij : i = j
    · subst j
      simp [eigenInclusion_projection_self]
    · simp [eigenInclusion_projection_ne V i j hij, hij]

lemma eigen_resolution (V : FDRep ℂ H) :
    (∑ i : EigenIndex V, eigenProjection V i ≫ eigenInclusion V i) = 𝟙 V := by
  apply Action.hom_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  let U : (V ⟶ V) →+ (V →ₗ[ℂ] V) :=
    { toFun := fun f => f.hom.hom
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change (U (∑ i : EigenIndex V, eigenProjection V i ≫ eigenInclusion V i)) v = v
  rw [map_sum]
  simp only [LinearMap.sum_apply]
  exact eigenVector_resolution V v

def eigenBiconeIsBilimit (V : FDRep ℂ H) : (eigenBicone V).IsBilimit :=
  isBilimitOfTotal (eigenBicone V) (eigen_resolution V)

/-- The actual finite eigenspace basis is an actual biproduct decomposition. -/
def eigenDecomposition (V : FDRep ℂ H) : (⨁ eigenLine V) ≅ V :=
  (biproduct.uniqueUpToIso _ (eigenBiconeIsBilimit V)).symm

/-- Every actual representation is an actual sum of trivial and sign lines. -/
def unitSignDecomposition (V : FDRep ℂ H) : V ≅
    ⨁ fun i : EigenIndex V =>
      Sum.elim (fun _ => 𝟙_ (FDRep ℂ H)) (fun _ => signRep) i :=
  (eigenDecomposition V).symm ≪≫ biproduct.mapIso (eigenLineIso V)

end Paper18.Category.RepresentationZ2

namespace Paper18.Category.TannakianCenter
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [HasFiniteBiproducts C]
  (T : TannakianCenter C RepresentationZ2.H)
open RepresentationZ2

/-- The actual Tannakian inclusion carries the explicit eigenspace decomposition
to an actual decomposition into the tensor unit and its canonical generator. -/
def c2RepresentationDecomposition (V : FDRep ℂ H) : T.inclusion.obj V ≅
    ⨁ fun i : EigenIndex V => Sum.elim (fun _ => 𝟙_ C) (fun _ => T.c2Generator) i :=
  T.inclusion.mapIso (unitSignDecomposition V) ≪≫
    T.inclusion.mapBiproduct _ ≪≫ biproduct.mapIso (fun i => by
      cases i with
      | inl a => exact (εIso T.inclusion).symm
      | inr a => exact Iso.refl _)

/-- Every transparent object is an actual finite direct sum of units and
copies of the distinguished sign generator. -/
theorem c2Generator_generates (X : C) (hX : X ∈ mugerCenter (C := C)) :
    ∃ m n : ℕ, Nonempty (X ≅
      ⨁ fun i : Fin m ⊕ Fin n => Sum.elim (fun _ => 𝟙_ C) (fun _ => T.c2Generator) i) := by
  obtain ⟨V, ⟨e⟩⟩ := T.exists_representation X hX
  exact ⟨Module.finrank ℂ (plusSpace V), Module.finrank ℂ (minusSpace V),
    ⟨e.symm ≪≫ T.c2RepresentationDecomposition V⟩⟩

/-- A transparent simple object is an actual unit or the actual canonical
generator. This follows from the genuine finite biproduct decomposition. -/
theorem c2Generator_simple_support (X : C) [Simple X]
    (hX : X ∈ mugerCenter (C := C)) :
    Nonempty (X ≅ 𝟙_ C) ∨ Nonempty (X ≅ T.c2Generator) := by
  obtain ⟨m, n, ⟨e⟩⟩ := T.c2Generator_generates X hX
  let Q : Fin m ⊕ Fin n → C := Sum.elim (fun _ => 𝟙_ C) (fun _ => T.c2Generator)
  change X ≅ ⨁ Q at e
  have hn : ∃ i, biproduct.ι Q i ≫ e.inv ≠ 0 := by
    by_contra h
    push_neg at h
    have hz : e.inv = 0 := by
      apply biproduct.hom_ext'
      intro i
      simpa using h i
    exact id_nonzero X (by rw [← e.hom_inv_id, hz, comp_zero])
  obtain ⟨i, hi⟩ := hn
  letI : IsIso (biproduct.ι Q i ≫ e.inv) := isIso_of_mono_of_nonzero hi
  cases i with
  | inl a => exact Or.inl ⟨(asIso (biproduct.ι Q (Sum.inl a) ≫ e.inv)).symm⟩
  | inr a => exact Or.inr ⟨(asIso (biproduct.ι Q (Sum.inr a) ≫ e.inv)).symm⟩

theorem c2Generator_simple_transparent_iff (X : C) [Simple X] :
    X ∈ mugerCenter (C := C) ↔
      Nonempty (X ≅ 𝟙_ C) ∨ Nonempty (X ≅ T.c2Generator) := by
  refine ⟨T.c2Generator_simple_support X, ?_⟩
  intro h Y _
  rcases h with h | h
  · exact (centralizes_unit_left Y).of_iso_left (Classical.choice h)
  · exact (T.c2Generator_centralizes Y).of_iso_left (Classical.choice h)

end Paper18.Category.TannakianCenter
