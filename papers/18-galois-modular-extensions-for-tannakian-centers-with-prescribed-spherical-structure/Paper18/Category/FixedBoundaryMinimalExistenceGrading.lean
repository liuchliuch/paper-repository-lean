import Paper18.Category.CrossedBraidedGauging
import Paper18.Category.SignKernelDimensions

/-! # Actual faithful C₂ gradings have index two

Degrees of simples and the sign fusion law are derived from the actual
projectors and actual tensor/retract diagrams. No numerical grading is
supplied as an independent certificate.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open Paper18.Category.CrossedBraidedGauging
universe v u w t
namespace Paper18.Category.FixedBoundary.MinimalExistence
variable {G : Type w} [Group G] [Fintype G]
  {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasKernels C] [HasFiniteBiproducts C]
  (P : Grading G C)

/-- A genuine simple lies in one genuine degree, detected by a nonzero
actual split projector. -/
theorem simple_homogeneous (X : C) [Simple X] : ∃ g : G, P.Homogeneous g X := by
  have hp : ∃ g : G, (P.projection g).app X ≠ 0 := by
    by_contra hn
    push_neg at hn
    have ht := P.total X
    simp only [hn, Finset.sum_const_zero] at ht
    exact CategoryTheory.id_nonzero X ht.symm
  obtain ⟨g, hg⟩ := hp
  have hi : P.componentInclusion g X ≠ 0 := by
    intro hz
    have he := P.componentProjection_inclusion g X
    rw [hz, comp_zero] at he
    exact hg he.symm
  letI : IsIso (P.componentInclusion g X) := isIso_of_mono_of_nonzero hi
  exact ⟨g, P.homogeneous_iso (asIso (P.componentInclusion g X)).symm
    (P.component_homogeneous g X)⟩

theorem homogeneous_simple_unique (X : C) [Simple X] {g h : G}
    (hg : P.Homogeneous g X) (hh : P.Homogeneous h X) : g = h := by
  by_contra hn
  exact CategoryTheory.id_nonzero X (P.homogeneous_hom_zero hn hg hh (𝟙 X))

section Fusion
variable [Linear ℂ C] [MonoidalLinear ℂ C] [RightRigidCategory C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type t} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

def simpleDegree (i : ι) : G := Classical.choose (simple_homogeneous P (S.simpleObject i))

theorem simpleDegree_homogeneous (i : ι) :
    P.Homogeneous (simpleDegree P S i) (S.simpleObject i) :=
  Classical.choose_spec (simple_homogeneous P (S.simpleObject i))

theorem simpleDegree_eq {g : G} (i : ι) (h : P.Homogeneous g (S.simpleObject i)) :
    simpleDegree P S i = g :=
  homogeneous_simple_unique P _ (simpleDegree_homogeneous P S i) h

theorem simpleDegree_tensor (i j k : ι) (h : 0 < S.fusionBasis.N i j k) :
    simpleDegree P S k = simpleDegree P S i * simpleDegree P S j := by
  apply simpleDegree_eq P S k
  apply P.homogeneous_retract
    (S.retractOfMultiplicityPos (S.simpleObject i ⊗ S.simpleObject j) k h)
  exact P.homogeneous_tensor (simpleDegree_homogeneous P S i)
    (simpleDegree_homogeneous P S j)

end Fusion

abbrev C2 := Multiplicative (ZMod 2)
def nonidentity : C2 := Multiplicative.ofAdd 1

theorem c2_cases (g : C2) : g = 1 ∨ g = nonidentity := by
  rcases Paper18.ZMod.two_eq_zero_or_one (Multiplicative.toAdd g) with h | h
  · exact Or.inl (congrArg Multiplicative.ofAdd h)
  · exact Or.inr (congrArg Multiplicative.ofAdd h)

def sign (g : C2) : ℝ := if g = 1 then 1 else -1

theorem sign_mul (g h : C2) : sign (g * h) = sign g * sign h := by
  have hs : nonidentity ≠ (1 : C2) := by decide
  have hss : nonidentity * nonidentity = (1 : C2) := by decide
  rcases c2_cases g with rfl | rfl <;> rcases c2_cases h with rfl | rfl <;>
    simp [sign, hs, hss]

section C2Fusion
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  (Q : Grading C2 C) {κ : Type t} [Fintype κ] (T : FiniteSemisimpleSkeleton C κ)

theorem sign_eq_one_iff (i : κ) :
    sign (simpleDegree Q T i) = 1 ↔ neutralProperty Q (T.simpleObject i) := by
  rw [neutralProperty]
  constructor
  · intro h
    have he : simpleDegree Q T i = 1 := by
      by_contra hn
      simp [sign, hn] at h
      norm_num at h
    simpa only [he] using simpleDegree_homogeneous Q T i
  · intro h
    rw [simpleDegree_eq Q T i h]
    simp [sign]

include T in
/-- Faithfulness is witnessed by an actual nonzero negative component,
and forces the actual neutral support to have half the total FP mass. -/
theorem totalFPdim_eq_twice_neutral (hf : Q.Faithful) :
    T.fusionBasis.totalFPdim = 2 * T.supportFPdim (neutralProperty Q) := by
  obtain ⟨X, hX, hnX⟩ := hf nonidentity
  have hlen : 0 < T.length X := GraphPicard.length_pos_of_id_ne_zero T X
    (fun hz => hnX ((IsZero.iff_id_eq_zero X).mpr hz))
  let a : Fin (T.length X) := ⟨0, hlen⟩
  have ha : Q.Homogeneous nonidentity (T.simpleObject (T.label X a)) := by
    apply Q.homogeneous_retract
      { i := T.coendInclusion X a
        r := T.coendProjection X a
        retract := by simp [FiniteSemisimpleSkeleton.coendInclusion,
          FiniteSemisimpleSkeleton.coendProjection, Category.assoc] } hX
  have hs : sign (simpleDegree Q T (T.label X a)) = -1 := by
    rw [simpleDegree_eq Q T _ ha]
    simp [sign, nonidentity]
  have he := T.fusionBasis.totalFPdim_eq_twice_sign_kernel
    (fun i => sign (simpleDegree Q T i))
    (fun i => by by_cases h : simpleDegree Q T i = 1 <;> simp [sign, h])
    (fun i j k h => by
      change sign (simpleDegree Q T k) = sign (simpleDegree Q T i) * sign (simpleDegree Q T j)
      rw [simpleDegree_tensor Q T i j k h, sign_mul])
    (T.label X a) hs
  simpa only [FiniteSemisimpleSkeleton.supportFPdim, sign_eq_one_iff Q T] using he

end C2Fusion
end Paper18.Category.FixedBoundary.MinimalExistence
