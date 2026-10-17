import Paper18.Category.PointedRelativeCenterObstructionKernelActionCoset

/-! # Actual nonzero induced objects in every nonempty quotient component -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
namespace Paper18.Category.PointedRelativeCenterObstruction
open FiniteCohomologyKilling
variable {Γ G : Type} [Group Γ] [Fintype Γ] [Group G]
  (p : Γ →* G) (ψ : ThreeCochain Γ ℂˣ) (ω : FourCocycle G ℂˣ)
  (hψ : ∀ a b c d, dThree ψ.val a b c d = ω.val (p a) (p b) (p c) (p d))

/-- An actual projective-equivariant object induced from the actual line
in any specified degree in a quotient coset. -/
def inducedCosetLine {g : G} (a : cosetSimpleIndex p g) :
    (kernelCosetAction p ψ ω hψ g).Equivariant :=
  (kernelCosetAction p ψ ω hψ g).induction ((cosetSkeleton p g).simpleObject a)

/-- The original line is an actual retract of the underlying induction,
so the induced equivariant object is actually nonzero. -/
lemma inducedCosetLine_not_isZero {g : G} (a : cosetSimpleIndex p g) :
    ¬ IsZero (inducedCosetLine p ψ ω hψ a) := by
  let A := kernelCosetAction p ψ ω hψ g
  let X := (cosetSkeleton p g).simpleObject a
  letI : Simple X := (cosetSkeleton p g).simple a
  intro hz
  have hz' : IsZero (A.induction X).obj := A.forget.map_isZero hz
  let r := A.inductionRetract X
  have hi : r.i = 0 := hz'.eq_of_tgt _ _
  apply CategoryTheory.id_nonzero X
  calc
    𝟙 X = r.i ≫ r.r := r.retract.symm
    _ = 0 := by rw [hi, zero_comp]

/-- Surjectivity of the actual quotient map constructs an actual nonzero
projective-equivariant object in every actual quotient degree. -/
def nonzeroCosetInduction (hp : Function.Surjective p) (g : G) :
    {X : (kernelCosetAction p ψ ω hψ g).Equivariant // ¬ IsZero X} :=
  ⟨inducedCosetLine p ψ ω hψ ⟨Classical.choose (hp g), Classical.choose_spec (hp g)⟩,
    inducedCosetLine_not_isZero p ψ ω hψ _⟩

end Paper18.Category.PointedRelativeCenterObstruction
