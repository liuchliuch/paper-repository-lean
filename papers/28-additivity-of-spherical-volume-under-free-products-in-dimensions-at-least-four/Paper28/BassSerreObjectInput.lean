import Paper28.TreeBranches
import Mathlib.GroupTheory.GroupAction.Quotient

/-! The standard Bass--Serre object for a free product of two subgroups.
The graph is the actual coset graph: vertices G/A disjoint union G/B and
edge g joins gA to gB. Only its standard tree/incidence structure is an
external input (Serre, Trees, I.4.1, Theorems 6--7). No shadow, current,
transfer, boundary, mass or spherical-volume conclusion is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open SimpleGraph
open scoped Classical
variable {G : Type} [Group G] (A B : Subgroup G)

/-- The categorical free-product property, on the actual subgroup maps. -/
structure IsFreeProductOfSubgroups : Prop where
  universal : ∀ (D : Type) [Group D] (fA : A →* D) (fB : B →* D),
    ∃! f : G →* D, (∀ a : A, f a.val = fA a) ∧ (∀ b : B, f b.val = fB b)

abbrev BassSerreVertex := (G ⧸ A) ⊕ (G ⧸ B)

def bassSerreLeft (g : G) : BassSerreVertex A B := Sum.inl (QuotientGroup.mk g)
def bassSerreRight (g : G) : BassSerreVertex A B := Sum.inr (QuotientGroup.mk g)

def bassSerreAdj : BassSerreVertex A B → BassSerreVertex A B → Prop
  | .inl a,.inr b => ∃ g : G, QuotientGroup.mk g = a ∧ QuotientGroup.mk g = b
  | .inr b,.inl a => ∃ g : G, QuotientGroup.mk g = a ∧ QuotientGroup.mk g = b
  | _,_ => False

def bassSerreGraph : SimpleGraph (BassSerreVertex A B) where
  Adj := bassSerreAdj A B
  symm := by intro v w; cases v <;> cases w <;> exact id
  loopless := by intro v; cases v <;> exact id

def bassSerreEdge (g : G) : (bassSerreGraph A B).edgeSet :=
  ⟨s(bassSerreLeft A B g,bassSerreRight A B g),⟨g,rfl,rfl⟩⟩

/-- Exact incidence labels, with the chosen coset representative explicit. -/
structure BassSerreObject where
  isTree : (bassSerreGraph A B).IsTree
  edge_bijective : Function.Bijective (bassSerreEdge A B)
  leftLabel : ∀ v : G ⧸ A, A ≃ (bassSerreGraph A B).neighborSet (Sum.inl v)
  leftLabel_formula : ∀ v (a : A), (leftLabel v a).val = bassSerreRight A B (v.out*a.val)
  rightLabel : ∀ v : G ⧸ B, B ≃ (bassSerreGraph A B).neighborSet (Sum.inr v)
  rightLabel_formula : ∀ v (b : B), (rightLabel v b).val = bassSerreLeft A B (v.out*b.val)

structure BassSerreStructureInput : Prop where
  realization : ∀ {G : Type} [Group G] (A B : Subgroup G),
    IsFreeProductOfSubgroups A B → Nonempty (BassSerreObject A B)

variable {A B}

def bassSerreEdgeEquiv (T : BassSerreObject A B) : G ≃ (bassSerreGraph A B).edgeSet :=
  Equiv.ofBijective _ T.edge_bijective

def bassSerreBranchA (T : BassSerreObject A B) (v : G ⧸ A) (g : G) : A :=
  (T.leftLabel v).symm (treeBranch (bassSerreGraph A B) T.isTree (.inl v) (bassSerreEdge A B g))

def bassSerreBranchB (T : BassSerreObject A B) (v : G ⧸ B) (g : G) : B :=
  (T.rightLabel v).symm (treeBranch (bassSerreGraph A B) T.isTree (.inr v) (bassSerreEdge A B g))

theorem bassSerreBranchA_incident (T : BassSerreObject A B) (v : G ⧸ A) (a : A) :
    bassSerreBranchA T v (v.out*a.val) = a := by
  apply (T.leftLabel v).injective
  rw [bassSerreBranchA,Equiv.apply_symm_apply]
  apply Subtype.ext
  have hq : QuotientGroup.mk (v.out*a.val) = v := by
    calc
      _ = (QuotientGroup.mk v.out : G ⧸ A) := Quotient.sound (QuotientGroup.leftRel_apply.mpr (by simp))
      _ = v := QuotientGroup.out_eq' v
  have ha : (bassSerreGraph A B).Adj (Sum.inl v) (bassSerreRight A B (v.out*a.val)) :=
    ⟨v.out*a.val,hq,rfl⟩
  have he : bassSerreEdge A B (v.out*a.val) =
      ⟨s(Sum.inl v,bassSerreRight A B (v.out*a.val)),ha⟩ := by
    apply Subtype.ext
    change s(Sum.inl (QuotientGroup.mk (v.out*a.val)),_) = _
    rw [hq]
  rw [he,treeBranch_incident,T.leftLabel_formula]

end Paper28
