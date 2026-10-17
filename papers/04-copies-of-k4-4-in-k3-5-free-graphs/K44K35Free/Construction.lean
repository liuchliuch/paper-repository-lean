import K44K35Free.ProjectivePairing
import K44K35Free.Pruning
import K44K35Free.PreliminaryAlteration

/-! Concrete graph and alteration definitions on the quartic point set.
No geometric estimate or counting assertion is part of the data. -/
noncomputable section
namespace K44K35Free.Construction
open Geometry Finset
variable {F : Type*} [Field F] [Fintype F]

local instance constructionLocalInstance1 : Fintype (Plane F) := Fintype.ofFinite _

/-- The indexed exceptional planes, retaining multiplicity of block type. -/
abbrev BlockIndex (α : F) (c : Quartic F) :=
  Pruning.SectionBlockIndex (Exceptional α c)

local instance constructionLocalInstance2 (α : F) (c : Quartic F) : Fintype (BlockIndex α c) := Fintype.ofFinite _

/-- The exact incidence edge set (15). -/
def initialEdges (α : F) (c : Quartic F) (T : V F ≃ₗ[F] V F) : Finset (Param F × Param F) := by
  classical
  exact univ.filter fun e => Incidence α c T e.1 e.2

@[simp] theorem mem_initialEdges (α : F) (c : Quartic F) (T : V F ≃ₗ[F] V F)
    (p r : Param F) : (p,r) ∈ initialEdges α c T ↔ Incidence α c T p r := by
  classical
  simp [initialEdges]

/-- The blocks (19),(20), on their original vertex sets. -/
def actualBlocks (α : F) (c : Quartic F) (T : V F ≃ₗ[F] V F) :
    BlockIndex α c → Pruning.Block (Param F) :=
  Pruning.sectionBlock (planeSection α c) (leftDual T) (rightDual T)

/-- Mutuality is determined before any deletion. -/
def actualMutual (α : F) (c : Quartic F) (T : V F ≃ₗ[F] V F) :
    BlockIndex α c → Prop :=
  Pruning.sectionMutual (Exceptional α c) (leftDual T) (rightDual T)

/-- All sixteen edges of a plane pair's four-by-four copy. -/
def copyEdges (α : F) (c : Quartic F) (D : Plane F × Plane F) :
    Finset (Param F × Param F) := planeSection α c D.1 ×ˢ planeSection α c D.2

/-- A rich plane has exactly four points and belongs to neither exceptional family. -/
def Rich (α : F) (c : Quartic F) (E : Plane F) : Prop :=
  ¬ Exceptional α c E ∧ (planeSection α c E).card = 4

def richPlanes (α : F) (c : Quartic F) : Finset (Plane F) := by
  classical
  exact univ.filter (Rich α c)

@[simp] theorem mem_richPlanes (α : F) (c : Quartic F) (E : Plane F) :
    E ∈ richPlanes α c ↔ Rich α c E := by
  classical
  simp [richPlanes]

/-- Designated plane pairs (16); both sides are actual rich sections. -/
def designatedPairs (α : F) (c : Quartic F) (T : V F ≃ₗ[F] V F) :
    Finset (Plane F × Plane F) := by
  classical
  exact ((richPlanes α c) ×ˢ (richPlanes α c)).filter fun D => D.1 = leftDual T D.2

@[simp] theorem mem_designatedPairs (α : F) (c : Quartic F) (T : V F ≃ₗ[F] V F)
    (D : Plane F × Plane F) : D ∈ designatedPairs α c T ↔
      Rich α c D.1 ∧ Rich α c D.2 ∧ D.1 = leftDual T D.2 := by
  classical
  simp [designatedPairs, and_assoc]

/-- The two actual deletions, using indexed original blocks and original loads. -/
def preliminary (α : F) (c : Quartic F) (T : V F ≃ₗ[F] V F) (L : ℕ) :
    Finset (Param F × Param F) := by
  classical
  exact PreliminaryAlteration.preliminaryEdges (initialEdges α c T)
    (fun i => (actualBlocks α c T i).edges) (actualMutual α c T) L

/-- Designated copies whose sixteen edges all survived the preliminary alteration. -/
def preDesignated (α : F) (c : Quartic F) (T : V F ≃ₗ[F] V F) (L : ℕ) :
    Finset (Plane F × Plane F) := by
  classical
  exact (designatedPairs α c T).filter fun D => copyEdges α c D ⊆ preliminary α c T L

/-- A local choice function; only nonmutual active blocks impose choices. -/
abbrev Choices (α : F) (c : Quartic F) := BlockIndex α c → Param F → Finset (Param F)

def ValidChoices (α : F) (c : Quartic F) (T : V F ≃ₗ[F] V F) (R : Choices α c) : Prop :=
  ∀ i, ¬ actualMutual α c T i → Pruning.Active (actualBlocks α c T i) →
    ∀ y ∈ (actualBlocks α c T i).exceptional,
      R i y ⊆ (actualBlocks α c T i).controlled ∧ (R i y).card = 2

/-- The simultaneous local pruning from Section 4. -/
def prune (α : F) (c : Quartic F) (T : V F ≃ₗ[F] V F) (L : ℕ)
    (R : Choices α c) : Finset (Param F × Param F) :=
  Pruning.prunedEdges (preliminary α c T L) (actualBlocks α c T) (actualMutual α c T) R

def finalGraph (α : F) (c : Quartic F) (T : V F ≃ₗ[F] V F) (L : ℕ)
    (R : Choices α c) : SimpleGraph (Param F ⊕ Param F) :=
  Pruning.bipartiteGraph (prune α c T L R)

def survivingPairs (α : F) (c : Quartic F) (T : V F ≃ₗ[F] V F) (L : ℕ)
    (R : Choices α c) : Finset (Plane F × Plane F) := by
  classical
  exact (preDesignated α c T L).filter fun D => copyEdges α c D ⊆ prune α c T L R

@[simp] theorem finalGraph_card (α : F) (c : Quartic F) :
    Fintype.card (Param F ⊕ Param F) = 2 * (Fintype.card F) ^ 3 := by
  simp [Param, Fintype.card_fun, two_mul]

end K44K35Free.Construction
