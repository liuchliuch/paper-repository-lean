import Paper13.LieDim
import Paper13.InvariantBlocks
import Paper13.GraphGk
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Matrix.Reindex
noncomputable section
namespace Paper13
open Matrix
open scoped BigOperators Kronecker

/-- Each undirected edge is included once, with the smaller endpoint first. -/
def graphEdges {n : ℕ} (G : SimpleGraph (Fin n)) : Finset (Fin n × Fin n) := by
  classical
  exact Finset.univ.filter (fun e => e.1 < e.2 ∧ G.Adj e.1 e.2)

def graphCost {n : ℕ} (G : SimpleGraph (Fin n)) : Op n := ∑ e ∈ graphEdges G, ZZ e.1 e.2

def graphStd {n : ℕ} (G : SimpleGraph (Fin n)) : Submodule ℝ (Op n) := gStd (HXFull n) (graphCost G)
def graphMa {n : ℕ} (G : SimpleGraph (Fin n)) : Submodule ℝ (Op n) := gMa (graphEdges G)

/-- Permuting the qubit coordinates in the computational basis. -/
def permuteState {n : ℕ} (φ : Equiv.Perm (Fin n)) (x : QubitBasis n) : QubitBasis n := x ∘ φ

/-- Operators fixed by all graph automorphisms, as an actual real subspace. -/
def graphFixed {n : ℕ} (G : SimpleGraph (Fin n)) : Submodule ℝ (Op n) where
  carrier := {A | ∀ (φ : G ≃g G) (x y : QubitBasis n),
    A (x ∘ φ) (y ∘ φ) = A x y}
  zero_mem' := by intro φ x y; rfl
  add_mem' := by intro A B hA hB φ x y; change A _ _ + B _ _ = A x y + B x y; rw [hA,hB]
  smul_mem' := by intro r A hA φ x y; change r • A _ _ = r • A x y; rw [hA]

/-- The natural symmetry bound is the fixed subspace of the actual multi-angle Lie algebra. -/
def graphNat {n : ℕ} (G : SimpleGraph (Fin n)) : Submodule ℝ (Op n) := graphMa G ⊓ graphFixed G

lemma graphNat_eq_ma_of_rigid {n : ℕ} (G : SimpleGraph (Fin n))
    (hrigid : ∀ φ : G ≃g G, φ = SimpleGraph.Iso.refl) : graphNat G = graphMa G := by
  apply inf_eq_left.mpr
  intro A hA φ x y
  rw [hrigid φ]
  rfl

/-- The +1 global-bit-flip space. -/
def plusSpace (n : ℕ) : Submodule ℂ (QubitBasis n → ℂ) :=
  LinearMap.ker (Matrix.toLin' (bitFlip n) - LinearMap.id)

/-- Irreducible dimensions in the positive-parity sector of the actual standard algebra. -/
def irrepDimensions {n : ℕ} (G : SimpleGraph (Fin n)) : Set ℕ :=
  {d | ∃ W : Submodule ℂ (QubitBasis n → ℂ), W ≤ plusSpace n ∧
    IrreducibleOn (graphStd G : Set (Op n)) W ∧ Module.finrank ℂ W = d}

def largestIrrep {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := sSup (irrepDimensions G)
def invariantDeficit {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := 2^(n-1) - largestIrrep G

/-- The same assembled graph, relabelled to a finite ordinal for its qubit operators. -/
def GkOrdinal (k : ℕ) : SimpleGraph (Fin (k*7)) := (Gk k).comap finProdFinEquiv.symm

/-- Relabelling is an actual graph isomorphism. -/
def GkOrdinalIso (k : ℕ) : GkOrdinal k ≃g Gk k where
  toEquiv := finProdFinEquiv.symm
  map_rel_iff' := Iff.rfl

lemma GkOrdinal_rigid (k : ℕ) (hk : 7 ≤ k) :
    ∀ φ : GkOrdinal k ≃g GkOrdinal k, φ = SimpleGraph.Iso.refl := by
  intro φ
  let e := GkOrdinalIso k
  have hi := Gk_aut_trivial k hk (e.symm.trans (φ.trans e))
  apply RelIso.ext
  intro v
  have hv := congrArg (fun f : Gk k ≃g Gk k => f (e v)) hi
  change e (φ (e.symm (e v))) = e v at hv
  rw [e.symm_apply_apply] at hv
  exact e.injective hv

lemma GkOrdinal_nat_eq_ma (k : ℕ) (hk : 7 ≤ k) :
    graphNat (GkOrdinal k) = graphMa (GkOrdinal k) :=
  graphNat_eq_ma_of_rigid _ (GkOrdinal_rigid k hk)

/-- Shared Hamiltonians are sums of independently controlled multi-angle generators. -/
lemma graphStd_le_ma {n : ℕ} (G : SimpleGraph (Fin n)) : graphStd G ≤ graphMa G := by
  apply lieClosure_le
  · intro A hA
    rcases mem_stdGens_iff.mp hA with rfl | rfl
    · change Complex.I • (∑ v : Fin n, Xv v) ∈ graphMa G
      rw [Finset.smul_sum]
      apply Submodule.sum_mem
      intro v hv
      apply subset_lieClosure
      exact Or.inl ⟨v,rfl⟩
    · change Complex.I • (∑ e ∈ graphEdges G, ZZ e.1 e.2) ∈ graphMa G
      rw [Finset.smul_sum]
      apply Submodule.sum_mem
      intro e he
      apply subset_lieClosure
      exact Or.inr ⟨e, he, rfl⟩
  · exact isLieSub_lieClosure _

lemma graphStd_le_nat_rigid {n : ℕ} (G : SimpleGraph (Fin n))
    (h : ∀ φ : G ≃g G, φ = SimpleGraph.Iso.refl) : graphStd G ≤ graphNat G := by
  rw [graphNat_eq_ma_of_rigid G h]
  exact graphStd_le_ma G

/-- Genuine operator assertions of Theorem 1, proved in NaturalDimension. -/
def Theorem1AlgebraClaim (k : ℕ) : Prop :=
  Module.finrank ℝ (graphStd (GkOrdinal k)) ≤ 15880^k / 2 - 1 ∧
  Module.finrank ℝ (graphNat (GkOrdinal k)) = 2^(14*k-1)-2

/-- Genuine irrep and deficit assertions of Corollary 2, proved in InvariantGap. -/
def Corollary2Claim (k : ℕ) : Prop :=
  largestIrrep (GkOrdinal k) ≤ 126^k / 2 ∧
  (128^k - 126^k) / 2 ≤ invariantDeficit (GkOrdinal k)
/-- Original hypotheses of Proposition 5, with h remaining non-port qubits.
The gadget has h+1 vertices. No dimension-bound conclusion is a field. -/
structure PortedGadget (h : ℕ) where
  graph : SimpleGraph (Fin (h+1))
  port : Fin (h+1)
  projector : Op (h+1)
  remainingProjector : Op h
  orthogonal : IsOrthProj projector
  port_factor : Matrix.reindexAlgEquiv ℂ ℂ (Fin.insertNthEquiv (fun _ : Fin (h+1) => Fin 2) port).symm projector =
    (1 : Op1) ⊗ₖ remainingProjector
  rank_pos : 0 < Module.finrank ℂ (LinearMap.range (Matrix.toLin' projector))
  rank_lt : Module.finrank ℂ (LinearMap.range (Matrix.toLin' projector)) < 2^(h+1)
  comm_mixer : projector * HXFull (h+1) = HXFull (h+1) * projector
  comm_cost : projector * graphCost graph = graphCost graph * projector

/-- Any choice of added simple edges between gadget ports. -/
def portedAssembly {h k : ℕ} (K : PortedGadget h) (B : SimpleGraph (Fin k)) :
    SimpleGraph (Fin k × Fin (h+1)) where
  Adj x y := (x.1=y.1 ∧ K.graph.Adj x.2 y.2) ∨
    (x.2=K.port ∧ y.2=K.port ∧ B.Adj x.1 y.1)
  symm := by
    rintro x y (h | h)
    · exact Or.inl ⟨h.1.symm,K.graph.symm h.2⟩
    · exact Or.inr ⟨h.2.1,h.1,B.symm h.2.2⟩
  loopless := by
    rintro x (h | h)
    · exact K.graph.loopless _ h.2
    · exact B.loopless _ h.2.2

def portedAssemblyOrdinal {h k : ℕ} (K : PortedGadget h) (B : SimpleGraph (Fin k)) :
    SimpleGraph (Fin (k*(h+1))) := (portedAssembly K B).comap finProdFinEquiv.symm

/-- The genuine full finite-k assertion of Proposition 5, proved in Proposition5.
The original Hilbert space, Lie closure, graph hypotheses and irreducible dimensions
are present explicitly. The external classification is not assumed as a conclusion. -/
def Proposition5Claim {h k : ℕ} (K : PortedGadget h) (B : SimpleGraph (Fin k)) : Prop := by
  classical
  exact let Γ := portedAssemblyOrdinal K B
  let d := 2^(h+1)
  let r := Module.finrank ℂ (LinearMap.range (Matrix.toLin' K.projector))
  let A := r^2 + (d-r)^2
  let D := max r (d-r)
  Module.finrank ℝ (graphStd Γ) ≤ A^k/2-1 ∧ largestIrrep Γ ≤ D^k/2 ∧
    ((Γ.Connected ∧ ¬ Nonempty (Γ.Coloring (Fin 2)) ∧
       (∀ φ : Γ ≃g Γ, φ = SimpleGraph.Iso.refl) ∧ ¬ Γ.IsRegularOfDegree 2) →
      Module.finrank ℝ (graphNat Γ) = d^(2*k)/2-2 ∧
      ((Module.finrank ℝ (graphNat Γ) : ℚ) / Module.finrank ℝ (graphStd Γ)) ≥
        ((d^2 : ℚ)/A)^k - 4/(A : ℚ)^k)
end Paper13

