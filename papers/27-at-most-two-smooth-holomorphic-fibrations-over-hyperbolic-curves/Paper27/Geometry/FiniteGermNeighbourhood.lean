import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Isolating the source representatives of a finite germ

This file proves the topological source-isolation step in P27, S2.p13.
It uses actual continuous maps, actual fibres, and actual open subsets.
Compactness and Hausdorff separation are the only hypotheses. No branch
divisor, normal form, analytic classification, or external theorem is assumed.
-/

noncomputable section

namespace Paper27.Geometry.FiniteGermNeighbourhood

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- If an open set contains the whole centre fibre of a continuous map from a
compact space to a Hausdorff space, a target neighbourhood has its entire
inverse image in that open set. The proof removes the closed image of its
closed complement. -/
theorem exists_target_neighbourhood_of_fibre_subset [CompactSpace X] [T2Space Y]
    (q : X → Y) (hq : Continuous q) (y₀ : Y) (O : Set X) (hO : IsOpen O)
    (hfibre : q ⁻¹' {y₀} ⊆ O) :
    ∃ V : Set Y, IsOpen V ∧ y₀ ∈ V ∧ q ⁻¹' V ⊆ O := by
  refine ⟨(q '' Oᶜ)ᶜ, (hq.isClosedMap Oᶜ hO.isClosed_compl).isOpen_compl, ?_, ?_⟩
  · rintro ⟨x, hx, hqx⟩
    exact hx (hfibre hqx)
  · intro x hx
    by_contra hnot
    exact hx ⟨x, hnot, rfl⟩

/-- Restriction over any target subspace remains proper. Closedness is the
actual closed-map restriction theorem, and its fibres are compact subsets of
the original compact source. -/
theorem proper_restrictPreimage [CompactSpace X] [T2Space Y]
    (q : X → Y) (hq : Continuous q) (V : Set Y) : IsProperMap (V.restrictPreimage q) := by
  apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
  refine ⟨hq.restrictPreimage, hq.isClosedMap.restrictPreimage V, ?_⟩
  intro y
  rw [Subtype.isCompact_iff]
  have heq : Subtype.val '' ((V.restrictPreimage q) ⁻¹' {y}) = q ⁻¹' {y.val} := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact congrArg Subtype.val hz
    · intro hx
      have hxV : q x ∈ V := by
        rw [show q x = y.val from hx]
        exact y.property
      refine ⟨⟨x, hxV⟩, ?_, rfl⟩
      exact Subtype.ext hx
  rw [heq]
  exact (isClosed_singleton.preimage hq).isCompact

/-- The localization data produced by separating the points of an actual
finite centre fibre. The index is that actual fibre, not an unrelated set. -/
structure FibreIsolation (q : X → Y) (y₀ : Y) where
  target : Set Y
  open_target : IsOpen target
  centre_mem : y₀ ∈ target
  source : (q ⁻¹' {y₀}) → Set X
  open_source : ∀ i, IsOpen (source i)
  point_mem : ∀ i, i.val ∈ source i
  disjoint_source : Pairwise (fun i j => Disjoint (source i) (source j))
  preimage_subset : q ⁻¹' target ⊆ ⋃ i, source i

/-- Hausdorff separation of the finite actual fibre followed by target
shrinking gives mutually disjoint source representatives of all its points. -/
theorem exists_fibre_isolation [CompactSpace X] [T2Space X] [T2Space Y]
    (q : X → Y) (hq : Continuous q) (y₀ : Y) (hfinite : (q ⁻¹' {y₀}).Finite) :
    Nonempty (FibreIsolation q y₀) := by
  obtain ⟨U, hU, hdisjoint⟩ := hfinite.t2_separation
  let O : (q ⁻¹' {y₀}) → Set X := fun i => U i.val
  have hopen : IsOpen (⋃ i, O i) := isOpen_iUnion fun i => (hU i.val).2
  have hcover : q ⁻¹' {y₀} ⊆ ⋃ i, O i := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, (hU x).1⟩
  obtain ⟨V, hV, hy, hpreimage⟩ :=
    exists_target_neighbourhood_of_fibre_subset q hq y₀ _ hopen hcover
  refine ⟨⟨V, hV, hy, O, fun i => (hU i.val).2, fun i => (hU i.val).1, ?_, hpreimage⟩⟩
  intro i j hij
  exact hdisjoint i.property j.property (fun h => hij (Subtype.ext h))

namespace FibreIsolation

variable {q : X → Y} {y₀ : Y}

/-- The actual open source piece after shrinking the target. -/
def piece (S : FibreIsolation q y₀) (i : q ⁻¹' {y₀}) : Set X :=
  S.source i ∩ q ⁻¹' S.target

theorem piece_open (S : FibreIsolation q y₀) (hq : Continuous q) (i : q ⁻¹' {y₀}) :
    IsOpen (S.piece i) := (S.open_source i).inter (S.open_target.preimage hq)

theorem point_mem_piece (S : FibreIsolation q y₀) (i : q ⁻¹' {y₀}) :
    i.val ∈ S.piece i := by
  refine ⟨S.point_mem i, ?_⟩
  change q i.val ∈ S.target
  rw [show q i.val = y₀ from i.property]
  exact S.centre_mem

theorem pieces_pairwise_disjoint (S : FibreIsolation q y₀) :
    Pairwise (fun i j => Disjoint (S.piece i) (S.piece j)) := by
  intro i j hij
  exact (S.disjoint_source hij).mono Set.inter_subset_left Set.inter_subset_left

theorem pieces_cover_preimage (S : FibreIsolation q y₀) :
    q ⁻¹' S.target = ⋃ i, S.piece i := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (S.preimage_subset hx)
    exact Set.mem_iUnion.mpr ⟨i, hi, hx⟩
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact hi.2

/-- The centre fibre in each source neighbourhood is exactly its indexing point. -/
theorem centre_fibre_source (S : FibreIsolation q y₀) (i : q ⁻¹' {y₀}) :
    {x : X | x ∈ S.source i ∧ q x = y₀} = {i.val} := by
  ext x
  constructor
  · rintro ⟨hx, hqx⟩
    let j : q ⁻¹' {y₀} := ⟨x, hqx⟩
    by_cases hji : j = i
    · exact congrArg Subtype.val hji
    · exact False.elim ((Set.disjoint_left.mp (S.disjoint_source (Ne.symm hji)))
        hx (S.point_mem j))
  · intro hx
    have heq : x = i.val := hx
    subst x
    exact ⟨S.point_mem i, i.property⟩

/-- The actual localized piece has precisely its one centre-fibre point. -/
theorem centre_fibre_piece (S : FibreIsolation q y₀) (i : q ⁻¹' {y₀}) :
    {x : X | x ∈ S.piece i ∧ q x = y₀} = {i.val} := by
  ext x
  constructor
  · rintro ⟨hx, hqx⟩
    exact Set.mem_singleton_iff.mp ((S.centre_fibre_source i).subset ⟨hx.1, hqx⟩)
  · intro hx
    have heq : x = i.val := hx
    subst x
    exact ⟨S.point_mem_piece i, i.property⟩

/-- The same actual piece, as a subset of the entire inverse-image space. -/
def relativePiece (S : FibreIsolation q y₀) (i : q ⁻¹' {y₀}) : Set (q ⁻¹' S.target) :=
  {x | x.val ∈ S.source i}

theorem relativePiece_open (S : FibreIsolation q y₀) (i : q ⁻¹' {y₀}) :
    IsOpen (S.relativePiece i) := (S.open_source i).preimage continuous_subtype_val

/-- Each representative is also closed in the full inverse-image space: its
complement is the union of all the other disjoint source representatives. -/
theorem relativePiece_closed (S : FibreIsolation q y₀) (i : q ⁻¹' {y₀}) :
    IsClosed (S.relativePiece i) := by
  have heq : (S.relativePiece i)ᶜ =
      ⋃ j : {j : q ⁻¹' {y₀} // j ≠ i}, S.relativePiece j.val := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (S.preimage_subset x.property)
      have hji : j ≠ i := fun h => hx (h ▸ hj)
      exact Set.mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩
    · intro hx hi
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
      exact (Set.disjoint_left.mp (S.disjoint_source (Ne.symm j.property))) hi hj
  have hopen : IsOpen ((S.relativePiece i)ᶜ) := by
    rw [heq]
    exact isOpen_iUnion fun j => S.relativePiece_open j.val
  exact isOpen_compl_iff.mp hopen

/-- The actual restricted map of a representative to the shrunk target. Its
source is written as the corresponding closed subspace of `q ⁻¹' target`. -/
def pieceMap (S : FibreIsolation q y₀) (i : q ⁻¹' {y₀}) : S.relativePiece i → S.target :=
  fun x => S.target.restrictPreimage q x.val

/-- Each isolated representative is proper over the actual target
neighbourhood, not merely finite at the centre. -/
theorem pieceMap_proper [CompactSpace X] [T2Space Y]
    (S : FibreIsolation q y₀) (hq : Continuous q) (i : q ⁻¹' {y₀}) :
    IsProperMap (S.pieceMap i) :=
  (proper_restrictPreimage q hq S.target).restrict (S.relativePiece_closed i)

/-- If the original map has finite actual fibres, so does each representative.
This is the finite-map property needed when the localization is applied to
the finite pair map in S2.p13. -/
theorem pieceMap_finite_fibres (S : FibreIsolation q y₀)
    (hfinite : ∀ y : Y, (q ⁻¹' {y}).Finite) (i : q ⁻¹' {y₀}) (y : S.target) :
    ((S.pieceMap i) ⁻¹' {y}).Finite := by
  let inclusion : S.relativePiece i → X := fun x => x.val.val
  have hinj : Function.Injective inclusion := by
    intro a b hab
    exact Subtype.ext (Subtype.ext hab)
  apply ((hfinite y.val).preimage hinj.injOn).subset
  intro x hx
  exact congrArg Subtype.val hx

end FibreIsolation

end Paper27.Geometry.FiniteGermNeighbourhood
