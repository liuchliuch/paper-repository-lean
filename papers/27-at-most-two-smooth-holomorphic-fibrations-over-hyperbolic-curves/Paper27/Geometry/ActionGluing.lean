import Paper27.Geometry.Objects
import Mathlib.Topology.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Realizing compatible finite powers on an invariant neighbourhood

This is the last step of Proposition 2.4, p.17. The maps initially satisfy their
group identities only on a common neighbourhood W of the compact curve. The
union of the finitely many images is invariant; the identities on W imply the
identities on that union. Thus the actual neighbourhood action is constructed,
not included in a generic gluing axiom.
-/
noncomputable section
open scoped Manifold Topology
namespace Paper27.Geometry.ActionGluing

variable {G X D : Type*} [Group G]

/-- The invariant open neighbourhood used in the source. -/
def invariantNeighbourhood (τ : G → X → X) (W : Set X) : Set X :=
  ⋃ g : G, τ g '' W

/-- Local identities on W propagate to every translate of W. -/
theorem multiplication_on_union (τ : G → X → X) (W : Set X)
    (hcomp : ∀ g h w, w ∈ W → τ g (τ h w) = τ (g * h) w)
    (g h : G) (x : X) (hx : x ∈ invariantNeighbourhood τ W) :
    τ g (τ h x) = τ (g * h) x := by
  obtain ⟨k, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
  rw [hcomp h k y hy, hcomp g (h * k) y hy,
    hcomp (g * h) k y hy, mul_assoc]

theorem identity_on_union (τ : G → X → X) (W : Set X)
    (hcomp : ∀ g h w, w ∈ W → τ g (τ h w) = τ (g * h) w)
    (x : X) (hx : x ∈ invariantNeighbourhood τ W) : τ 1 x = x := by
  obtain ⟨k, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
  rw [hcomp 1 k y hy, one_mul]

theorem maps_union (τ : G → X → X) (W : Set X)
    (hcomp : ∀ g h w, w ∈ W → τ g (τ h w) = τ (g * h) w)
    (g : G) (x : X) (hx : x ∈ invariantNeighbourhood τ W) :
    τ g x ∈ invariantNeighbourhood τ W := by
  obtain ⟨k, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
  apply Set.mem_iUnion.mpr
  refine ⟨g * k, y, hy, ?_⟩
  exact (hcomp g k y hy).symm

/-- The point maps on the invariant neighbourhood are actual permutations. -/
def permutation (τ : G → X → X) (W : Set X)
    (hcomp : ∀ g h w, w ∈ W → τ g (τ h w) = τ (g * h) w) (g : G) :
    Equiv.Perm (invariantNeighbourhood τ W) where
  toFun x := ⟨τ g x, maps_union τ W hcomp g x x.property⟩
  invFun x := ⟨τ g⁻¹ x, maps_union τ W hcomp g⁻¹ x x.property⟩
  left_inv x := by
    apply Subtype.ext
    change τ g⁻¹ (τ g x.val) = x.val
    rw [multiplication_on_union τ W hcomp _ _ _ x.property,
      inv_mul_cancel, identity_on_union τ W hcomp _ x.property]
  right_inv x := by
    apply Subtype.ext
    change τ g (τ g⁻¹ x.val) = x.val
    rw [multiplication_on_union τ W hcomp _ _ _ x.property,
      mul_inv_cancel, identity_on_union τ W hcomp _ x.property]

/-- A genuine group homomorphism into permutations, not merely action germs. -/
def action (τ : G → X → X) (W : Set X)
    (hcomp : ∀ g h w, w ∈ W → τ g (τ h w) = τ (g * h) w) :
    G →* Equiv.Perm (invariantNeighbourhood τ W) where
  toFun := permutation τ W hcomp
  map_one' := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    exact identity_on_union τ W hcomp _ x.property
  map_mul' g h := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    exact (multiplication_on_union τ W hcomp g h x x.property).symm

/-- Invariance of each retraction propagates from W to the actual action
neighbourhood; the same proof applies to both r and s. -/
theorem preserves_on_union (τ : G → X → X) (W : Set X)
    (hcomp : ∀ g h w, w ∈ W → τ g (τ h w) = τ (g * h) w)
    (r : X → D) (hr : ∀ g w, w ∈ W → r (τ g w) = r w)
    (g : G) (x : X) (hx : x ∈ invariantNeighbourhood τ W) : r (τ g x) = r x := by
  obtain ⟨k, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
  rw [hcomp g k y hy, hr (g * k) y hy, hr k y hy]

/-- Fixed points of the germs are fixed points of the actual action. -/
theorem curve_subset_union (τ : G → X → X) (W C : Set X)
    (hCW : C ⊆ W) (hfix : ∀ g x, x ∈ C → τ g x = x) :
    C ⊆ invariantNeighbourhood τ W := by
  intro x hx
  exact Set.mem_iUnion.mpr ⟨1, x, hCW hx, hfix 1 x hx⟩

omit [Group G] in
/-- The union is an actual open neighbourhood when the local automorphisms
are open on W. Compactness/finite powers are used to choose W beforehand. -/
theorem invariantNeighbourhood_open [TopologicalSpace X]
    (τ : G → X → X) (W : Set X) (himages : ∀ g, IsOpen (τ g '' W)) :
    IsOpen (invariantNeighbourhood τ W) := isOpen_iUnion himages

/-- The constructed action is faithful if each nonidentity local power has a
nonfixed point on W, as is witnessed by y↦ζ^j y in the source charts. -/
theorem action_injective (τ : G → X → X) (W : Set X)
    (hcomp : ∀ g h w, w ∈ W → τ g (τ h w) = τ (g * h) w)
    (hid : ∀ w, w ∈ W → τ 1 w = w)
    (hwitness : ∀ g, g ≠ 1 → ∃ w, w ∈ W ∧ τ g w ≠ w) :
    Function.Injective (action τ W hcomp) := by
  apply (injective_iff_map_eq_one (action τ W hcomp)).mpr
  intro g hg
  by_contra hne
  obtain ⟨w, hw, hmove⟩ := hwitness g hne
  have hwU : w ∈ invariantNeighbourhood τ W :=
    Set.mem_iUnion.mpr ⟨1, w, hw, hid w hw⟩
  have heq := Equiv.congr_fun hg ⟨w, hwU⟩
  exact hmove (congrArg Subtype.val heq)

/-- The constructed permutation action really fixes every point of the curve. -/
theorem action_fixes_curve (τ : G → X → X) (W C : Set X)
    (hcomp : ∀ g h w, w ∈ W → τ g (τ h w) = τ (g * h) w)
    (hCW : C ⊆ W) (hfix : ∀ g x, x ∈ C → τ g x = x)
    (g : G) (c : X) (hc : c ∈ C) :
    action τ W hcomp g ⟨c, curve_subset_union τ W C hCW hfix hc⟩ =
      ⟨c, curve_subset_union τ W C hCW hfix hc⟩ := by
  apply Subtype.ext
  exact hfix g c hc

/-- Preservation of either actual retraction by the actual permutation action. -/
theorem action_preserves (τ : G → X → X) (W : Set X)
    (hcomp : ∀ g h w, w ∈ W → τ g (τ h w) = τ (g * h) w)
    (r : X → D) (hr : ∀ g w, w ∈ W → r (τ g w) = r w)
    (g : G) (x : invariantNeighbourhood τ W) :
    r ((action τ W hcomp g x).val) = r x.val :=
  preserves_on_union τ W hcomp r hr g x x.property

/-- Finitely many local assertions, each on an open neighbourhood of `C`, hold
on the actual finite intersection of those neighbourhoods. -/
theorem finite_common_open_neighbourhood [TopologicalSpace X]
    {I : Type*} [Finite I] (C : Set X) (N : I → Set X) (P : I → X → Prop)
    (hopen : ∀ i, IsOpen (N i)) (hcontains : ∀ i, C ⊆ N i)
    (hlaw : ∀ i x, x ∈ N i → P i x) :
    ∃ W : Set X, IsOpen W ∧ C ⊆ W ∧ ∀ i x, x ∈ W → P i x := by
  refine ⟨⋂ i, N i, isOpen_iInter_of_finite hopen, ?_, ?_⟩
  · intro x hx
    exact Set.mem_iInter.mpr (fun i => hcontains i hx)
  · intro i x hx
    exact hlaw i x (Set.mem_iInter.mp hx i)

/-- A concrete common shrinking for finite representatives of all group powers:
all compositions, the identity, and all image-in-`V` conditions hold on one
actual open neighbourhood. This proves the finite intersection step in p.17. -/
theorem common_group_neighbourhood [TopologicalSpace X] [Finite G]
    (τ : G → X → X) (C V : Set X) (hV : IsOpen V) (hCV : C ⊆ V)
    (Nc : G → G → Set X) (hcopen : ∀ g h, IsOpen (Nc g h))
    (hccontains : ∀ g h, C ⊆ Nc g h)
    (hcomp : ∀ g h w, w ∈ Nc g h → τ g (τ h w) = τ (g * h) w)
    (Ni : G → Set X) (hiopen : ∀ g, IsOpen (Ni g))
    (hicontains : ∀ g, C ⊆ Ni g) (himage : ∀ g w, w ∈ Ni g → τ g w ∈ V)
    (None : Set X) (honeopen : IsOpen None) (honecontains : C ⊆ None)
    (hone : ∀ w, w ∈ None → τ 1 w = w) :
    ∃ W : Set X, IsOpen W ∧ C ⊆ W ∧ W ⊆ V ∧
      (∀ g w, w ∈ W → τ g w ∈ V) ∧
      (∀ g h w, w ∈ W → τ g (τ h w) = τ (g * h) w) ∧
      (∀ w, w ∈ W → τ 1 w = w) := by
  obtain ⟨Wc, hWc, hCWc, hcompW⟩ := finite_common_open_neighbourhood C
    (fun gh : G × G => Nc gh.1 gh.2)
    (fun gh w => τ gh.1 (τ gh.2 w) = τ (gh.1 * gh.2) w)
    (fun gh => hcopen gh.1 gh.2) (fun gh => hccontains gh.1 gh.2)
    (fun gh => hcomp gh.1 gh.2)
  obtain ⟨Wi, hWi, hCWi, himageW⟩ := finite_common_open_neighbourhood C Ni
    (fun g w => τ g w ∈ V) hiopen hicontains himage
  refine ⟨V ∩ Wc ∩ Wi ∩ None, ((hV.inter hWc).inter hWi).inter honeopen, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨⟨hCV hx, hCWc hx⟩, hCWi hx⟩, honecontains hx⟩
  · intro x hx
    exact hx.1.1.1
  · intro g w hw
    exact himageW g w hw.1.2
  · intro g h w hw
    exact hcompW (g, h) w hw.1.1.2
  · intro w hw
    exact hone w hw.2

omit [Group G] in
/-- Holomorphicity of the actual maps on the invariant union follows by
restriction from the common domain `V` that contains all image pieces. -/
theorem holomorphic_on_invariantNeighbourhood (X : CompactComplexSurface)
    (τ : G → X → X) (W V : Set X)
    (himages : ∀ g, τ g '' W ⊆ V)
    (hholomorphic : ∀ g, MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) (τ g) V) :
    ∀ g, MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) (τ g)
      (invariantNeighbourhood τ W) := by
  intro g
  apply (hholomorphic g).mono
  intro x hx
  obtain ⟨h, hx⟩ := Set.mem_iUnion.mp hx
  exact himages h hx

/-- Every nonempty open subset meeting an actual surface chart contains a point
with nonzero normal coordinate. This witness is proved, rather than assumed. -/
theorem exists_nonzero_normal_coordinate [TopologicalSpace X]
    (e : OpenPartialHomeomorph X (ℂ × ℂ)) (W : Set X) (hW : IsOpen W)
    (p : X) (hp : p ∈ W) (hep : p ∈ e.source) :
    ∃ w : X, w ∈ W ∧ w ∈ e.source ∧ (e w).2 ≠ 0 := by
  have hO : IsOpen (Prod.snd '' (e '' (e.source ∩ W))) :=
    isOpenMap_snd _ (e.isOpen_image_source_inter hW)
  have hpO : (e p).2 ∈ Prod.snd '' (e '' (e.source ∩ W)) :=
    ⟨e p, ⟨p, ⟨hep, hp⟩, rfl⟩, rfl⟩
  have hinfinite : (Prod.snd '' (e '' (e.source ∩ W))).Infinite :=
    infinite_of_mem_nhds _ (hO.mem_nhds hpO)
  obtain ⟨z, hz, hz0⟩ := hinfinite.exists_notMem_finite (Set.finite_singleton (0 : ℂ))
  obtain ⟨v, ⟨w, ⟨hew, hWw⟩, rfl⟩, hwz⟩ := hz
  refine ⟨w, hWw, hew, ?_⟩
  rw [hwz]
  simpa using hz0

/-- A nonidentity cyclic group element moves every nonzero normal coordinate
under its primitive-root rotation. Exact order is not among the assumptions. -/
theorem primitive_rotation_moves {n : ℕ} [NeZero n] {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ n) (g : Multiplicative (ZMod n)) (hg : g ≠ 1)
    (y : ℂ) (hy : y ≠ 0) : ζ ^ g.toAdd.val * y ≠ y := by
  have hj : g.toAdd.val ≠ 0 := by
    intro hz
    apply hg
    apply Multiplicative.toAdd.injective
    simpa using (ZMod.val_eq_zero g.toAdd).mp hz
  intro h
  have hpow : ζ ^ g.toAdd.val = 1 := mul_right_cancel₀ hy (by simpa using h)
  exact hζ.pow_ne_one_of_pos_of_lt hj (ZMod.val_lt g.toAdd) hpow

/-- The actual open chart and primitive root supply the local nonfixed-point
witnesses required by the general action construction. -/
theorem primitive_normal_chart_witness [TopologicalSpace X]
    {n : ℕ} [NeZero n] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n)
    (τ : Multiplicative (ZMod n) → X → X) (W : Set X) (hW : IsOpen W)
    (e : OpenPartialHomeomorph X (ℂ × ℂ)) (p : X) (hp : p ∈ W) (hep : p ∈ e.source)
    (hcoordinate : ∀ g w, w ∈ W → w ∈ e.source →
      (e (τ g w)).2 = ζ ^ g.toAdd.val * (e w).2) :
    ∀ g, g ≠ 1 → ∃ w, w ∈ W ∧ τ g w ≠ w := by
  obtain ⟨w, hw, hew, hy⟩ := exists_nonzero_normal_coordinate e W hW p hp hep
  intro g hg
  refine ⟨w, hw, ?_⟩
  intro hfixed
  have h := hcoordinate g w hw hew
  rw [hfixed] at h
  exact primitive_rotation_moves hζ g hg (e w).2 hy h.symm

/-- The primitive normal form proves faithfulness of the actual action, and
therefore proves that the actual generator permutation has order `n`. -/
theorem primitive_normal_chart_action [TopologicalSpace X]
    {n : ℕ} [NeZero n] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n)
    (τ : Multiplicative (ZMod n) → X → X) (W : Set X) (hW : IsOpen W)
    (hcomp : ∀ g h w, w ∈ W → τ g (τ h w) = τ (g * h) w)
    (hid : ∀ w, w ∈ W → τ 1 w = w)
    (e : OpenPartialHomeomorph X (ℂ × ℂ)) (p : X) (hp : p ∈ W) (hep : p ∈ e.source)
    (hcoordinate : ∀ g w, w ∈ W → w ∈ e.source →
      (e (τ g w)).2 = ζ ^ g.toAdd.val * (e w).2) :
    Function.Injective (action τ W hcomp) ∧
      orderOf (action τ W hcomp (Multiplicative.ofAdd (1 : ZMod n))) = n := by
  have hinjective : Function.Injective (action τ W hcomp) := action_injective τ W hcomp hid
    (primitive_normal_chart_witness hζ τ W hW e p hp hep hcoordinate)
  refine ⟨hinjective, ?_⟩
  rw [orderOf_injective (action τ W hcomp) hinjective,
    orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]

end Paper27.Geometry.ActionGluing
