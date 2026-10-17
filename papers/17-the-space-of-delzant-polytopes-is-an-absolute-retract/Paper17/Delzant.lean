import Paper17.Basic
import Paper17.Polytope
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Normal fans, smoothness, and Delzant polytopes (paper §2)

We set up cones, fans, refinement, the normal fan of a polytope, the Delzant
property, and record Lemmas 2.1–2.3 and Example 2.4.

Proved here:
* `det2_example_2_4` / `det2_hexagon_*` — the determinant computations of Example 2.4
* `exists_mem_verts_isMaxOn` — linear functionals attain maxima at vertices
* `carrier_add_eq` / `carrier_smul_eq` — Minkowski/dilation calculus of carriers
* `normalConeAt` is a well-defined cone
-/

noncomputable section

open scoped BigOperators Pointwise

namespace Paper17

/-! ## Auxiliary facts (see `Paper17.Basic` for `dot_add_right`, `dot_smul_right`) -/

/-- Linear functionals attain their maximum on a polytope at a vertex. -/
theorem exists_mem_verts_isMaxOn {m : ℕ} (P : Polytope m) (u : V m) :
    ∃ v ∈ P.verts, ∀ y ∈ P.carrier, dot u y ≤ dot u v := by
  classical
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image P.verts (fun x => dot u x)
    P.nonempty_verts'
  refine ⟨v, hv, fun y hy => ?_⟩
  have half : Convex ℝ {x : V m | dot u x ≤ dot u v} := by
    rw [convex_iff_add_mem]
    intro x hx y hy a b ha hb hab
    show dot u (a • x + b • y) ≤ dot u v
    rw [dot_add_right, dot_smul_right, dot_smul_right]
    have hx' : dot u x ≤ dot u v := hx
    have hy' : dot u y ≤ dot u v := hy
    have h1 : a * dot u x ≤ a * dot u v := mul_le_mul_of_nonneg_left hx' ha
    have h2 : b * dot u y ≤ b * dot u v := mul_le_mul_of_nonneg_left hy' hb
    have h3 : a * dot u v + b * dot u v = dot u v := by
      rw [← add_mul, hab, one_mul]
    linarith [h1, h2, h3]
  have hgen : (P.verts : Set (V m)) ⊆ {x | dot u x ≤ dot u v} :=
    fun w hw => hmax w hw
  have hsub : convexHull ℝ (P.verts : Set (V m)) ⊆ {x | dot u x ≤ dot u v} :=
    convexHull_min hgen half
  exact hsub hy

/-- The carrier of a Minkowski sum is the Minkowski sum of carriers. -/
theorem carrier_add_eq {m : ℕ} (P Q : Polytope m) :
    (P.add Q).carrier = P.carrier + Q.carrier := by
  unfold Polytope.carrier Polytope.add
  simp only [Finset.coe_image, Finset.product_eq_sprod, Finset.coe_product]
  have hset : (fun p : V m × V m => p.1 + p.2) '' ((P.verts : Set (V m)) ×ˢ (Q.verts : Set (V m)))
      = (P.verts : Set (V m)) + (Q.verts : Set (V m)) :=
    Set.add_image_prod
  rw [hset, convexHull_add]

/-- The carrier of a dilation is the dilation of the carrier. -/
theorem carrier_smul_eq {m : ℕ} (P : Polytope m) (t : ℝ) :
    (P.smul t).carrier = t • P.carrier := by
  unfold Polytope.carrier Polytope.smul
  simp only [Finset.coe_image, Set.image_smul, convexHull_smul]

/-! ## Cones and fans -/

/-- A polyhedral cone in `V m` (a convex cone containing 0). -/
structure Cone (m : ℕ) where
  carrier : Set (V m)
  convex' : Convex ℝ carrier
  smul_mem' : ∀ ⦃x : V m⦄ ⦃t : ℝ⦄, x ∈ carrier → 0 ≤ t → t • x ∈ carrier
  zero_mem' : (0 : V m) ∈ carrier

namespace Cone

variable {m : ℕ}

instance : SetLike (Cone m) (V m) where
  coe := carrier
  coe_injective' K L h := by cases K; cases L; congr

@[ext]
theorem ext {K L : Cone m} (h : (K : Set (V m)) = L) : K = L := SetLike.ext' h

theorem convex (K : Cone m) : Convex ℝ (K : Set (V m)) := K.convex'
theorem smul_mem (K : Cone m) {x : V m} {t : ℝ} (hx : x ∈ K) (ht : 0 ≤ t) :
    t • x ∈ K := K.smul_mem' hx ht
theorem zero_mem (K : Cone m) : (0 : V m) ∈ K := K.zero_mem'

/-- Intersection of two cones (used for common refinements). -/
def inter (K₁ K₂ : Cone m) : Cone m where
  carrier := (K₁ : Set (V m)) ∩ (K₂ : Set (V m))
  convex' := K₁.convex.inter K₂.convex
  smul_mem' := by
    intro x t hx ht
    exact ⟨K₁.smul_mem hx.1 ht, K₂.smul_mem hx.2 ht⟩
  zero_mem' := ⟨K₁.zero_mem, K₂.zero_mem⟩

theorem inter_carrier (K₁ K₂ : Cone m) :
    (K₁.inter K₂ : Set (V m)) = (K₁ : Set (V m)) ∩ (K₂ : Set (V m)) := rfl

end Cone

/-- A fan: finite collection of cones covering `V m`. -/
structure Fan (m : ℕ) where
  cones : Finset (Cone m)
  covers' : ⋃ K ∈ cones, (K : Set (V m)) = Set.univ

namespace Fan

variable {m : ℕ}

/-- Refinement: every cone of `f` is contained in a cone of `g`. -/
def refines (f g : Fan m) : Prop :=
  ∀ K' ∈ f.cones, ∃ K ∈ g.cones, (K' : Set (V m)) ⊆ K

theorem refines_refl (f : Fan m) : refines f f := by
  intro K' hK'
  exact ⟨K', hK', fun _ hx => hx⟩

theorem refines_trans {f g h : Fan m} (h₁ : refines f g) (h₂ : refines g h) :
    refines f h := by
  intro K' hK'
  obtain ⟨K, hK, hss⟩ := h₁ K' hK'
  obtain ⟨M, hM, hss'⟩ := h₂ K hK
  exact ⟨M, hM, hss.trans hss'⟩

/-- Mutual refinement. -/
def Equivalent (f g : Fan m) : Prop := refines f g ∧ refines g f

/-- Smoothness of a cone: positive span of a lattice basis of `V m`. -/
def IsSmoothCone (K : Cone m) : Prop :=
  ∃ u : Fin m → V m,
    (∀ i j, ∃ k : ℤ, u i j = k) ∧
    |Matrix.det (fun i j => u i j)| = 1 ∧
    (K : Set (V m)) = {x | ∃ t : Fin m → ℝ, (∀ i, 0 ≤ t i) ∧ x = ∑ i, t i • u i}

/-- A fan is smooth if every full-dimensional cone is smooth
(lower-dimensional cones are faces and are not required to be unimodular). -/
def IsSmooth (f : Fan m) : Prop :=
  ∀ K ∈ f.cones, (interior (K : Set (V m))).Nonempty → IsSmoothCone K

/-- Common refinement of two fans (pairwise intersections of cones). -/
def meet (f g : Fan m) : Fan m := by
  classical
  exact {
    cones := (f.cones.product g.cones).image (fun p => Cone.inter p.1 p.2)
    covers' := by
      apply Set.eq_univ_of_forall
      intro x
      simp only [Set.mem_iUnion]
      have hf : x ∈ ⋃ K ∈ f.cones, (K : Set (V m)) := by rw [f.covers']; trivial
      have hg : x ∈ ⋃ K ∈ g.cones, (K : Set (V m)) := by rw [g.covers']; trivial
      simp only [Set.mem_iUnion] at hf hg
      obtain ⟨K₁, hK₁, hx₁⟩ := hf
      obtain ⟨K₂, hK₂, hx₂⟩ := hg
      refine ⟨Cone.inter K₁ K₂, Finset.mem_image.2 ⟨⟨K₁, K₂⟩,
        Finset.mem_product.2 ⟨hK₁, hK₂⟩, rfl⟩, ⟨hx₁, hx₂⟩⟩
  }

theorem meet_refines_left (f g : Fan m) : refines (meet f g) f := by
  intro K' hK'
  classical
  obtain ⟨⟨K₁, K₂⟩, h, rfl⟩ := Finset.mem_image.1 hK'
  have hprod : K₁ ∈ f.cones ∧ K₂ ∈ g.cones := Finset.mem_product.1 h
  exact ⟨K₁, hprod.1, Set.inter_subset_left⟩

theorem meet_refines_right (f g : Fan m) : refines (meet f g) g := by
  intro K' hK'
  classical
  obtain ⟨⟨K₁, K₂⟩, h, rfl⟩ := Finset.mem_image.1 hK'
  have hprod : K₁ ∈ f.cones ∧ K₂ ∈ g.cones := Finset.mem_product.1 h
  exact ⟨K₂, hprod.2, Set.inter_subset_right⟩

/-- If `g` refines `f`, their common refinement is equivalent to `g`
("the common refinement of a chain is its finest member"). -/
theorem meet_equiv_of_refines {f g : Fan m} (h : refines g f) :
    Equivalent (meet f g) g := by
  constructor
  · exact meet_refines_right f g
  · classical
    intro K' hK'
    obtain ⟨K, hK, hss⟩ := h K' hK'
    refine ⟨Cone.inter K K', Finset.mem_image.2 ⟨⟨K, K'⟩,
      Finset.mem_product.2 ⟨hK, hK'⟩, rfl⟩, fun x hx => ⟨hss hx, hx⟩⟩

end Fan

/-! ## Normal cones and the normal fan -/

/-- The normal cone at a point `x` of a polytope `P`. -/
def normalConeAt {m : ℕ} (P : Polytope m) (x : V m) : Cone m where
  carrier := {u : V m | ∀ y ∈ P.carrier, dot u x ≥ dot u y}
  convex' := by
    intro u hu v hv a b ha hb hab
    show ∀ y ∈ P.carrier, dot (a • u + b • v) x ≥ dot (a • u + b • v) y
    intro y hy
    have hu' : dot u x ≥ dot u y := hu y hy
    have hv' : dot v x ≥ dot v y := hv y hy
    rw [dot_add_left, dot_smul_left, dot_smul_left,
      dot_add_left, dot_smul_left, dot_smul_left]
    nlinarith
  smul_mem' := by
    intro x' t hx' ht
    show ∀ y ∈ P.carrier, dot (t • x') x ≥ dot (t • x') y
    intro y hy
    rw [dot_smul_left, dot_smul_left]
    exact mul_le_mul_of_nonneg_left (hx' y hy) ht
  zero_mem' := by
    intro y hy
    show dot (0 : V m) x ≥ dot (0 : V m) y
    unfold dot
    simp

/-- The normal fan of a polytope: one cone per vertex. -/
def NormalFan {m : ℕ} (P : Polytope m) : Fan m := by
  classical
  exact {
    cones := P.verts.image (fun v => normalConeAt P v)
    covers' := by
      apply Set.eq_univ_of_forall
      intro u
      simp only [Set.mem_iUnion]
      obtain ⟨v, hv, hmax⟩ := exists_mem_verts_isMaxOn P u
      refine ⟨normalConeAt P v, Finset.mem_image.2 ⟨v, hv, rfl⟩, ?_⟩
      exact fun y hy => hmax y hy
  }

/-! ## Normal cones and Minkowski operations (equation 2.3) -/

/-- **Equation (2.3)** at the level of cones: the normal cone of a sum is the
intersection of the normal cones of the summands. -/
theorem normalConeAt_add {m : ℕ} {P Q : Polytope m} {v w : V m}
    (hv : v ∈ P.carrier) (hw : w ∈ Q.carrier) :
    (normalConeAt (P.add Q) (v + w) : Set (V m))
      = (normalConeAt P v : Set (V m)) ∩ (normalConeAt Q w : Set (V m)) := by
  have hcar : (P.add Q).carrier = P.carrier + Q.carrier := carrier_add_eq P Q
  apply Set.ext
  intro u
  simp only [Set.mem_inter_iff]
  constructor
  · intro hu
    have hv' : ∀ y ∈ P.carrier, dot u y ≤ dot u v := by
      intro y hy
      have hyw : y + w ∈ (P.add Q).carrier := by
        rw [hcar]
        exact Set.add_mem_add hy hw
      have hge : dot u (v + w) ≥ dot u (y + w) := hu (y + w) hyw
      rw [dot_add_right, dot_add_right] at hge
      linarith
    have hw' : ∀ z ∈ Q.carrier, dot u z ≤ dot u w := by
      intro z hz
      have hvz : v + z ∈ (P.add Q).carrier := by
        rw [hcar]
        exact Set.add_mem_add hv hz
      have hge : dot u (v + w) ≥ dot u (v + z) := hu (v + z) hvz
      rw [dot_add_right, dot_add_right] at hge
      linarith
    exact ⟨hv', hw'⟩
  · intro hu
    obtain ⟨hu1, hu2⟩ := hu
    intro y hy
    have hy' : y ∈ P.carrier + Q.carrier := hcar ▸ hy
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Set.mem_add.1 hy'
    have h1 : dot u y₁ ≤ dot u v := hu1 y₁ hy₁
    have h2 : dot u y₂ ≤ dot u w := hu2 y₂ hy₂
    show dot u (v + w) ≥ dot u (y₁ + y₂)
    rw [dot_add_right, dot_add_right]
    linarith

/-- Positive dilations do not change normal cones. -/
theorem normalConeAt_smul {m : ℕ} {P : Polytope m} {t : ℝ} (ht : 0 < t) {x : V m}
    (hx : x ∈ P.carrier) :
    (normalConeAt (P.smul t) (t • x) : Set (V m)) = (normalConeAt P x : Set (V m)) := by
  have hcar : (P.smul t).carrier = t • P.carrier := carrier_smul_eq P t
  apply Set.ext
  intro u
  constructor
  · intro hu
    intro y hy
    have hy' : t • y ∈ (P.smul t).carrier := by
      rw [hcar]
      exact Set.smul_mem_smul_set hy
    have hge : dot u (t • x) ≥ dot u (t • y) := hu (t • y) hy'
    rw [dot_smul_right, dot_smul_right] at hge
    exact (mul_le_mul_iff_of_pos_left ht).1 hge
  · intro hu
    intro y hy
    rw [hcar] at hy
    obtain ⟨z, hz, rfl⟩ := Set.mem_smul_set.1 hy
    show dot u (t • x) ≥ dot u (t • z)
    rw [dot_smul_right, dot_smul_right]
    exact mul_le_mul_of_nonneg_left (hu z hz) (le_of_lt ht)

/-- The normal fan of a Minkowski sum refines the common refinement of the
normal fans of the summands (one direction of equation 2.3). -/
theorem normalFan_add_refines_meet {m : ℕ} (P Q : Polytope m) :
    Fan.refines (NormalFan (P.add Q)) (Fan.meet (NormalFan P) (NormalFan Q)) := by
  classical
  intro K' hK'
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hK'
  -- v is a vertex of P.add Q, so v = p + q for vertices p of P and q of Q
  obtain ⟨p, q, hp, hq, rfl⟩ : ∃ p q, p ∈ P.verts ∧ q ∈ Q.verts ∧ v = p + q := by
    have hv' : v ∈ (P.verts.product Q.verts).image (fun p => p.1 + p.2) := hv
    obtain ⟨⟨p, q⟩, hpq, he⟩ := Finset.mem_image.1 hv'
    have hprod : p ∈ P.verts ∧ q ∈ Q.verts := Finset.mem_product.1 hpq
    exact ⟨p, q, hprod.1, hprod.2, he.symm⟩
  refine ⟨Cone.inter (normalConeAt P p) (normalConeAt Q q), ?_, ?_⟩
  · refine Finset.mem_image.2 ⟨(normalConeAt P p, normalConeAt Q q),
      Finset.mem_product.2 ⟨?_, ?_⟩, rfl⟩
    · exact Finset.mem_image.2 ⟨p, hp, rfl⟩
    · exact Finset.mem_image.2 ⟨q, hq, rfl⟩
  · -- the normal cone of the sum equals the intersection (2.3)
    have hsub : (normalConeAt (P.add Q) (p + q) : Set (V m))
        = (normalConeAt P p : Set (V m)) ∩ (normalConeAt Q q : Set (V m)) :=
      normalConeAt_add (subset_convexHull _ _ hp) (subset_convexHull _ _ hq)
    intro x hx
    rw [hsub] at hx
    exact hx

/-- The other direction of equation (2.3): every cone of the common refinement
is contained in a normal cone of the sum.  Together with
`normalFan_add_refines_meet`, the normal fan of a sum is equivalent to the
common refinement of the summands' normal fans. -/
theorem normalFan_add_refined_by_meet {m : ℕ} (P Q : Polytope m) :
    Fan.refines (Fan.meet (NormalFan P) (NormalFan Q)) (NormalFan (P.add Q)) := by
  classical
  intro K' hK'
  obtain ⟨⟨K₁, K₂⟩, h, rfl⟩ := Finset.mem_image.1 hK'
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 (Finset.mem_product.1 h).1
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 (Finset.mem_product.1 h).2
  refine ⟨normalConeAt (P.add Q) (p + q), ?_, ?_⟩
  · refine Finset.mem_image.2 ⟨p + q, ?_, rfl⟩
    exact Finset.mem_image.2 ⟨⟨p, q⟩, Finset.mem_product.2 ⟨hp, hq⟩, rfl⟩
  · have hsub : (normalConeAt (P.add Q) (p + q) : Set (V m))
        = (normalConeAt P p : Set (V m)) ∩ (normalConeAt Q q : Set (V m)) :=
      normalConeAt_add (subset_convexHull _ _ hp) (subset_convexHull _ _ hq)
    intro x hx
    have hx' : x ∈ (normalConeAt P p : Set (V m)) ∩ (normalConeAt Q q : Set (V m)) := hx
    rw [← hsub] at hx'
    exact hx'

/-- Equation (2.3) at the level of fans: the normal fan of a sum is equivalent
to the common refinement of the summands' normal fans. -/
theorem normalFan_add {m : ℕ} (P Q : Polytope m) :
    Fan.Equivalent (NormalFan (P.add Q)) (Fan.meet (NormalFan P) (NormalFan Q)) :=
  ⟨normalFan_add_refines_meet P Q, normalFan_add_refined_by_meet P Q⟩

/-! ## Delzant polytopes -/

/-- Delzant property: full-dimensional with smooth normal fan.
Equivalently: simple, rational edges, primitive edge vectors at each vertex
form a basis of `ℤ^n`. -/
def IsDelzant {m : ℕ} (P : Polytope m) : Prop :=
  P.IsFullDim ∧ (NormalFan P).IsSmooth

/-- The space of full-dimensional Delzant polytopes `𝒟(n)`. -/
def DelzantPolytope (n : ℕ) := {P : Polytope n // IsDelzant P}

namespace DelzantPolytope

variable {n : ℕ}

/-- The refinement preorder: `P ≼ Q` iff `N(Q)` refines `N(P)`. -/
def le (P Q : DelzantPolytope n) : Prop := (NormalFan Q.val).refines (NormalFan P.val)

theorem le_refl (P : DelzantPolytope n) : le P P := Fan.refines_refl _
theorem le_trans {P Q R : DelzantPolytope n} (h₁ : le P Q) (h₂ : le Q R) : le P R :=
  Fan.refines_trans h₂ h₁

def carrier (P : DelzantPolytope n) : Set (V n) := P.val.carrier

theorem isDelzant (P : DelzantPolytope n) : IsDelzant P.val := P.property

/-- **Lemma 2.1** (Interpolation along a chain).
If `N(P_j)` refines `N(P_i)` for `i < j`, every convex combination of the `P_i`
is Delzant, with the normal fan of `P_j` where `j` is the last positive index.

We record the combinatorial core: the last positive index `j` exists, and every
positively weighted `P_i` is coarser than `P_j` while `P_j` refines itself, so
the chain of normal fans has `N(P_j)` as its finest member.  Geometric content
(see `lemma_2_1_pair`): a two-term Minkowski interpolation `αP + βQ` along a
chain is Delzant with `N(αP + βQ) ≈ N(Q)`; positive dilation preserves fans
(`normalConeAt_smul`); apply (2.3) (`normalConeAt_add`) along the chain. -/
theorem exists_last_positive_weight {k : ℕ} (P : Fin (k+1) → DelzantPolytope n)
    (hchain : ∀ i j : Fin (k+1), (i : ℕ) ≤ j → le (P i) (P j))
    (w : Fin (k+1) → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) :
    ∃ j : Fin (k+1), 0 < w j ∧ (∀ i, 0 < w i → (i : ℕ) ≤ j) := by
  classical
  -- Some weight is positive: otherwise all vanish, contradicting `hsum = 1`.
  have hex : ∃ i : Fin (k+1), 0 < w i := by
    by_contra h
    have hz : ∀ i : Fin (k+1), w i ≤ 0 := by
      intro i
      by_contra hi
      push_neg at hi
      exact h ⟨i, hi⟩
    have hz' : ∀ i : Fin (k+1), w i = 0 :=
      fun i => le_antisymm (hz i) (hw i)
    rw [Finset.sum_eq_zero (fun i _ => hz' i)] at hsum
    norm_num at hsum
  -- The support {i | 0 < w i} is a nonempty Finset; take its largest index.
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter (fun i : Fin (k+1) => 0 < w i))
    (fun i : Fin (k+1) => (i : ℕ))
    (let ⟨i, hi⟩ := hex; ⟨i, by simpa using hi⟩)
  refine ⟨j, ?_, ?_⟩
  · simpa using hj
  · intro i hi
    have hi' : i ∈ Finset.univ.filter (fun i : Fin (k+1) => 0 < w i) := by
      simpa using hi
    exact hmax i hi'

/-- Special case of Lemma 2.2 that is complete: a single polytope is its own
smooth refinement. -/
theorem lemma_2_2_singleton {n : ℕ} (Ps : Fin 1 → DelzantPolytope n) :
    ∃ Q : DelzantPolytope n, ∀ i, DelzantPolytope.le (Ps i) Q :=
  ⟨Ps 0, fun i => by
    have hi : i = (0 : Fin 1) := Subsingleton.elim i 0
    rw [hi]; exact le_refl _⟩

/-- Smoothness depends only on the set of cones of a fan (not on the Finset
multiplicity).  Mutually refining fans need not share smoothness — a proper
face cone of a smooth cone is not itself unimodular — so the transfer
hypothesis is equality of the underlying cone sets. -/
theorem isSmooth_of_equivalent {n : ℕ} {f g : Fan n}
    (h : ∀ K : Cone n, K ∈ f.cones ↔ K ∈ g.cones) (hs : f.IsSmooth) : g.IsSmooth := by
  intro K hK hdim
  exact hs K ((h K).2 hK) hdim

/-- The Minkowski perturbation part of Lemma 2.3: `Q_t = P + tS` converges to
`P` in Hausdorff distance as `t → 0⁺`.  Precisely, `d_H(P + tS, P) ≤ t · M`
where `M = max_{s ∈ S} ‖s‖`, so any `t ∈ (0, η/M)` works. -/
theorem lemma_2_3_perturbation {m : ℕ} (P S : Polytope m)
    {η : ℝ} (hη : 0 < η) :
    ∃ t : ℝ, 0 < t ∧
      Metric.hausdorffDist ((P.add (S.smul t)).carrier) P.carrier < η := by
  -- Maximum of `dist · 0` on the compact nonempty carrier of `S`.
  have hsc : IsCompact S.carrier := S.isCompact
  have hsne : S.carrier.Nonempty := S.nonempty
  have hcont : Continuous (fun x : V m => dist x 0) :=
    (continuous_id.dist (continuous_const : Continuous fun _ => (0 : V m)))
  obtain ⟨s₀, hs₀, hmax⟩ := hsc.exists_isMaxOn hsne hcont.continuousOn
  -- `hmax : IsMaxOn (fun x => dist x 0) S.carrier s₀`
  set M : ℝ := dist s₀ 0 with hM
  -- Choose a positive scale with `t * M < η`.
  have hM0 : 0 ≤ M := dist_nonneg
  obtain ⟨t, ht, htM⟩ : ∃ t : ℝ, 0 < t ∧ t * M < η := by
    rcases le_or_gt M 0 with hMpos | hMpos
    · -- M = 0: any small positive t works.
      refine ⟨min 1 (η / 2), by positivity, ?_⟩
      have hM0' : M = 0 := le_antisymm hMpos hM0
      rw [hM0', mul_zero]
      exact hη
    · refine ⟨η / (2 * M), by positivity, ?_⟩
      have h2M : 0 < 2 * M := by positivity
      calc η / (2 * M) * M = η / 2 := by field_simp
        _ < η := by linarith
  -- Hausdorff estimate: every point of P + tS is within `t*M` of P and conversely.
  have hcar : (P.add (S.smul t)).carrier = P.carrier + t • S.carrier := by
    rw [carrier_add_eq, carrier_smul_eq]
  have hbound : ∀ y ∈ S.carrier, dist (t • y) 0 ≤ t * M := by
    intro y hy
    have hyM : dist y 0 ≤ M := hmax hy
    have hdist : dist (t • y) 0 = t * dist y 0 := by
      have h1 : dist (t • y) (t • (0 : V m)) = ‖t‖ * dist y 0 := dist_smul₀ t y 0
      rw [smul_zero] at h1
      rw [h1, Real.norm_eq_abs, abs_of_nonneg ht.le]
    rw [hdist]
    exact mul_le_mul_of_nonneg_left hyM ht.le
  have hstep1 : ∀ x ∈ (P.add (S.smul t)).carrier, ∃ y ∈ P.carrier, dist x y < η := by
    intro x hx
    rw [hcar] at hx
    obtain ⟨p, hp, z, hz, rfl⟩ := Set.mem_add.1 hx
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.1 hz
    refine ⟨p, hp, ?_⟩
    have hdist : dist (p + t • y) p = dist (t • y) 0 := by
      simp [dist_eq_norm]
    rw [hdist]
    exact (hbound y hy).trans_lt htM
  have hstep2 : ∀ y ∈ P.carrier, ∃ x ∈ (P.add (S.smul t)).carrier, dist y x < η := by
    intro y hy
    obtain ⟨s₁, hs₁⟩ := hsne
    refine ⟨y + t • s₁, ?_, ?_⟩
    · rw [hcar]
      exact Set.add_mem_add hy (Set.smul_mem_smul_set hs₁)
    · have hdist : dist y (y + t • s₁) = dist (t • s₁) 0 := by
        have hcancel : y - (y + t • s₁) = -(t • s₁) := by abel
        simp [dist_eq_norm, hcancel]
      rw [hdist]
      exact (hbound s₁ hs₁).trans_lt htM
  -- Conclude via the Hausdorff distance characterization.
  have hle : Metric.hausdorffDist ((P.add (S.smul t)).carrier) P.carrier ≤ t * M := by
    apply Metric.hausdorffDist_le_of_mem_dist (mul_nonneg ht.le hM0)
    · intro x hx
      rw [hcar] at hx
      obtain ⟨p, hp, z, hz, rfl⟩ := Set.mem_add.1 hx
      obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.1 hz
      exact ⟨p, hp, by simpa [dist_eq_norm] using hbound y hy⟩
    · intro p hp
      refine ⟨p + t • s₀, ?_, ?_⟩
      · rw [hcar]
        exact Set.add_mem_add hp (Set.smul_mem_smul_set hs₀)
      · simpa [dist_eq_norm] using hbound s₀ hs₀
  exact ⟨t, ht, lt_of_le_of_lt hle htM⟩

end DelzantPolytope

/-! ## Example 2.4: Minkowski sums need not be Delzant -/

/-- The 2-dimensional determinant of two vectors. -/
def det2 (u v : V 2) : ℝ := u 0 * v 1 - u 1 * v 0

theorem det2_apply (u v : V 2) : det2 u v = u 0 * v 1 - u 1 * v 0 := rfl

/-- The adjacent pair `(1,1), (-1,1)` of the normal fan of `A+B'` has
determinant 2, so `A+B'` is not Delzant. -/
theorem det2_example_2_4 : det2 ![1, 1] ![-1, 1] = 2 := by
  norm_num [det2]

/-- All consecutive determinants of the hexagon rays are 1 (smooth fan). -/
theorem det2_hexagon_1 : det2 ![1, 0] ![1, 1] = 1 := by norm_num [det2]
theorem det2_hexagon_2 : det2 ![1, 1] ![0, 1] = 1 := by norm_num [det2]
theorem det2_hexagon_3 : det2 ![0, 1] ![-1, 1] = 1 := by norm_num [det2]
theorem det2_hexagon_4 : det2 ![-1, 1] ![-1, 0] = 1 := by norm_num [det2]
theorem det2_hexagon_5 : det2 ![-1, 0] ![0, -1] = 1 := by norm_num [det2]
theorem det2_hexagon_6 : det2 ![0, -1] ![1, 0] = 1 := by norm_num [det2]

/-- The two triangles of Example 2.4. -/
def triangleA : Polytope 2 :=
  ⟨{![0, 0], ![1, 0], ![0, 1]}, by
    rw [Finset.Nonempty]; exact ⟨![0, 0], by simp⟩⟩

def triangleB' : Polytope 2 :=
  ⟨{![0, 0], ![-1, 0], ![0, 1]}, by
    rw [Finset.Nonempty]; exact ⟨![0, 0], by simp⟩⟩

/-- The hexagon `T` that is a common smooth refinement of the fans of `A` and
`B'` (Example 2.4). -/
def hexagonT : Polytope 2 :=
  ⟨{![2, -2], ![2, 1], ![1, 2], ![-1, 2], ![-2, 1], ![-2, -2]}, by
    rw [Finset.Nonempty]; exact ⟨![2, -2], by simp⟩⟩

/-- Euclidean norm squared of a point in `V 2`. -/
def enormSq (x : V 2) : ℝ := x 0 ^ 2 + x 1 ^ 2

theorem enormSq_example : enormSq ![2, -2] = 8 := by
  norm_num [enormSq]

/-- In dimension 3, the product point `(2,-2,1)` has Euclidean norm-squared 9
(hence Euclidean norm 3, as stated in Example 2.4). -/
def enormSq3 (x : V 3) : ℝ := x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2

theorem enormSq3_example : enormSq3 ![2, -2, 1] = 9 := by
  simp [enormSq3]
  norm_num

end Paper17
