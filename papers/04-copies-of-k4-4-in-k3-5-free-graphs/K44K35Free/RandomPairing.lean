import K44K35Free.ProjectivePairing
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

/-!
# Uniform finite group pairings

The exact finite averaging identities used in Section 3.  All averages are
literal sums over the finite group, rather than asymptotic or probabilistic
certificates.  Transitivity is the sole group-action hypothesis.
-/

open scoped BigOperators
open Finset

namespace K44K35Free.RandomPairing

noncomputable def mean {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ ω, f ω) / Fintype.card Ω

variable {G P : Type*} [Group G] [Fintype G] [Fintype P] [MulAction G P] [DecidableEq P]

/-- Left translation sends one action fibre bijectively onto another. -/
noncomputable def actionFiberEquiv (a b c : P) (h : G) (hh : h • b = c) :
    {g : G // g • a = b} ≃ {g : G // g • a = c} where
  toFun g := ⟨h * g.1, by rw [mul_smul, g.2, hh]⟩
  invFun g := ⟨h⁻¹ * g.1, by rw [mul_smul, g.2, ← hh, inv_smul_smul]⟩
  left_inv g := by ext; simp
  right_inv g := by ext; simp

/-- For a transitive finite action, every fibre has the same size. -/
theorem action_fiber_card_eq
    (trans : ∀ b c : P, ∃ h : G, h • b = c) (a b c : P) :
    (univ.filter fun g : G => g • a = b).card =
      (univ.filter fun g : G => g • a = c).card := by
  classical
  obtain ⟨h, hh⟩ := trans b c
  simpa only [Fintype.card_subtype, Set.toFinset_setOf] using
    Fintype.card_congr (actionFiberEquiv a b c h hh)

/-- Orbit-stabilizer, in the fibre form needed for uniform pairings. -/
theorem action_fiber_card_mul
    (trans : ∀ b c : P, ∃ h : G, h • b = c) (a b : P) :
    (univ.filter fun g : G => g • a = b).card * Fintype.card P =
      Fintype.card G := by
  classical
  have hf := Finset.sum_card_fiberwise_eq_card_filter
    (univ : Finset G) (univ : Finset P) (fun g => g • a)
  have he : (∑ c : P, (univ.filter fun g : G => g • a = c).card) =
      Fintype.card P * (univ.filter fun g : G => g • a = b).card := by
    simp_rw [action_fiber_card_eq trans a _ b]
    simp
  simpa only [mem_univ, filter_true, card_univ, he, Nat.mul_comm] using hf

/-- A fixed source plane has uniform image under a uniformly chosen group element. -/
theorem mean_action_indicator
    (trans : ∀ b c : P, ∃ h : G, h • b = c) (a b : P) :
    mean (fun g : G => if g • a = b then (1 : ℝ) else 0) =
      1 / Fintype.card P := by
  classical
  have hg : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hf := action_fiber_card_mul trans a b
  have hf' : ((univ.filter fun g : G => g • a = b).card : ℝ) *
      Fintype.card P = Fintype.card G := by exact_mod_cast hf
  have hp : (Fintype.card P : ℝ) ≠ 0 := by
    haveI : Nonempty P := ⟨a⟩
    exact_mod_cast Fintype.card_ne_zero
  unfold mean
  simp only [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
  field_simp
  exact hf'

/-- Weighted uniformity; in particular this computes expected plane sections. -/
theorem mean_action
    (trans : ∀ b c : P, ∃ h : G, h • b = c) (a : P) (w : P → ℝ) :
    mean (fun g : G => w (g • a)) = (∑ b, w b) / Fintype.card P := by
  classical
  have hi : ∀ g : G, w (g • a) =
      ∑ b : P, if g • a = b then w b else 0 := by
    intro g
    simp
  simp_rw [hi]
  unfold mean
  rw [sum_comm, sum_div]
  calc
    ∑ b : P, (∑ g : G, if g • a = b then w b else 0) / Fintype.card G =
        ∑ b : P, w b * mean (fun g : G => if g • a = b then 1 else 0) := by
      apply sum_congr rfl
      intro b _
      simp only [mean, ← mul_div_assoc, mul_sum]
      apply congrArg (fun x : ℝ => x / Fintype.card G)
      apply sum_congr rfl
      intro g _
      split_ifs <;> simp
    _ = _ := by simp_rw [mean_action_indicator trans]; simp [div_eq_mul_inv, sum_mul]

/-- A bijective reindexing does not change a finite uniform average. -/
theorem mean_equiv {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']
    (e : Ω ≃ Ω') (f : Ω' → ℝ) : mean (fun ω => f (e ω)) = mean f := by
  unfold mean
  rw [Fintype.card_congr e]
  congr 1
  exact e.sum_comp f

/-- Inversion can be used on the right side of the pairing with the same law. -/
theorem mean_inv_action
    (trans : ∀ b c : P, ∃ h : G, h • b = c) (a : P) (w : P → ℝ) :
    mean (fun g : G => w (g⁻¹ • a)) = (∑ b, w b) / Fintype.card P := by
  rw [show (fun g : G => w (g⁻¹ • a)) =
    (fun g : G => (fun h : G => w (h • a)) ((Equiv.inv G) g)) from rfl]
  calc
    _ = mean (fun g : G => w (g • a)) :=
      mean_equiv (Equiv.inv G) (fun g : G => w (g • a))
    _ = _ := mean_action trans a w

/-- Number of designated pairs, with their original left/right indexing. -/
noncomputable def designatedPairs [DecidableEq P] (B : Finset P)
    (dual : P ≃ P) (g : G) : Finset (P × P) :=
  (B ×ˢ B).filter fun ac => g • ac.2 = dual ac.1

/-- Exact expectation in (18): `|B|² / |planes|`. -/
theorem mean_designatedPairs [DecidableEq P]
    (trans : ∀ b c : P, ∃ h : G, h • b = c)
    (B : Finset P) (dual : P ≃ P) :
    mean (fun g : G => ((designatedPairs B dual g).card : ℝ)) =
      (B.card : ℝ) ^ 2 / Fintype.card P := by
  classical
  have hc : ∀ g : G, ((designatedPairs B dual g).card : ℝ) =
      ∑ ac ∈ B ×ˢ B, if g • ac.2 = dual ac.1 then (1 : ℝ) else 0 := by
    intro g
    rw [designatedPairs, card_eq_sum_ones, sum_filter]
    push_cast
    apply sum_congr rfl
    intro ac _
    split_ifs <;> norm_num
  simp_rw [hc]
  unfold mean
  rw [sum_comm, sum_div]
  change (∑ ac ∈ B ×ˢ B,
    mean (fun g : G => if g • ac.2 = dual ac.1 then (1 : ℝ) else 0)) = _
  simp_rw [mean_action_indicator trans]
  simp [pow_two, div_eq_mul_inv]

/-- Linearity of the literal uniform average. -/
theorem mean_add {Ω : Type*} [Fintype Ω] (f h : Ω → ℝ) :
    mean (fun ω => f ω + h ω) = mean f + mean h := by
  simp only [mean, sum_add_distrib, add_div]

theorem mean_sum {Ω A : Type*} [Fintype Ω] (s : Finset A) (f : Ω → A → ℝ) :
    mean (fun ω => ∑ a ∈ s, f ω a) = ∑ a ∈ s, mean (fun ω => f ω a) := by
  unfold mean
  rw [sum_comm, sum_div]

theorem mean_const_mul {Ω : Type*} [Fintype Ω] (a : ℝ) (f : Ω → ℝ) :
    mean (fun ω => a * f ω) = a * mean f := by
  simp only [mean, ← mul_sum]
  ring

theorem mean_dual_action
    (trans : ∀ b c : P, ∃ h : G, h • b = c)
    (dual : P ≃ P) (a : P) (w : P → ℝ) :
    mean (fun g : G => w (dual (g • a))) = (∑ b, w b) / Fintype.card P := by
  rw [mean_action trans a (fun b => w (dual b)), dual.sum_comp w]

/-- Original indexed exceptional-block edge counts, including multiplicities. -/
noncomputable def exceptionalEdgeSum (D : Finset P) (dual : P ≃ P)
    (sectionSize : P → ℝ) (g : G) : ℝ :=
  ∑ E ∈ D, sectionSize E *
    (sectionSize (dual (g • E)) + sectionSize (g⁻¹ • dual E))

/-- Original indexed mutual-block edge counts. -/
noncomputable def mutualEdgeSum (D : Finset P) (dual : P ≃ P)
    (sectionSize : P → ℝ) (g : G) : ℝ :=
  ∑ E ∈ D, sectionSize E *
    ((if dual (g • E) ∈ D then sectionSize (dual (g • E)) else 0) +
     (if g⁻¹ • dual E ∈ D then sectionSize (g⁻¹ • dual E) else 0))

/-- Exact equation (22), before inserting the finite-field section incidence count. -/
theorem mean_exceptionalEdgeSum
    (trans : ∀ b c : P, ∃ h : G, h • b = c)
    (D : Finset P) (dual : P ≃ P) (sectionSize : P → ℝ) :
    mean (exceptionalEdgeSum (G := G) D dual sectionSize) =
      2 * (∑ E ∈ D, sectionSize E) * (∑ F, sectionSize F) / Fintype.card P := by
  unfold exceptionalEdgeSum
  rw [mean_sum]
  simp_rw [mean_const_mul, mean_add, mean_dual_action trans, mean_inv_action trans]
  rw [← sum_mul]
  ring

/-- Exact equation (23); the two indexed types each contribute one square. -/
theorem mean_mutualEdgeSum
    (trans : ∀ b c : P, ∃ h : G, h • b = c)
    (D : Finset P) (dual : P ≃ P) (sectionSize : P → ℝ) :
    mean (mutualEdgeSum (G := G) D dual sectionSize) =
      2 * (∑ E ∈ D, sectionSize E) ^ 2 / Fintype.card P := by
  classical
  let w : P → ℝ := fun E => if E ∈ D then sectionSize E else 0
  have hw : (∑ E, w E) = ∑ E ∈ D, sectionSize E := by
    simp only [w, ← sum_filter]
    congr 1
    ext E
    simp
  change mean (fun g : G => ∑ E ∈ D,
    sectionSize E * (w (dual (g • E)) + w (g⁻¹ • dual E))) = _
  rw [mean_sum]
  simp_rw [mean_const_mul, mean_add, mean_dual_action trans, mean_inv_action trans, hw]
  rw [← sum_mul]
  ring

theorem mean_mono {Ω : Type*} [Fintype Ω] (f h : Ω → ℝ)
    (hf : ∀ ω, f ω ≤ h ω) : mean f ≤ mean h := by
  unfold mean
  exact div_le_div_of_nonneg_right (sum_le_sum fun ω _ => hf ω) (Nat.cast_nonneg _)

/-- Some actual outcome attains the finite average. -/
theorem exists_mean_le {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ) :
    ∃ ω, mean f ≤ f ω := by
  have hn : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hs : (∑ _ω : Ω, mean f) ≤ ∑ ω, f ω := by
    simp only [sum_const, card_univ, nsmul_eq_mul, mean]
    exact le_of_eq (mul_div_cancel₀ _ hn)
  obtain ⟨ω, _, hω⟩ := Finset.exists_le_of_sum_le (s := (univ : Finset Ω))
    univ_nonempty hs
  exact ⟨ω, hω⟩

end K44K35Free.RandomPairing

namespace K44K35Free.Geometry

attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F]

instance generalLinearFinite [Finite F] : Finite (V F ≃ₗ[F] V F) :=
  Finite.of_injective (fun T : V F ≃ₗ[F] V F => (T : V F → V F))
    LinearEquiv.coe_injective

noncomputable instance generalLinearFintype [Fintype F] : Fintype (V F ≃ₗ[F] V F) :=
  Fintype.ofFinite _

noncomputable instance planeFintype [Fintype F] : Fintype (Plane F) := Fintype.ofFinite _

noncomputable instance planeDecidableEq : DecidableEq (Plane F) := Classical.decEq _

/-- The full linear group acts on the actual three-dimensional subspaces. -/
instance generalLinearPlaneAction : MulAction (V F ≃ₗ[F] V F) (Plane F) where
  smul := mapPlane
  one_smul E := mapPlane_refl E
  mul_smul T U E := by
    change mapPlane (U.trans T) E = mapPlane T (mapPlane U E)
    exact mapPlane_trans U T E

@[simp] theorem generalLinear_smul_plane (T : V F ≃ₗ[F] V F) (E : Plane F) :
    T • E = mapPlane T E := rfl

/-- Equation (18), instantiated with actual GL(6,F), planes, and polarity. -/
theorem mean_designated_planes [Fintype F] (B : Finset (Plane F)) :
    RandomPairing.mean (fun T : V F ≃ₗ[F] V F =>
      ((RandomPairing.designatedPairs B polarEquiv T).card : ℝ)) =
        (B.card : ℝ)^2 / Fintype.card (Plane F) := by
  classical
  exact RandomPairing.mean_designatedPairs mapPlane_transitive B polarEquiv

/-- A designated pair of actual planes supplies every required incidence edge. -/
theorem designated_plane_incidence [Fintype F] (α : F) (c : Quartic F)
    (T : V F ≃ₗ[F] V F) (A C : Plane F)
    (hdes : mapPlane T C = polar A) {p r : Param F}
    (hp : p ∈ planeSection α c A) (hr : r ∈ planeSection α c C) :
    Incidence α c T p r := by
  have htr : T (point α c r) ∈ (mapPlane T C).val := by
    simpa using (mem_section α c C r).1 hr
  rw [hdes] at htr
  exact (mem_polar A (T (point α c r))).1 htr _ ((mem_section α c A p).1 hp)

/-- Equation (22), with actual plane sections and both indexed block types. -/
theorem mean_exceptional_plane_edges [Fintype F] (α : F) (c : Quartic F)
    (D : Finset (Plane F)) :
    RandomPairing.mean (RandomPairing.exceptionalEdgeSum
      (G := V F ≃ₗ[F] V F) D polarEquiv
      (fun E => ((planeSection α c E).card : ℝ))) =
      2 * (∑ E ∈ D, ((planeSection α c E).card : ℝ)) *
        (∑ E, ((planeSection α c E).card : ℝ)) / Fintype.card (Plane F) := by
  classical
  exact RandomPairing.mean_exceptionalEdgeSum mapPlane_transitive D polarEquiv _

/-- Equation (23), with actual plane sections and polarity. -/
theorem mean_mutual_plane_edges [Fintype F] (α : F) (c : Quartic F)
    (D : Finset (Plane F)) :
    RandomPairing.mean (RandomPairing.mutualEdgeSum
      (G := V F ≃ₗ[F] V F) D polarEquiv
      (fun E => ((planeSection α c E).card : ℝ))) =
      2 * (∑ E ∈ D, ((planeSection α c E).card : ℝ)) ^ 2 /
        Fintype.card (Plane F) := by
  classical
  exact RandomPairing.mean_mutualEdgeSum mapPlane_transitive D polarEquiv _

/-- The hyperplane imposed by a fixed right endpoint. -/
noncomputable def edgeHyperplane (α : F) (c : Quartic F)
    (T : V F ≃ₗ[F] V F) (r : Param F) : Submodule F (V F) :=
  LinearMap.ker (dotForm (T (point α c r)))

/-- Candidate left rich planes for copies through a fixed ordered edge. -/
noncomputable def edgePlanes [Fintype F] (α : F) (c : Quartic F)
    (T : V F ≃ₗ[F] V F) (p r : Param F) : Finset (Plane F) := by
  classical
  exact univ.filter fun A => point α c p ∈ A.val ∧ A.val ≤ edgeHyperplane α c T r

/-- Designated plane pairs containing an edge inject into the planes through
its left point contained in its right endpoint's orthogonal hyperplane.
This is the geometric injection in Lemma 7. -/
theorem designated_through_edge_le_edgePlanes [Fintype F]
    (α : F) (c : Quartic F) (T : V F ≃ₗ[F] V F) (B : Finset (Plane F))
    (p r : Param F) :
    ((RandomPairing.designatedPairs B polarEquiv T).filter
      (fun ac : Plane F × Plane F => p ∈ planeSection α c ac.1 ∧ r ∈ planeSection α c ac.2)).card ≤
        (edgePlanes α c T p r).card := by
  classical
  apply Finset.card_le_card_of_injOn (f := Prod.fst)
  · intro ac hac
    rcases mem_filter.1 hac with ⟨hdes, hp, hr⟩
    have hd : mapPlane T ac.2 = polar ac.1 := (mem_filter.1 hdes).2
    refine mem_filter.2 ⟨mem_univ _, (mem_section α c ac.1 p).1 hp, ?_⟩
    intro v hv
    have htr : T (point α c r) ∈ (polar ac.1).val := by
      rw [← hd]
      simpa using (mem_section α c ac.2 r).1 hr
    have hz := (mem_polar ac.1 (T (point α c r))).1 htr v hv
    change dotProduct (T (point α c r)) v = 0
    rw [dotProduct_comm]
    exact hz
  · intro ac hac bd hbd hab
    have ha : mapPlane T ac.2 = polar ac.1 :=
      (mem_filter.1 (mem_filter.1 hac).1).2
    have hb : mapPlane T bd.2 = polar bd.1 :=
      (mem_filter.1 (mem_filter.1 hbd).1).2
    apply Prod.ext hab
    apply (mapPlaneEquiv T).injective
    change mapPlane T ac.2 = mapPlane T bd.2
    rw [ha, hb, hab]

end K44K35Free.Geometry
