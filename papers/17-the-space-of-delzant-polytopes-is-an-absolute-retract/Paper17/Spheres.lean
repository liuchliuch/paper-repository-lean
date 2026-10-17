import Paper17.AbsExt
import Paper17.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Path
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Real.Basic

/-!
# Corollary 4.1 and Corollary 1.3: filling spheres and deformation retract

Corollary 4.1: every continuous map `f : S^k → 𝒟(n)` extends to a continuous
map `B^{k+1} → 𝒟(n)`.

Corollary 1.3: `𝒟(n)` strongly deformation retracts onto any prescribed
polytope `P*`.  The argument is Theorem 1.2 applied to the closed subset
`A = (𝒟(n) × {0,1}) ∪ ({P*} × [0,1])` of `X = 𝒟(n) × [0,1]`, with the
prescriptions `f(P,0)=P`, `f(P,1)=P*`, `f(P*,t)=P*`.
-/

noncomputable section

open scoped Topology

namespace Paper17

/-! ## Spheres and balls -/

/-- The unit sphere `S^k ⊂ ℝ^{k+1}`. -/
def sphere (k : ℕ) : Set (V (k + 1)) :=
  {x | ∑ i, x i ^ 2 = 1}

/-- The closed unit ball `B^{k+1} ⊂ ℝ^{k+1}`. -/
def unitSphereBall (k : ℕ) : Set (V (k + 1)) :=
  {x | ∑ i, x i ^ 2 ≤ 1}

theorem sphere_subset_unitSphereBall (k : ℕ) : sphere k ⊆ unitSphereBall k :=
  fun _ hx => le_of_eq hx

/-- The squared-norm function on `V (k+1)` is continuous. -/
theorem continuous_sum_sq (k : ℕ) : Continuous fun x : V (k + 1) => ∑ i, x i ^ 2 := by
  continuity

/-- The unit sphere is closed in `V (k+1)`. -/
theorem isClosed_sphere (k : ℕ) : IsClosed (sphere k) := by
  simpa [sphere] using isClosed_eq (continuous_sum_sq k) continuous_const

/-- The closed unit ball is closed in `V (k+1)`. -/
theorem isClosed_unitSphereBall (k : ℕ) : IsClosed (unitSphereBall k) := by
  simpa [unitSphereBall] using isClosed_le (continuous_sum_sq k) continuous_const

/-! ## Corollary 1.3: strong deformation retraction -/

/-- **Corollary 1.3** (abstract form, subtype version).
If `Y` is a nonempty absolute extensor and `P* ∈ Y`, then `Y` strongly
deformation retracts onto `{P*}`.  This is the deduction on the closed subset
`A = (Y × {0,1}) ∪ ({P*} × ℝ)` of `Y × ℝ`. -/
theorem sdr_of_absoluteExtensor {E : Type*} [MetricSpace E]
    {Y : Set E} (hY : IsAbsoluteExtensor Y) (hne : Y.Nonempty)
    (Pstar : E) (hP : Pstar ∈ Y) :
    ∃ H : ↥Y × ℝ → E,
      Continuous H ∧
      (∀ y : ↥Y, H (y, 0) = y) ∧
      (∀ y : ↥Y, H (y, 1) = Pstar) ∧
      (∀ t, H (⟨Pstar, hP⟩, t) = Pstar) ∧
      (∀ (y : ↥Y) t, H (y, t) ∈ Y) := by
  classical
  let X := ↥Y × ℝ
  let P₀ : ↥Y := ⟨Pstar, hP⟩
  let A : Set X := {p | p.2 = 0 ∨ p.2 = 1 ∨ p.1 = P₀}
  have hA : IsClosed A :=
    (isClosed_eq continuous_snd continuous_const).union
      ((isClosed_eq continuous_snd continuous_const).union
        (isClosed_eq continuous_fst continuous_const))
  let f : A → E := fun p => if p.val.2 = 0 then p.val.1.val else Pstar
  have hfY : ∀ p, f p ∈ Y := by
    intro p
    dsimp [f]
    split_ifs
    · exact p.val.1.property
    · exact hP
  let s₀ : Set A := {p | p.val.2 = 0}
  let s₁ : Set A := {p | p.val.2 = 1}
  let sP : Set A := {p | p.val.1 = P₀}
  have h₀ : IsClosed s₀ := isClosed_eq
    (continuous_snd.comp continuous_subtype_val) continuous_const
  have h₁ : IsClosed s₁ := isClosed_eq
    (continuous_snd.comp continuous_subtype_val) continuous_const
  have hP' : IsClosed sP := isClosed_eq
    (continuous_fst.comp continuous_subtype_val) continuous_const
  have hc₀ : ContinuousOn f s₀ := by
    apply (continuous_subtype_val.comp
      (continuous_fst.comp continuous_subtype_val)).continuousOn.congr
    intro p hp
    exact if_pos hp
  have hc₁ : ContinuousOn f s₁ := by
    apply continuous_const.continuousOn.congr
    intro p hp
    exact if_neg (by dsimp [s₁] at hp; rw [hp]; norm_num)
  have hcP : ContinuousOn f sP := by
    apply continuous_const.continuousOn.congr
    intro p hp
    change (if p.val.2 = 0 then p.val.1.val else Pstar) = Pstar
    have hp' : p.val.1.val = Pstar := congrArg Subtype.val hp
    simp [hp']
  have hcover : s₀ ∪ (s₁ ∪ sP) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro p
    exact p.property
  have hf : Continuous f := continuousOn_univ.mp
    (hcover ▸ hc₀.union_of_isClosed (hc₁.union_of_isClosed hcP h₁ hP') h₀ (h₁.union hP'))
  obtain ⟨H, hHc, hHY, hHeq⟩ := hY X A hA f hf hfY
  refine ⟨H, hHc, ?_, ?_, ?_, fun y t => hHY (y,t)⟩
  · intro y
    exact (hHeq ⟨(y, 0), Or.inl rfl⟩).trans (by simp [f])
  · intro y
    exact (hHeq ⟨(y, 1), Or.inr (Or.inl rfl)⟩).trans (by simp [f])
  · intro t
    exact (hHeq ⟨(P₀, t), Or.inr (Or.inr rfl)⟩).trans (by simp [f, P₀])

/-- Path connectedness of an absolute extensor with a point. -/
theorem pathConnected_of_absoluteExtensor {E : Type*} [MetricSpace E]
    {Y : Set E} (hY : IsAbsoluteExtensor Y) (hne : Y.Nonempty) :
    IsPathConnected Y := by
  obtain ⟨Pstar, hP⟩ := hne
  obtain ⟨H, hHc, h0, h1, hs, hYmem⟩ :=
    sdr_of_absoluteExtensor hY ⟨Pstar, hP⟩ Pstar hP
  refine ⟨Pstar, hP, ?_⟩
  intro y hy
  -- The path t ↦ H(⟨y,hy⟩, 1-t) runs from P* to y, with values in Y.
  refine ⟨Path.ofLine (f := fun t => H (⟨y, hy⟩, 1 - t)) ?_ ?_ ?_, ?_⟩
  · exact (hHc.comp (continuous_const.prodMk (continuous_const.sub continuous_id))).continuousOn
  · simp [h1 ⟨y, hy⟩]
  · simp [h0 ⟨y, hy⟩]
  · intro t
    exact hYmem ⟨y, hy⟩ (1 - t)

/-- An absolute extensor with a point is contractible, in Mathlib's actual
homotopy-equivalence sense. -/
theorem contractible_of_absoluteExtensor {E : Type*} [MetricSpace E]
    {Y : Set E} (hY : IsAbsoluteExtensor Y) (hne : Y.Nonempty) :
    ContractibleSpace ↥Y := by
  obtain ⟨Pstar, hP⟩ := hne
  obtain ⟨H, hHc, h0, h1, hs, hYmem⟩ :=
    sdr_of_absoluteExtensor hY ⟨Pstar, hP⟩ Pstar hP
  apply (contractible_iff_id_nullhomotopic ↥Y).mpr
  refine ⟨⟨Pstar, hP⟩, ⟨{
    toFun := fun p => ⟨H (p.2, (p.1 : ℝ)), hYmem p.2 _⟩
    continuous_toFun := (hHc.comp (continuous_snd.prodMk
      (continuous_subtype_val.comp continuous_fst))).subtype_mk _
    map_zero_left := ?_
    map_one_left := ?_ }⟩⟩
  · intro y
    apply Subtype.ext
    exact h0 y
  · intro y
    apply Subtype.ext
    exact h1 y

/-! ## Corollary 4.1: filling spheres -/

/-- **Corollary 4.1**.
If `Y` is an absolute extensor then every continuous map from `S^k` into `Y`
extends to `B^{k+1}`. -/
theorem fill_sphere_of_absoluteExtensor {E : Type u} [TopologicalSpace E]
    {Y : Set E} (hY : IsAbsoluteExtensor Y) (k : ℕ)
    (f : sphere k → E) (hf : Continuous f) (hmem : ∀ x, f x ∈ Y) :
    ∃ F : unitSphereBall k → E, Continuous F ∧ (∀ x, F x ∈ Y) ∧
      (∀ x : sphere k, F ⟨x, sphere_subset_unitSphereBall k x.2⟩ = f x) := by
  let e : ULift.{u} (V (k + 1)) ≃ₜ V (k + 1) := Homeomorph.ulift
  let A := e ⁻¹' sphere k
  have hA : IsClosed A := (isClosed_sphere k).preimage e.continuous
  let fA : A → E := fun x => f ⟨e x, x.property⟩
  have hfA : Continuous fA := hf.comp
    ((e.continuous.comp continuous_subtype_val).subtype_mk _)
  obtain ⟨G, hGc, hGY, hGeq⟩ := hY (ULift.{u} (V (k + 1))) A hA fA hfA
    (fun x => hmem ⟨e x, x.property⟩)
  refine ⟨fun x => G (e.symm x),
    hGc.comp (e.symm.continuous.comp continuous_subtype_val),
    fun x => hGY _, ?_⟩
  intro x
  simpa [fA, A] using hGeq ⟨e.symm x, by simpa [A] using x.property⟩

end Paper17
