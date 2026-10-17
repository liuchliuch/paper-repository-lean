import Mathlib.Topology.Semicontinuous
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-! The actual finite incident-piece upper envelope used in the sharp
polyhedral approximation. Closed incidence and continuity imply upper
semicontinuity; equality on every incident tangent gives the exact value. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
variable {X J : Type*} [TopologicalSpace X] [Fintype J]

def incidentValues (pieces : J → Set X) (jac : J → X → ℝ) (x : X) : Finset ℝ := by
  classical
  exact insert 0 ((Finset.univ.filter (fun j => x ∈ pieces j)).image (fun j => jac j x))

def incidentEnvelope (pieces : J → Set X) (jac : J → X → ℝ) (x : X) : ℝ :=
  (incidentValues pieces jac x).max' (by
    classical
    exact Finset.insert_nonempty _ _)

theorem incidentEnvelope_nonneg (pieces : J → Set X) (jac : J → X → ℝ) (x : X) :
    0 ≤ incidentEnvelope pieces jac x := by
  classical
  exact Finset.le_max' _ 0 (by simp [incidentValues])

theorem le_incidentEnvelope (pieces : J → Set X) (jac : J → X → ℝ)
    (x : X) (j : J) (hj : x ∈ pieces j) : jac j x ≤ incidentEnvelope pieces jac x := by
  classical
  exact Finset.le_max' _ _ (by simp only [incidentValues,Finset.mem_insert,Finset.mem_image,
    Finset.mem_filter,Finset.mem_univ,true_and]; exact Or.inr ⟨j,hj,rfl⟩)

theorem incidentEnvelope_le (pieces : J → Set X) (jac : J → X → ℝ)
    (x : X) (a : ℝ) (ha : 0 ≤ a) (h : ∀ j, x ∈ pieces j → jac j x ≤ a) :
    incidentEnvelope pieces jac x ≤ a := by
  classical
  apply Finset.max'_le
  intro y hy
  rcases Finset.mem_insert.mp hy with rfl | hy
  · exact ha
  · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hy
    exact h j (Finset.mem_filter.mp hj).2

theorem incidentEnvelope_eq (pieces : J → Set X) (jac : J → X → ℝ)
    (x : X) (a : ℝ) (ha : 0 ≤ a) (hSome : ∃ j, x ∈ pieces j)
    (h : ∀ j, x ∈ pieces j → jac j x = a) : incidentEnvelope pieces jac x = a := by
  apply le_antisymm (incidentEnvelope_le pieces jac x a ha (fun j hj => (h j hj).le))
  obtain ⟨j,hj⟩ := hSome
  exact (h j hj).symm.le.trans (le_incidentEnvelope pieces jac x j hj)

theorem incidentEnvelope_upperSemicontinuous (pieces : J → Set X) (jac : J → X → ℝ)
    (hClosed : ∀ j, IsClosed (pieces j)) (hJac : ∀ j, ContinuousOn (jac j) (pieces j)) :
    UpperSemicontinuous (incidentEnvelope pieces jac) := by
  classical
  rw [upperSemicontinuous_iff_isClosed_preimage]
  intro a
  by_cases ha : a ≤ 0
  · have he : incidentEnvelope pieces jac ⁻¹' Ici a = univ := by
      ext x
      simp only [mem_preimage,mem_Ici,mem_univ,iff_true]
      exact ha.trans (incidentEnvelope_nonneg pieces jac x)
    rw [he]
    exact isClosed_univ
  · have ha' : 0 < a := lt_of_not_ge ha
    have he : incidentEnvelope pieces jac ⁻¹' Ici a = ⋃ j, pieces j ∩ (jac j ⁻¹' Ici a) := by
      ext x
      constructor
      · intro hx
        have hm := (incidentValues pieces jac x).max'_mem (by exact Finset.insert_nonempty _ _)
        rcases Finset.mem_insert.mp hm with hz | hm
        · have hzero : incidentEnvelope pieces jac x = 0 := hz
          exact False.elim (by change a ≤ incidentEnvelope pieces jac x at hx; rw [hzero] at hx; linarith)
        · obtain ⟨j,hj,heq⟩ := Finset.mem_image.mp hm
          refine mem_iUnion.mpr ⟨j,(Finset.mem_filter.mp hj).2,?_⟩
          change a ≤ jac j x
          rw [heq]
          exact hx
      · intro hx
        obtain ⟨j,hj,hax⟩ := mem_iUnion.mp hx
        exact hax.trans (le_incidentEnvelope pieces jac x j hj)
    rw [he]
    exact isClosed_iUnion_of_finite (fun j =>
      (hJac j).preimage_isClosed_of_isClosed (hClosed j) isClosed_Ici)

end Paper28
