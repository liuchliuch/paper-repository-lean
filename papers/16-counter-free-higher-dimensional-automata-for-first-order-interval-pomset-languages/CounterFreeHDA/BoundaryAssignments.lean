import CounterFreeHDA.TypedCorners
import CounterFreeHDA.PersistentPowers

namespace CounterFreeHDA.Status

theorem le_star_of_ne_one (a : Status) (h : a ≠ Status.one) : a ≤ Status.star := by
  have hn : a.val ≠ 2 := fun he => h (Fin.ext he)
  have hb := a.isLt
  change a.val ≤ 1
  omega

theorem star_le_of_ne_zero (a : Status) (h : a ≠ Status.zero) : Status.star ≤ a := by
  have hn : a.val ≠ 0 := fun he => h (Fin.ext he)
  change 1 ≤ a.val
  omega

end CounterFreeHDA.Status

namespace CounterFreeHDA.EndoPom
universe u
open Cubical
variable {Lab : Type u} {k : ℕ} {U A B : Cube Lab k}

def StableCompatible (P : EndoPom (cubeInterface U)) (α : Cubical.Face A U) (β : Cubical.Face B U) : Prop :=
  ∀ i, P.Shared i i → α.status i ≤ β.status i

noncomputable def boundaryDeleted (P : EndoPom (cubeInterface U)) (α : Cubical.Face A U) (β : Cubical.Face B U) :
    Finset (Fin U.dim) := by
  classical
  exact Finset.univ.filter (fun i => P.Shared i i ∧ (α.status i = Status.one ∨ β.status i = Status.zero))

theorem boundaryDeleted_persistent (P : EndoPom (cubeInterface U)) (α : Cubical.Face A U) (β : Cubical.Face B U) :
    P.PersistentSet (P.boundaryDeleted α β) := by
  classical
  intro i hi
  exact (Finset.mem_filter.mp hi).2.1

noncomputable def boundaryStatus (P : EndoPom (cubeInterface U)) (α : Cubical.Face A U) (β : Cubical.Face B U)
    (i : Fin U.dim) : Status :=
  if i ∈ P.boundaryDeleted α β then if α.status i = Status.one then Status.one else Status.zero else Status.star

noncomputable def boundaryFace (P : EndoPom (cubeInterface U)) (α : Cubical.Face A U) (β : Cubical.Face B U) :
    Cubical.Face (Cubical.Face.activeCube U (P.boundaryStatus α β)) U := Cubical.Face.ofStatuses U (P.boundaryStatus α β)

theorem boundaryStatus_star (P : EndoPom (cubeInterface U)) (α : Cubical.Face A U) (β : Cubical.Face B U) (i : Fin U.dim) :
    P.boundaryStatus α β i = Status.star ↔ i ∉ P.boundaryDeleted α β := by
  constructor
  · intro hs hi
    have hn : P.boundaryStatus α β i ≠ Status.star := by
      unfold boundaryStatus
      rw [if_pos hi]
      split_ifs <;> decide
    exact hn hs
  · intro hi
    unfold boundaryStatus
    rw [if_neg hi]

theorem source_le_boundary (P : EndoPom (cubeInterface U)) (α : Cubical.Face A U) (β : Cubical.Face B U)
    (hc : P.StableCompatible α β) (i : Fin U.dim) (hi : P.Shared i i) :
    α.status i ≤ P.boundaryStatus α β i := by
  classical
  by_cases hα : α.status i = Status.one
  · have hm : i ∈ P.boundaryDeleted α β := Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi,Or.inl hα⟩
    simp only [boundaryStatus,if_pos hm,if_pos hα,hα]
    exact le_refl _
  by_cases hβ : β.status i = Status.zero
  · have hm : i ∈ P.boundaryDeleted α β := Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi,Or.inr hβ⟩
    simpa only [boundaryStatus,if_pos hm,if_neg hα,hβ] using hc i hi
  · have hm : i ∉ P.boundaryDeleted α β := by
      intro h
      exact (Finset.mem_filter.mp h).2.2.elim hα hβ
    simpa only [boundaryStatus,if_neg hm] using Status.le_star_of_ne_one (α.status i) hα

theorem boundary_le_target (P : EndoPom (cubeInterface U)) (α : Cubical.Face A U) (β : Cubical.Face B U)
    (hc : P.StableCompatible α β) (i : Fin U.dim) (hi : P.Shared i i) :
    P.boundaryStatus α β i ≤ β.status i := by
  classical
  by_cases hα : α.status i = Status.one
  · have hm : i ∈ P.boundaryDeleted α β := Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi,Or.inl hα⟩
    simpa only [boundaryStatus,if_pos hm,if_pos hα,hα] using hc i hi
  by_cases hβ : β.status i = Status.zero
  · have hm : i ∈ P.boundaryDeleted α β := Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi,Or.inr hβ⟩
    simp only [boundaryStatus,if_pos hm,if_neg hα,hβ]
    exact le_refl _
  · have hm : i ∉ P.boundaryDeleted α β := by
      intro h
      exact (Finset.mem_filter.mp h).2.2.elim hα hβ
    simpa only [boundaryStatus,if_neg hm] using Status.star_le_of_ne_zero (β.status i) hβ

theorem boundary_middle_compatible (P : EndoPom (cubeInterface U)) (α : Cubical.Face A U) (β : Cubical.Face B U)
    (hw : P.pom.val.WidthLE k) (n : ℕ) :
    (P.boundedPower hw n).toArrow.Compatible (P.boundaryFace α β) (P.boundaryFace α β) := by
  intro i j hij
  change (P.pow n).Shared i j at hij
  change (P.boundaryFace α β).status i ≤ (P.boundaryFace α β).status j
  simp only [boundaryFace,Cubical.Face.ofStatuses_status]
  by_cases hi : i ∈ P.boundaryDeleted α β
  · have hii := P.persistent_pow n i (P.boundaryDeleted_persistent α β i hi)
    have hji := shared_target_unique (P.pow n) hij hii
    subst j
    exact le_refl _
  by_cases hj : j ∈ P.boundaryDeleted α β
  · have hjj := P.persistent_pow n j (P.boundaryDeleted_persistent α β j hj)
    have he := (P.pow n).pom.val.src_inj (hij.trans hjj.symm)
    have hij' : i = j := Fin.ext (congrArg (fun a : Fin (P.pow n).pom.srcLen => a.val) he)
    subst j
    exact le_refl _
  · simp only [boundaryStatus,if_neg hi,if_neg hj]
    exact le_refl _

/-- The two fixed outside corners are compatible once their k-copy
interface histories have stabilized. -/
theorem boundary_left_compatible (P : EndoPom (cubeInterface U)) (α : Cubical.Face A U) (β : Cubical.Face B U)
    (hc : P.StableCompatible α β) (hw : P.pom.val.WidthLE k) {n : ℕ} (hn : k ≤ n) :
    (P.boundedPower hw n).toArrow.Compatible α (P.boundaryFace α β) := by
  intro i j hij
  change (P.pow n).Shared i j at hij
  obtain ⟨hij,hi⟩ := (P.lemma_4_1_actual (Nat.le_of_lt_succ U.1.isLt) hn i j).mp hij
  subst j
  exact (P.source_le_boundary α β hc i hi).trans_eq (Cubical.Face.ofStatuses_status U (P.boundaryStatus α β) i).symm

theorem boundary_right_compatible (P : EndoPom (cubeInterface U)) (α : Cubical.Face A U) (β : Cubical.Face B U)
    (hc : P.StableCompatible α β) (hw : P.pom.val.WidthLE k) {n : ℕ} (hn : k ≤ n) :
    (P.boundedPower hw n).toArrow.Compatible (P.boundaryFace α β) β := by
  intro i j hij
  change (P.pow n).Shared i j at hij
  obtain ⟨hij,hi⟩ := (P.lemma_4_1_actual (Nat.le_of_lt_succ U.1.isLt) hn i j).mp hij
  subst j
  exact (Cubical.Face.ofStatuses_status U (P.boundaryStatus α β) i).le.trans (P.boundary_le_target α β hc i hi)

end CounterFreeHDA.EndoPom
