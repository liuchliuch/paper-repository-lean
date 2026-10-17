import MEJF.Setup
import Mathlib.Data.Finset.Image

/-! Equivariance of the actual multiset-learner endpoint rule (4.5). -/
namespace MEJF.SetupEquivariance
open MEJF.Setup MEJF.Exchangeability Finset
noncomputable section
attribute [local instance] Classical.propDecidable

variable {X : Type*} [MeasurableSpace X] {N m n : ℕ}

lemma training_relabel (Z : Fin N → Block X n) (e : Equiv.Perm (Fin N)) (i k : Fin N) :
    (((univ.erase (e i)).erase (e k)).val.map (relabel e Z)) =
      (((univ.erase i).erase k).val.map Z) := by
  have hs : (((univ.erase (e i)).erase (e k)).map e.symm.toEmbedding) =
      (univ.erase i).erase k := by simp
  have hh := congrArg (fun s : Finset (Fin N) => s.val.map Z) hs
  simpa only [Finset.map_val, Multiset.map_map, Equiv.coe_toEmbedding,
    Function.comp_def, relabel] using hh

lemma pairPrediction_relabel (A : Learner X n) (Z : Fin N → Block X n)
    (e : Equiv.Perm (Fin N)) (i k : Fin N) (x : X) :
    pairPrediction A (relabel e Z) (e i) (e k) x = pairPrediction A Z i k x := by
  unfold pairPrediction
  rw [training_relabel]

lemma radius_relabel (A : Learner X n) (Z : Fin N → Block X n)
    (e : Equiv.Perm (Fin N)) (i k : Fin N) (t : ℕ) (ht : 1 ≤ t ∧ t ≤ n) :
    radius A (relabel e Z) (e i) (e k) t ht = radius A Z i k t ht := by
  unfold radius
  congr 1
  funext j
  have hZi : relabel e Z (e i) = Z i := by simp [relabel]
  simp only [hZi]
  rw [pairPrediction_relabel]

/-- The canonical enumeration of all labels other than the pivot. -/
def otherEquiv (i : Fin (m+1)) : Fin m ≃ {k : Fin (m+1) // k ≠ i} :=
  Equiv.ofBijective (fun k => ⟨i.succAbove k, Fin.succAbove_ne i k⟩) ⟨
    fun k l h => Fin.succAbove_right_injective (congrArg Subtype.val h),
    fun k => by
      obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq k.property
      exact ⟨l, Subtype.ext hl⟩⟩

/-- Relabeling induces an actual permutation of the other-label indices. -/
def otherPerm (e : Equiv.Perm (Fin (m+1))) (i : Fin (m+1)) : Equiv.Perm (Fin m) :=
  ((otherEquiv i).trans (Equiv.subtypeEquiv e (by
    intro k
    exact not_congr (e.injective.eq_iff.symm)))).trans (otherEquiv (e i)).symm

lemma otherPerm_spec (e : Equiv.Perm (Fin (m+1))) (i : Fin (m+1)) (k : Fin m) :
    (e i).succAbove (otherPerm e i k) = e (i.succAbove k) := by
  have h := (otherEquiv (e i)).apply_symm_apply
    ((Equiv.subtypeEquiv e (by intro k; exact not_congr e.injective.eq_iff.symm)) (otherEquiv i k))
  exact congrArg Subtype.val h

lemma lowerEndpoint_relabel (A : Learner X n) (Z : Fin (m+1) → Block X n)
    (e : Equiv.Perm (Fin (m+1))) (i : Fin (m+1)) (j : Fin n)
    (t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    lowerEndpoint A (relabel e Z) (e i) j t ell ht he =
      lowerEndpoint A Z i j t ell ht he := by
  unfold lowerEndpoint
  rw [← OrderStatistics.stat_perm _ (otherPerm e i)]
  apply congrArg (fun u : Fin m → ℝ => OrderStatistics.stat u (lowerIndex m ell he))
  funext k
  simp only [Function.comp_apply, otherPerm_spec]
  rw [radius_relabel]
  have hZi : relabel e Z (e i) = Z i := by simp [relabel]
  simp only [hZi]
  rw [pairPrediction_relabel]

lemma upperEndpoint_relabel (A : Learner X n) (Z : Fin (m+1) → Block X n)
    (e : Equiv.Perm (Fin (m+1))) (i : Fin (m+1)) (j : Fin n)
    (t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    upperEndpoint A (relabel e Z) (e i) j t ell ht he =
      upperEndpoint A Z i j t ell ht he := by
  unfold upperEndpoint
  rw [← OrderStatistics.stat_perm _ (otherPerm e i)]
  apply congrArg (fun u : Fin m → ℝ => OrderStatistics.stat u (upperIndex m ell he))
  funext k
  simp only [Function.comp_apply, otherPerm_spec]
  rw [radius_relabel]
  have hZi : relabel e Z (e i) = Z i := by simp [relabel]
  simp only [hZi]
  rw [pairPrediction_relabel]

lemma covered_relabel (A : Learner X n) (Z : Fin (m+1) → Block X n)
    (e : Equiv.Perm (Fin (m+1))) (i : Fin (m+1)) (j : Fin n)
    (t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    covered A (relabel e Z) (e i) j t ell ht he ↔ covered A Z i j t ell ht he := by
  unfold covered
  rw [lowerEndpoint_relabel, upperEndpoint_relabel]
  simp only [relabel, Function.comp_apply, Equiv.symm_apply_apply]

theorem failure_equivariant (A : Learner X n) (F t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    Equivariant (fun Z : Fin (m+1) → Block X n => fun i => Setup.failure A Z i F t ell ht he) := by
  intro e Z i
  unfold Setup.failure
  simp only [covered_relabel]

end
end MEJF.SetupEquivariance
