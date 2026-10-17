import Paper29.TwoBatchOutput
import Paper29.QueryModel

noncomputable section
open scoped BigOperators Classical
namespace Paper29.ProcessTools

/-- Preselected union of both batches; repeated draws reuse a queried label. -/
def batchQueries {n m₀ m : ℕ} (ω : (Fin m₀ → Fin n) × (Fin m → Fin n)) : Finset (Fin n) :=
  Finset.univ.image ω.1 ∪ Finset.univ.image ω.2

theorem batchQueries_card_le {n m₀ m : ℕ} (ω : (Fin m₀ → Fin n) × (Fin m → Fin n)) :
    (batchQueries ω).card ≤ min n (m₀+m) := by
  apply le_min
  · exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
  · exact (Finset.card_union_le _ _).trans (add_le_add
      ((Finset.card_image_le).trans_eq (by simp)) ((Finset.card_image_le).trans_eq (by simp)))

theorem importanceWeights_zero_of_unsampled {n m : ℕ} (π : Fin n → ℝ)
    (ν : Fin m → Fin n) (i : Fin n) (hi : i ∉ Finset.univ.image ν) :
    Sampling.importanceWeights π ν i = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  have hj : ν j ≠ i := by intro h; exact hi (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,h⟩)
  simp [hj]

/-- The actual chosen pilot vector ignores every unsampled label. -/
theorem pilotCenter_eq_of_samples_eq {n d m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (b c π : Fin n → ℝ) (hp : ∀ i, 0 ≤ π i) (ν : Fin m → Fin n)
    (hbc : ∀ j, b (ν j) = c (ν j)) : pilotCenter A b π hp ν = pilotCenter A c π hp ν := by
  apply congrArg WithLp.ofLp
  apply Attainment.minimumNormSelection_observed_labels_only
  intro i hi
  by_contra hne
  apply hi
  apply importanceWeights_zero_of_unsampled
  intro hm
  obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hm
  subst i
  exact hne (hbc j)

theorem twoBatchOutput_eq_of_observed_labels {n d m₀ m : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (b c π₀ π : Fin n → ℝ)
    (hp₀ : ∀ i, 0 ≤ π₀ i) (hp : ∀ i, 0 ≤ π i)
    (ω : (Fin m₀ → Fin n) × (Fin m → Fin n))
    (hbc : ∀ i ∈ batchQueries ω, b i = c i) :
    twoBatchOutput A b π₀ π hp₀ hp ω = twoBatchOutput A c π₀ π hp₀ hp ω := by
  have hc : pilotCenter A b π₀ hp₀ ω.1 = pilotCenter A c π₀ hp₀ ω.1 :=
    pilotCenter_eq_of_samples_eq A b c π₀ hp₀ ω.1 (fun j => hbc _
      (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)))
  unfold twoBatchOutput
  rw [hc]
  congr 1
  apply pilotCenter_eq_of_samples_eq
  intro j
  unfold pilotResidual
  rw [hc, hbc _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩))]

/-- Arbitrary extension of observed labels; output invariance proves that these
filler labels have no effect. -/
def extendLabels {n : ℕ} (q : Finset (Fin n)) (labels : {i // i ∈ q} → ℝ) (i : Fin n) : ℝ :=
  if hi : i ∈ q then labels ⟨i,hi⟩ else 0

def batchProcedure {n d m₀ m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (π₀ π : Fin n → ℝ) (hp₀ : ∀ i, 0 ≤ π₀ i) (hp : ∀ i, 0 ≤ π i) :
    QueryModel.NonadaptiveProcedure ((Fin m₀ → Fin n) × (Fin m → Fin n)) n d where
  queried := batchQueries
  output := fun ω labels => twoBatchOutput A (extendLabels (batchQueries ω) labels) π₀ π hp₀ hp ω

theorem batchProcedure_answer {n d m₀ m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (b π₀ π : Fin n → ℝ) (hp₀ : ∀ i, 0 ≤ π₀ i) (hp : ∀ i, 0 ≤ π i)
    (ω : (Fin m₀ → Fin n) × (Fin m → Fin n)) :
    (batchProcedure (m₀:=m₀) (m:=m) A π₀ π hp₀ hp).answer ω b =
      twoBatchOutput A b π₀ π hp₀ hp ω := by
  apply twoBatchOutput_eq_of_observed_labels
  intro i hi
  simp [extendLabels, hi]

end Paper29.ProcessTools
