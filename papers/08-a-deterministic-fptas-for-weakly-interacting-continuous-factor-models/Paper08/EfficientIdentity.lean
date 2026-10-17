import Paper08.EfficientSupports
import Paper08.ModelSupport
import Paper08.FPTASAlgorithm

/-!
# Actual logarithmic coefficients on executable support candidates

The forest decoder may return additional disconnected candidates. Their
actual support coefficients vanish, so replacing the global powerset by
the executable candidate set preserves every coefficient. We then flatten
exactly the support/subset pairs and all retained coefficient orders.
-/

noncomputable section
open scoped BigOperators
open Finset

namespace Paper08.EfficientIdentity

/-- The executable candidates give the exact connected-support coefficient
identity even when they include additional disconnected sets. -/
theorem candidate_support_identity {n r m d s p : ℕ} (E : FactorFamily n r m)
    (N : Fin m → Finset (Fin m)) (hdeg : ∀ u, (N u).card ≤ d)
    (hN : ∀ u v, (Interaction.graph E).Adj u v → v ∈ N u) (hp : p ≤ s) :
    ModelSupport.logCoeff E Finset.univ p =
      ∑ A ∈ (EfficientSupports.supports N d s).filter (fun A => A.card ≤ p),
        ∑ B ∈ A.powerset, (-1 : ℝ) ^ (A.card - B.card) * ModelSupport.logCoeff E B p := by
  classical
  let C := (EfficientSupports.supports N d s).filter (fun A => A.card ≤ p)
  have hsub : C ⊆ (Finset.univ : Finset (Fin m)).powerset := by
    intro A _
    exact Finset.mem_powerset.mpr (Finset.subset_univ A)
  have hzero : ∀ A ∈ (Finset.univ : Finset (Fin m)).powerset, A ∉ C →
      ModelSupport.supportCoeff E A p = 0 := by
    intro A _ hnot
    by_cases hne : A.Nonempty
    · by_cases hcard : A.card ≤ p
      · by_cases hconn : ((Interaction.graph E).induce (A : Set (Fin m))).Connected
        · have hA := EfficientSupports.contains_connected N (Interaction.graph E)
            hdeg hN A hne (hcard.trans hp) hconn
          exact (hnot (Finset.mem_filter.mpr ⟨hA, hcard⟩)).elim
        · exact ModelSupport.supportCoeff_eq_zero_of_disconnected E A hne hconn p
      · exact ModelSupport.supportCoeff_eq_zero_of_card E A p (by omega)
    · have hA : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst A
      exact ModelSupport.supportCoeff_empty E p
  calc
    ModelSupport.logCoeff E Finset.univ p =
        ∑ A ∈ (Finset.univ : Finset (Fin m)).powerset, ModelSupport.supportCoeff E A p :=
      (ModelSupport.sum_supportCoeff E p).symm
    _ = ∑ A ∈ C, ModelSupport.supportCoeff E A p := (Finset.sum_subset hsub hzero).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro A _
      exact ModelSupport.supportCoeff_eq_mobius E A p

/-- Flattening the executable support/subset pairs preserves the nested sum.
The first coordinate of a pair makes the images for different supports disjoint. -/
theorem sum_supportPairs_eq {m d s p : ℕ} (N : Fin m → Finset (Fin m))
    (f : Finset (Fin m) × Finset (Fin m) → ℝ) :
    (∑ AB ∈ (EfficientSupports.supportPairs N d s).filter (fun AB => AB.1.card ≤ p), f AB) =
      ∑ A ∈ (EfficientSupports.supports N d s).filter (fun A => A.card ≤ p),
        ∑ B ∈ A.powerset, f (A, B) := by
  classical
  let C := (EfficientSupports.supports N d s).filter (fun A => A.card ≤ p)
  have hpair : (EfficientSupports.supportPairs N d s).filter (fun AB => AB.1.card ≤ p) =
      C.biUnion (fun A => A.powerset.image (fun B => (A, B))) := by
    ext AB
    rcases AB with ⟨A, B⟩
    simp only [Finset.mem_filter, EfficientSupports.mem_supportPairs, Finset.mem_biUnion,
      Finset.mem_image, Prod.mk.injEq, Finset.mem_powerset, C]
    aesop
  have hdisj : ∀ A ∈ C, ∀ D ∈ C, A ≠ D →
      Disjoint (A.powerset.image (fun B => (A, B))) (D.powerset.image (fun B => (D, B))) := by
    intro A _ D _ hAD
    apply Finset.disjoint_left.mpr
    intro AB hA hD
    obtain ⟨B, _, hB⟩ := Finset.mem_image.mp hA
    obtain ⟨F, _, hF⟩ := Finset.mem_image.mp hD
    exact hAD (congrArg Prod.fst (hB.trans hF.symm))
  rw [hpair, Finset.sum_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro A _
  rw [Finset.sum_image]
  intro B _ D _ hBD
  exact (Prod.mk.inj hBD).2

/-- Each local coefficient equals the exact flat pair sum evaluated by the
program, over the efficiently generated support pairs only. -/
theorem supportPairs_identity {n r m d s p : ℕ} (E : FactorFamily n r m)
    (N : Fin m → Finset (Fin m)) (hdeg : ∀ u, (N u).card ≤ d)
    (hN : ∀ u v, (Interaction.graph E).Adj u v → v ∈ N u) (hp : p ≤ s) :
    ModelSupport.logCoeff E Finset.univ p =
      ∑ AB ∈ (EfficientSupports.supportPairs N d s).filter (fun AB => AB.1.card ≤ p),
        (-1 : ℝ) ^ (AB.1.card - AB.2.card) * ModelSupport.logCoeff E AB.2 p := by
  rw [sum_supportPairs_eq]
  exact candidate_support_identity E N hdeg hN hp

/-- All coefficient-order/support/subset occurrences actually used in the
retained Taylor polynomial, without enumeration of the global powerset. -/
def occurrences {m : ℕ} (N : Fin m → Finset (Fin m)) (d s : ℕ) :
    Finset (ℕ × (Finset (Fin m) × Finset (Fin m))) :=
  ((Finset.Icc 1 s).product (EfficientSupports.supportPairs N d s)).filter
    (fun o => o.2.1.card ≤ o.1)

/-- The entire retained logarithmic Taylor polynomial equals the flat
occurrence sum corresponding to the executable program. -/
theorem occurrences_identity {n r m d s : ℕ} (E : FactorFamily n r m)
    (N : Fin m → Finset (Fin m)) (hdeg : ∀ u, (N u).card ≤ d)
    (hN : ∀ u v, (Interaction.graph E).Adj u v → v ∈ N u) :
    (∑ p ∈ Finset.Icc 1 s, ModelSupport.logCoeff E Finset.univ p) =
      ∑ o ∈ occurrences N d s,
        (-1 : ℝ) ^ (o.2.1.card - o.2.2.card) * ModelSupport.logCoeff E o.2.2 o.1 := by
  classical
  calc
    (∑ p ∈ Finset.Icc 1 s, ModelSupport.logCoeff E Finset.univ p) =
        ∑ p ∈ Finset.Icc 1 s,
          ∑ AB ∈ (EfficientSupports.supportPairs N d s).filter (fun AB => AB.1.card ≤ p),
            (-1 : ℝ) ^ (AB.1.card - AB.2.card) * ModelSupport.logCoeff E AB.2 p := by
      apply Finset.sum_congr rfl
      intro p hp
      exact supportPairs_identity E N hdeg hN (Finset.mem_Icc.mp hp).2
    _ = _ := by
      simp only [occurrences, Finset.product_eq_sprod, Finset.sum_filter, Finset.sum_product]

/-- The actual flat coefficient occurrences satisfy the order-exponential
bound used to allocate moment precision. -/
theorem occurrences_count {m d s : ℕ} (N : Fin m → Finset (Fin m)) (hd : 1 ≤ d) :
    (occurrences N d s).card ≤ s * m * (8 * d) ^ s := by
  calc
    (occurrences N d s).card ≤
        ((Finset.Icc 1 s).product (EfficientSupports.supportPairs N d s)).card :=
      Finset.card_filter_le _ _
    _ = s * (EfficientSupports.supportPairs N d s).card := by
      rw [Finset.product_eq_sprod, Finset.card_product]
      simp
    _ ≤ s * (m * (8 * d) ^ s) :=
      Nat.mul_le_mul_left s (EfficientSupports.supportPairs_count N hd)
    _ = s * m * (8 * d) ^ s := by ring

/-- The exact flat identity for the neighbor lists and pair enumeration
used by the executable FPTAS program. -/
theorem factor_pairs_identity {n r m c s p : ℕ} (E : FactorFamily n r m)
    (hc : FamilyBoundedOccurrence E c) (hp : p ≤ s) :
    ModelSupport.logCoeff E Finset.univ p =
      ∑ AB ∈ FPTASAlgorithm.pairs (fun e => (E e).scope) r c s p,
        (-1 : ℝ) ^ (AB.1.card - AB.2.card) * ModelSupport.logCoeff E AB.2 p := by
  apply supportPairs_identity E _ (FPTASAlgorithm.neighbors_degree E hc) ?_ hp
  intro u v huv
  rw [FPTASAlgorithm.neighbors_eq]
  simpa only [SimpleGraph.mem_neighborFinset] using huv

/-- All retained orders for the actual executable factor-neighbor lists. -/
theorem factor_occurrences_identity {n r m c s : ℕ} (E : FactorFamily n r m)
    (hc : FamilyBoundedOccurrence E c) :
    (∑ p ∈ Finset.Icc 1 s, ModelSupport.logCoeff E Finset.univ p) =
      ∑ o ∈ occurrences (FPTASAlgorithm.neighbors (fun e => (E e).scope))
          (FPTASAlgorithm.degreeBound r c) s,
        (-1 : ℝ) ^ (o.2.1.card - o.2.2.card) * ModelSupport.logCoeff E o.2.2 o.1 := by
  apply occurrences_identity E _ (FPTASAlgorithm.neighbors_degree E hc)
  intro u v huv
  rw [FPTASAlgorithm.neighbors_eq]
  simpa only [SimpleGraph.mem_neighborFinset] using huv

/-- The actual program's coefficient-order occurrences obey the same
polynomial-budget count, using `max 1` for isolated factor graphs. -/
theorem factor_occurrences_count {n r m c s : ℕ} (E : FactorFamily n r m) :
    (occurrences (FPTASAlgorithm.neighbors (fun e => (E e).scope))
      (FPTASAlgorithm.degreeBound r c) s).card ≤
      s * m * (8 * FPTASAlgorithm.degreeBound r c) ^ s :=
  occurrences_count _ (le_max_left _ _)


end Paper08.EfficientIdentity
