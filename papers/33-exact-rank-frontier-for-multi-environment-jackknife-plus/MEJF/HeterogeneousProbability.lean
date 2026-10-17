import MEJF.HeterogeneousMeasurable
import MEJF.HeterogeneousEquivariance
import MEJF.ConditionalExchangeability
import MEJF.HeterogeneousSharpness
import MEJF.FiniteExchangeable
import MEJF.ActualPareto

/-! Statistical fixed-size-multiset and random-size frontiers on the actual
variable-positive-length block space from §6.1. -/
namespace MEJF.HeterogeneousProbability
open MeasureTheory Finset HeterogeneousSetup Exchangeability HeterogeneousFrontier
open MEJF.HeterogeneousEquivariance
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Countable size multisets carry their discrete sigma algebra. -/
instance sizeMultisetMeasurableSpace : MeasurableSpace (Multiset ℕ) := ⊤
instance sizeMultisetDiscreteMeasurableSpace : DiscreteMeasurableSpace (Multiset ℕ) := ⟨fun _ => trivial⟩
instance sizeMultisetMeasurableSingletonClass : MeasurableSingletonClass (Multiset ℕ) :=
  ⟨fun _ => trivial⟩

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {m : ℕ}

/-- The multiset frontier is evaluated using any indexed representative; the
next theorem proves independence of that choice. -/
def frontierOfMultiset (m : ℕ) (alpha a : ℝ) (ell : ℕ) (M : Multiset ℕ) : ℕ :=
  if h : ∃ v : Fin (m+1) → ℕ, univ.val.map v=M then
    sStar (fun i => sizeDemand m alpha a ell (Classical.choose h i)) else 0

lemma frontierOfMultiset_eq (m : ℕ) (alpha a : ℝ) (ell : ℕ) (v : Fin (m+1) → ℕ) :
    frontierOfMultiset m alpha a ell (univ.val.map v) =
      sStar (fun i => sizeDemand m alpha a ell (v i)) := by
  unfold frontierOfMultiset
  rw [dif_pos ⟨v,rfl⟩]
  apply sStar_eq_of_multiset_eq
  have h := congrArg (Multiset.map (sizeDemand m alpha a ell))
    (Classical.choose_spec (show ∃ w : Fin (m+1) → ℕ, univ.val.map w=univ.val.map v from ⟨v,rfl⟩))
  simpa only [Multiset.map_map,Function.comp_def] using h

lemma sStar_le_card {N : ℕ} (w : Fin N → ℕ) : sStar w ≤ N := by
  obtain ⟨S,hS,_⟩ := sStar_attained w
  rw [← hS]
  simpa using card_le_univ S

lemma frontierOfMultiset_le (m : ℕ) (alpha a : ℝ) (ell : ℕ) (M : Multiset ℕ) :
    frontierOfMultiset m alpha a ell M ≤ m+1 := by
  unfold frontierOfMultiset
  split_ifs
  · exact sStar_le_card _
  · omega

lemma frontierOfMultiset_realized (alpha a : ℝ) (ell : ℕ)
    (Z : Fin (m+1) → Block X) :
    frontierOfMultiset m alpha a ell (sizeMultiset Z) = realizedFrontier alpha a ell Z :=
  frontierOfMultiset_eq m alpha a ell (fun i => size (Z i))

lemma measurable_sizeMultiset : Measurable (sizeMultiset (X := X) (N := m+1)) := by
  have hh : sizeMultiset (X := X) (N := m+1) =
      (fun ns : Fin (m+1) → ℕ+ => univ.val.map (fun i => (ns i).val)) ∘ sizeVector := rfl
  rw [hh]
  exact (measurable_of_countable _).comp measurable_sizeVector

lemma finiteFailure_count_le (A : Learner X) (alpha a : ℝ) (ell : ℕ)
    (he : 1 ≤ ell ∧ ell ≤ m) (Z : Fin (m+1) → Block X) :
    (univ.filter fun i => finiteFailure A Z alpha a ell he i).card ≤
      frontierOfMultiset m alpha a ell (sizeMultiset Z) := by
  rw [frontierOfMultiset_realized]
  by_cases ht : ∀ k, 1 ≤ innerRank a Z k ∧ innerRank a Z k ≤ size (Z k)
  · have hs : (univ.filter fun i => finiteFailure A Z alpha a ell he i) =
        (univ.filter fun i => learnerFailure A Z (failureRank alpha Z) (innerRank a Z) ht ell he i) := by
      ext i
      simp only [mem_filter,mem_univ,true_and,finiteFailure_iff A Z alpha a ell he i ht]
    rw [hs]
    exact source_failure_count_le_frontier A Z alpha a ell ht he
  · have hs : (univ.filter fun i => finiteFailure A Z alpha a ell he i) = ∅ := by
      ext i
      simp only [mem_filter,mem_univ,true_and,Finset.notMem_empty,iff_false]
      exact fun ⟨h,_⟩ => ht h
    rw [hs,card_empty]
    exact Nat.zero_le _

/-- The canonical conditional probability version for the source unordered size
multiset. Its integral identity below verifies the actual conditional meaning. -/
def conditionalFailure (μ : Measure (Fin (m+1) → Block X)) (A : Learner X)
    (alpha a : ℝ) (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) (i : Fin (m+1)) (M : Multiset ℕ) : ℝ :=
  ConditionalExchangeability.conditionalRatio μ
    (fun Z i => finiteFailure A Z alpha a ell he i) sizeMultiset i M

/-- Equation (6.12), conditional upper bound on every size cell, including
zero-mass cells by the standard zero convention. -/
theorem conditional_failure_le (μ : Measure (Fin (m+1) → Block X)) [IsProbabilityMeasure μ]
    (hex : Exchangeable μ) (A : Learner X) (alpha a : ℝ)
    (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) (i : Fin (m+1)) (M : Multiset ℕ) :
    conditionalFailure μ A alpha a ell he i M ≤
      (frontierOfMultiset m alpha a ell M : ℝ)/(m+1 : ℕ) := by
  simpa only [conditionalFailure,Fintype.card_fin] using ConditionalExchangeability.conditionalRatio_le μ hex
    (fun Z i => finiteFailure A Z alpha a ell he i)
    (fun i => measurableSet_finiteFailure A alpha a ell he i)
    (finiteFailure_equivariant A alpha a ell he)
    sizeMultiset measurable_sizeMultiset (fun e Z => sizeMultiset_relabel Z e)
    (frontierOfMultiset m alpha a ell) (finiteFailure_count_le A alpha a ell he) i M

/-- The displayed conditional probability is a genuine version: every event
in the sigma algebra of the countable size statistic has the defining identity. -/
theorem conditional_failure_integral (μ : Measure (Fin (m+1) → Block X)) [IsProbabilityMeasure μ]
    (A : Learner X) (alpha a : ℝ) (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m)
    (i : Fin (m+1)) (D : Set (Multiset ℕ)) :
    (∫ Z in sizeMultiset ⁻¹' D, conditionalFailure μ A alpha a ell he i (sizeMultiset Z) ∂μ) =
      μ.real {Z | finiteFailure A Z alpha a ell he i ∧ sizeMultiset Z ∈ D} :=
  ConditionalExchangeability.conditionalRatio_setIntegral μ
    (fun Z i => finiteFailure A Z alpha a ell he i)
    (fun i => measurableSet_finiteFailure A alpha a ell he i)
    sizeMultiset measurable_sizeMultiset i D

/-- Equation (6.12), unconditional expectation bound, for the actual sample
space and actual source ranks. On the positive-rank almost-sure domain the
event is exactly the original interval rule by `finiteFailure_iff`. -/
theorem failure_probability_le_expectation (μ : Measure (Fin (m+1) → Block X)) [IsProbabilityMeasure μ]
    (hex : Exchangeable μ) (A : Learner X) (alpha a : ℝ)
    (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) (i : Fin (m+1)) :
    μ.real {Z | finiteFailure A Z alpha a ell he i} ≤
      ∫ Z, (frontierOfMultiset m alpha a ell (sizeMultiset Z) : ℝ)/(m+1 : ℕ) ∂μ := by
  simpa only [Fintype.card_fin] using ConditionalExchangeability.probability_le_integral_frontier μ hex
    (fun Z i => finiteFailure A Z alpha a ell he i)
    (fun i => measurableSet_finiteFailure A alpha a ell he i)
    (finiteFailure_equivariant A alpha a ell he)
    sizeMultiset measurable_sizeMultiset (frontierOfMultiset m alpha a ell)
    (by simpa using frontierOfMultiset_le m alpha a ell) (finiteFailure_count_le A alpha a ell he) i

/-- Source minimax problem (6.10), over every law with the fixed unordered
size multiset; assignment of the sizes to labels remains random. -/
def gamma (n : Fin (m+1) → ℕ+) (alpha a : ℝ) (ell : ℕ)
    (he : 1 ≤ ell ∧ ell ≤ m) : ℝ :=
  sSup {r : ℝ | ∃ (A : Learner Setup.UniversalCovariate)
    (μ : Measure (Fin (m+1) → Block Setup.UniversalCovariate)),
    IsProbabilityMeasure μ ∧ Exchangeable μ ∧
    μ.real {Z | sizeMultiset Z=univ.val.map (fun i => (n i).val)} = 1 ∧
    r = μ.real {Z | finiteFailure A Z alpha a ell he (Fin.last m)}}

lemma ae_sizeMultiset_of_real_eq_one (μ : Measure (Fin (m+1) → Block X)) [IsProbabilityMeasure μ]
    (M : Multiset ℕ) (hM : μ.real {Z | sizeMultiset Z=M}=1) :
    ∀ᵐ Z ∂μ, sizeMultiset Z=M := by
  have hm : MeasurableSet {Z : Fin (m+1) → Block X | sizeMultiset Z=M} :=
    (measurableSet_singleton M).preimage measurable_sizeMultiset
  have hc := measureReal_add_measureReal_compl (μ := μ) hm
  have hz : μ.real {Z | sizeMultiset Z=M}ᶜ=0 := by
    rw [hM,measureReal_univ_eq_one] at hc
    linarith
  have hz' : μ {Z | sizeMultiset Z=M}ᶜ=0 := (measureReal_eq_zero_iff).mp hz
  exact ae_iff.mpr hz'

/-- Fixed-multiset upper bound; the measure is supported on exactly the source
size multiset, with no ordering restriction on which label receives each size. -/
theorem fixed_multiset_probability_le (μ : Measure (Fin (m+1) → Block X)) [IsProbabilityMeasure μ]
    (hex : Exchangeable μ) (A : Learner X) (alpha a : ℝ)
    (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) (i : Fin (m+1)) (M : Multiset ℕ)
    (hM : μ.real {Z | sizeMultiset Z=M}=1) :
    μ.real {Z | finiteFailure A Z alpha a ell he i} ≤
      (frontierOfMultiset m alpha a ell M : ℝ)/(m+1 : ℕ) := by
  apply (failure_probability_le_expectation μ hex A alpha a ell he i).trans_eq
  have hae := ae_sizeMultiset_of_real_eq_one μ M hM
  calc
    (∫ Z, (frontierOfMultiset m alpha a ell (sizeMultiset Z) : ℝ)/(m+1 : ℕ) ∂μ) =
        ∫ _ : Fin (m+1) → Block X, (frontierOfMultiset m alpha a ell M : ℝ)/(m+1 : ℕ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hae] with Z hZ
      rw [hZ]
    _ = _ := by simp

/-- Any uniformly permuted fixed array remains on exactly its size multiset. -/
lemma permutationLaw_sizeMultiset (data : Fin (m+1) → Block X) :
    (FiniteExchangeable.blockPermutationLaw data).real
      {Z | sizeMultiset Z=sizeMultiset data}=1 := by
  have hp := FiniteExchangeable.blockPermutationLaw_equivariant_probability data
    (fun Z (_i : Fin (m+1)) => sizeMultiset Z=sizeMultiset data)
    (fun _ => (measurableSet_singleton (sizeMultiset data)).preimage measurable_sizeMultiset)
    (by intro e Z i; dsimp; rw [sizeMultiset_relabel]) (Fin.last m)
  have hc : (univ.filter fun _i : Fin (m+1) => sizeMultiset data=sizeMultiset data)=univ := by simp
  simpa [show (m : ℝ)+1 ≠ 0 by positivity] using hp

/-- A true jointly measurable variable-block learner and a finite exchangeable
law attain the fixed-size-multiset frontier. -/
theorem exists_attaining_model (n : Fin (m+1) → ℕ+) (alpha a : ℝ)
    (halpha : 0 ≤ alpha) (halpha1 : alpha < 1)
    (ht : ∀ i, 1 ≤ ⌊a*((n i).val+1)⌋₊ ∧ ⌊a*((n i).val+1)⌋₊ ≤ (n i).val)
    (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) :
    ∃ (A : Learner Setup.UniversalCovariate)
      (data : Fin (m+1) → Block Setup.UniversalCovariate),
      sizeMultiset data=univ.val.map (fun i => (n i).val) ∧
      (FiniteExchangeable.blockPermutationLaw data).real
        {Z | finiteFailure A Z alpha a ell he (Fin.last m)} =
        (frontierOfMultiset m alpha a ell (univ.val.map (fun i => (n i).val)) : ℝ)/(m+1 : ℕ) := by
  let F : Fin (m+1) → ℕ := fun i => ⌊alpha*(n i).val⌋₊+1
  let t : Fin (m+1) → ℕ := fun i => ⌊a*((n i).val+1)⌋₊
  have hF : ∀ i, 1 ≤ F i ∧ F i ≤ (n i).val := by
    intro i
    exact ActualPareto.failureRank_bounds (n i).property halpha halpha1
  let emb := HeterogeneousLearner.unitEmbedding n
  obtain ⟨A,hcount⟩ := HeterogeneousSharpness.exists_exact_failure_count_model n F t hF ht ell he emb emb.injective
  let data := HeterogeneousLearner.modelData n emb
  have hdata : sizeMultiset data=univ.val.map (fun i => (n i).val) := rfl
  have hf : ∀ i, finiteFailure A data alpha a ell he i ↔ learnerFailure A data F t ht ell he i :=
    fun i => finiteFailure_iff A data alpha a ell he i ht
  have hs : (univ.filter fun i => finiteFailure A data alpha a ell he i)=
      (univ.filter fun i => learnerFailure A data F t ht ell he i) := by
    ext i
    simp only [mem_filter,mem_univ,true_and,hf]
  refine ⟨A,data,hdata,?_⟩
  have hp := FiniteExchangeable.blockPermutationLaw_equivariant_probability data
    (fun Z i => finiteFailure A Z alpha a ell he i)
    (fun i => measurableSet_finiteFailure A alpha a ell he i)
    (finiteFailure_equivariant A alpha a ell he) (Fin.last m)
  rw [hs] at hp
  have hc : (univ.filter fun i => learnerFailure A data F t ht ell he i).card =
      sStar (demand F t ell) := hcount
  rw [hc] at hp
  rw [frontierOfMultiset_eq]
  simpa only [Fintype.card_fin, demand, sizeDemand, F, t] using hp

/-- Theorem 6.1, equation (6.11), for the actual fixed-multiset statistical
supremum. No exact-law or graph-realizability conclusion is an input. -/
theorem gamma_eq (n : Fin (m+1) → ℕ+) (alpha a : ℝ)
    (halpha : 0 ≤ alpha) (halpha1 : alpha < 1)
    (ht : ∀ i, 1 ≤ ⌊a*((n i).val+1)⌋₊ ∧ ⌊a*((n i).val+1)⌋₊ ≤ (n i).val)
    (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) :
    gamma n alpha a ell he =
      (frontierOfMultiset m alpha a ell (univ.val.map (fun i => (n i).val)) : ℝ)/(m+1 : ℕ) := by
  obtain ⟨A,data,hdata,hp⟩ := exists_attaining_model n alpha a halpha halpha1 ht ell he
  let ν := FiniteExchangeable.blockPermutationLaw data
  have hmem : (frontierOfMultiset m alpha a ell (univ.val.map (fun i => (n i).val)) : ℝ)/(m+1 : ℕ) ∈
      {r : ℝ | ∃ (A : Learner Setup.UniversalCovariate)
        (μ : Measure (Fin (m+1) → Block Setup.UniversalCovariate)),
        IsProbabilityMeasure μ ∧ Exchangeable μ ∧
        μ.real {Z | sizeMultiset Z=univ.val.map (fun i => (n i).val)}=1 ∧
        r=μ.real {Z | finiteFailure A Z alpha a ell he (Fin.last m)}} := by
    refine ⟨A,ν,by dsimp [ν]; infer_instance,FiniteExchangeable.blockPermutationLaw_exchangeable data,?_,hp.symm⟩
    rw [← hdata]
    exact permutationLaw_sizeMultiset data
  have hb : ∀ r ∈ {r : ℝ | ∃ (A : Learner Setup.UniversalCovariate)
      (μ : Measure (Fin (m+1) → Block Setup.UniversalCovariate)),
      IsProbabilityMeasure μ ∧ Exchangeable μ ∧
      μ.real {Z | sizeMultiset Z=univ.val.map (fun i => (n i).val)}=1 ∧
      r=μ.real {Z | finiteFailure A Z alpha a ell he (Fin.last m)}},
      r ≤ (frontierOfMultiset m alpha a ell (univ.val.map (fun i => (n i).val)) : ℝ)/(m+1 : ℕ) := by
    intro r hr
    obtain ⟨B,μ,hprob,hex,hM,rfl⟩ := hr
    letI : IsProbabilityMeasure μ := hprob
    exact fixed_multiset_probability_le μ hex B alpha a ell he (Fin.last m) _ hM
  unfold gamma
  exact le_antisymm (csSup_le ⟨_,hmem⟩ hb) (le_csSup ⟨_,hb⟩ hmem)

end
end MEJF.HeterogeneousProbability
