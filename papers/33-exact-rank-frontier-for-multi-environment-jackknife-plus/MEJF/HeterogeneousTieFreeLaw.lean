import MEJF.HeterogeneousTieFree
import MEJF.HeterogeneousSharpness
import MEJF.HeterogeneousEquivariance
import MEJF.HeterogeneousProbability

/-! Actual no-tie heterogeneous attaining models and their finite exchangeable
laws. The adaptive source radii are used only to express relabeling without
changing any dependent coordinate type; they equal the source scores on-domain. -/
set_option maxHeartbeats 800000

namespace MEJF.HeterogeneousTieFree
open Finset MeasureTheory HeterogeneousSetup HeterogeneousLearner HeterogeneousEquivariance
noncomputable section
attribute [local instance] Classical.propDecidable
variable {m : ℕ} {X : Type*} [MeasurableSpace X]

def actualCandidate (A : Learner X) (Z : Fin (m+1) → Block X) (a : ℝ) (upper : Bool)
    (u v : Fin (m+1)) (x : X) : ℝ :=
  if upper then pairPrediction A Z u v x+adaptiveRadius A Z a v u
  else pairPrediction A Z u v x-adaptiveRadius A Z a v u

def actualAggregate (A : Learner X) (Z : Fin (m+1) → Block X) (a : ℝ) (upper : Bool)
    (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) (u : Fin (m+1)) (x : X) : ℝ :=
  if upper then adaptiveUpperAt A Z a ell he u x else adaptiveLowerAt A Z a ell he u x

structure ActualTieFree (A : Learner X) (Z : Fin (m+1) → Block X) (a : ℝ)
    (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) : Prop where
  residuals : ∀ u v, u ≠ v → Function.Injective (fun j : Fin (size (Z u)) =>
    |((Z u).2 j).2-pairPrediction A Z u v ((Z u).2 j).1|)
  comparisons : ∀ u v, u ≠ v → adaptiveRadius A Z a u v ≠ adaptiveRadius A Z a v u
  candidates : ∀ upper u v w, u ≠ v → u ≠ w → v ≠ w → ∀ j : Fin (size (Z u)),
    actualCandidate A Z a upper u v ((Z u).2 j).1 ≠ actualCandidate A Z a upper u w ((Z u).2 j).1
  endpoints : ∀ upper u (j : Fin (size (Z u))),
    actualAggregate A Z a upper ell he u ((Z u).2 j).1 ≠ ((Z u).2 j).2

section Model
variable [MeasurableSingletonClass X]

lemma vector_adaptiveRadius (n : Fin (m+1) → ℕ+) (emb : CovariateTable n → X)
    (hinj : Function.Injective emb) (z : Vector n) (a : ℝ)
    (ht : ∀ u, 1 ≤ ⌊a*((n u).val+1)⌋₊ ∧ ⌊a*((n u).val+1)⌋₊ ≤ (n u).val)
    (u v : Fin (m+1)) (huv : u ≠ v) :
    adaptiveRadius (learner n (P n z) emb) (vectorData n emb z) a u v =
      radius n z u v (Setup.innerIndex (n u).val ⌊a*((n u).val+1)⌋₊ (ht u)) := by
  have ht' : finiteDomain (vectorData n emb z) a := by intro i; exact ht i
  rw [adaptiveRadius_eq (learner n (P n z) emb) (vectorData n emb z) a ht' u v]
  exact vector_radius n emb hinj z _ ht u v huv

lemma vector_actualCandidate (n : Fin (m+1) → ℕ+) (emb : CovariateTable n → X)
    (hinj : Function.Injective emb) (z : Vector n) (a : ℝ)
    (ht : ∀ u, 1 ≤ ⌊a*((n u).val+1)⌋₊ ∧ ⌊a*((n u).val+1)⌋₊ ≤ (n u).val)
    (upper : Bool) (u v : Fin (m+1)) (huv : u ≠ v) (j : Fin (n u).val) :
    actualCandidate (learner n (P n z) emb) (vectorData n emb z) a upper u v (emb ⟨u,j⟩) =
      candidate n z upper u v j (Setup.innerIndex (n v).val ⌊a*((n v).val+1)⌋₊ (ht v)) := by
  unfold actualCandidate
  rw [vector_pairPrediction n emb hinj z u v huv,vector_adaptiveRadius n emb hinj z a ht v u (Ne.symm huv)]
  rfl

lemma vector_actualAggregate (n : Fin (m+1) → ℕ+) (emb : CovariateTable n → X)
    (hinj : Function.Injective emb) (z : Vector n) (a : ℝ)
    (ht : ∀ u, 1 ≤ ⌊a*((n u).val+1)⌋₊ ∧ ⌊a*((n u).val+1)⌋₊ ≤ (n u).val)
    (upper : Bool) (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) (u : Fin (m+1)) (j : Fin (n u).val) :
    actualAggregate (learner n (P n z) emb) (vectorData n emb z) a upper ell he u (emb ⟨u,j⟩) =
      aggregate n z upper u j (fun v => Setup.innerIndex (n v).val ⌊a*((n v).val+1)⌋₊ (ht v))
        (if upper then Setup.upperIndex m ell he else Setup.lowerIndex m ell he) := by
  have ht' : finiteDomain (vectorData n emb z) a := by intro i; exact ht i
  cases upper
  · change adaptiveLowerAt (learner n (P n z) emb) (vectorData n emb z) a ell he u (emb ⟨u,j⟩) = _
    exact (adaptiveLowerAt_eq (learner n (P n z) emb) (vectorData n emb z) a ht' ell he u j).trans
      (vector_lowerEndpoint n emb hinj z _ ht ell he u j)
  · change adaptiveUpperAt (learner n (P n z) emb) (vectorData n emb z) a ell he u (emb ⟨u,j⟩) = _
    exact (adaptiveUpperAt_eq (learner n (P n z) emb) (vectorData n emb z) a ht' ell he u j).trans
      (vector_upperEndpoint n emb hinj z _ ht ell he u j)

/-- The table property proves every source no-tie assertion, including radii
selected from genuinely different coordinate dimensions. -/
theorem actualTieFree_of_table (n : Fin (m+1) → ℕ+) (emb : CovariateTable n → X)
    (hinj : Function.Injective emb) (z : Vector n) (hz : TieFree n z) (a : ℝ)
    (ht : ∀ u, 1 ≤ ⌊a*((n u).val+1)⌋₊ ∧ ⌊a*((n u).val+1)⌋₊ ≤ (n u).val)
    (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) :
    ActualTieFree (learner n (P n z) emb) (vectorData n emb z) a ell he := by
  constructor
  · intro u v huv j q heq
    apply hz.residuals u v
    change |Y n z u j-pairPrediction _ _ u v (emb ⟨u,j⟩)| =
      |Y n z u q-pairPrediction _ _ u v (emb ⟨u,q⟩)| at heq
    simpa only [vector_pairPrediction n emb hinj z u v huv] using heq
  · intro u v huv
    rw [vector_adaptiveRadius n emb hinj z a ht u v huv,
      vector_adaptiveRadius n emb hinj z a ht v u (Ne.symm huv)]
    exact hz.comparisons u v huv _ _
  · intro upper u v w huv huw hvw j
    change actualCandidate _ _ a upper u v (emb ⟨u,j⟩) ≠ actualCandidate _ _ a upper u w (emb ⟨u,j⟩)
    rw [vector_actualCandidate n emb hinj z a ht upper u v huv j,
      vector_actualCandidate n emb hinj z a ht upper u w huw j]
    exact hz.candidates upper u v w huv huw hvw _ _ _
  · intro upper u j
    change actualAggregate _ _ a upper ell he u (emb ⟨u,j⟩) ≠ Y n z u j
    rw [vector_actualAggregate n emb hinj z a ht upper ell he u j]
    exact hz.endpoints upper u j _ _

end Model

lemma actualCandidate_relabel (A : Learner X) (Z : Fin (m+1) → Block X)
    (e : Equiv.Perm (Fin (m+1))) (a : ℝ) (upper : Bool) (u v : Fin (m+1)) (x : X) :
    actualCandidate A (Exchangeability.relabel e Z) a upper (e u) (e v) x =
      actualCandidate A Z a upper u v x := by
  unfold actualCandidate
  rw [pairPrediction_relabel,adaptiveRadius_relabel]

lemma actualAggregate_relabel (A : Learner X) (Z : Fin (m+1) → Block X)
    (e : Equiv.Perm (Fin (m+1))) (a : ℝ) (upper : Bool) (ell : ℕ)
    (he : 1 ≤ ell ∧ ell ≤ m) (u : Fin (m+1)) (x : X) :
    actualAggregate A (Exchangeability.relabel e Z) a upper ell he (e u) x =
      actualAggregate A Z a upper ell he u x := by
  cases upper <;> simp only [actualAggregate,Bool.false_eq_true,↓reduceIte,
    adaptiveLowerAt_relabel,adaptiveUpperAt_relabel]

/-- All four actual no-tie conditions survive label permutation. -/
theorem ActualTieFree.relabel {A : Learner X} {Z : Fin (m+1) → Block X} {a : ℝ}
    {ell : ℕ} {he : 1 ≤ ell ∧ ell ≤ m} (h : ActualTieFree A Z a ell he)
    (e : Equiv.Perm (Fin (m+1))) : ActualTieFree A (Exchangeability.relabel e Z) a ell he := by
  constructor
  · intro u v huv
    obtain ⟨u,rfl⟩ := e.surjective u
    obtain ⟨v,rfl⟩ := e.surjective v
    have hZu : Exchangeability.relabel e Z (e u) = Z u := by simp [Exchangeability.relabel]
    simp only [pairPrediction_relabel]
    simp only [Exchangeability.relabel,Function.comp_apply]
    rw [e.symm_apply_apply u]
    exact h.residuals u v (fun hh => huv (congrArg e hh))
  · intro u v huv
    obtain ⟨u,rfl⟩ := e.surjective u
    obtain ⟨v,rfl⟩ := e.surjective v
    rw [adaptiveRadius_relabel,adaptiveRadius_relabel]
    exact h.comparisons u v (fun hh => huv (congrArg e hh))
  · intro upper u v w huv huw hvw
    obtain ⟨u,rfl⟩ := e.surjective u
    obtain ⟨v,rfl⟩ := e.surjective v
    obtain ⟨w,rfl⟩ := e.surjective w
    have hZu : Exchangeability.relabel e Z (e u) = Z u := by simp [Exchangeability.relabel]
    simp only [actualCandidate_relabel]
    simp only [Exchangeability.relabel,Function.comp_apply]
    rw [e.symm_apply_apply u]
    exact h.candidates upper u v w
      (fun hh => huv (congrArg e hh)) (fun hh => huw (congrArg e hh)) (fun hh => hvw (congrArg e hh))
  · intro upper u
    obtain ⟨u,rfl⟩ := e.surjective u
    have hZu : Exchangeability.relabel e Z (e u) = Z u := by simp [Exchangeability.relabel]
    simp only [actualAggregate_relabel]
    simp only [Exchangeability.relabel,Function.comp_apply]
    rw [e.symm_apply_apply u]
    exact h.endpoints upper u

section Attainment
variable [MeasurableSingletonClass X]

lemma P_baseline_eq (n : Fin (m+1) → ℕ+) (p : PredictionTable n) : P n (baseline n p) = p := by
  funext u v j
  exact P_baseline n p u v j

lemma vectorData_baseline (n : Fin (m+1) → ℕ+) (emb : CovariateTable n → X) (p : PredictionTable n) :
    vectorData n emb (baseline n p) = modelData n emb := rfl

/-- One primitive perturbation attains the exact heterogeneous frontier without
any relevant table tie; the universal count excludes new failing labels. -/
theorem exists_quantitative_tieFree_model (n : Fin (m+1) → ℕ+) (F t : Fin (m+1) → ℕ)
    (hF : ∀ u, 1 ≤ F u ∧ F u ≤ (n u).val) (ht : ∀ u, 1 ≤ t u ∧ t u ≤ (n u).val)
    (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) (emb : CovariateTable n → X)
    (hinj : Function.Injective emb) (η : ℝ) (hη : 0 < η) (hη' : η < 1/4) :
    ∃ (p : PredictionTable n) (z : Vector n),
      (∀ u v j, 1 ≤ p u v j) ∧ (∀ c, |z c-baseline n p c| ≤ η) ∧ TieFree n z ∧
      (univ.filter fun u => learnerFailure (learner n (P n z) emb) (vectorData n emb z)
        F t ht ell he u).card = HeterogeneousFrontier.sStar (demand F t ell) := by
  obtain ⟨R,S,B,hR,hS,hmark,hunmark,hrows,_hzero⟩ := HeterogeneousSharpness.exists_sharpness_bits
    n F t (fun u => (hF u).2) (fun u => (ht u).1) ell he
  let p := HeterogeneousSharpness.table n R B
  have hp : ∀ u v j, 1 ≤ p u v j := HeterogeneousSharpness.table_ge_one n R B
  obtain ⟨z,hz,htf,hpres⟩ := quantitative_tie_removal n p hp η hη hη'
  let A := learner n (P n z) emb
  let Z := vectorData n emb z
  have hsel : S ⊆ univ.filter (fun u => learnerFailure A Z F t ht ell he u) := by
    intro u hu
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    unfold learnerFailure HeterogeneousSetup.failure
    rw [← Sharpness.firstRows_card (hF u).2]
    apply Finset.card_le_card
    intro j hj
    have hjF : j.val < F u := (mem_filter.mp hj).2
    have hlbase : aggregate n (baseline n p) false u j
        (fun v => Setup.innerIndex (n v).val (t v) (ht v)) (Setup.lowerIndex m ell he) = 1 := by
      rw [← vector_lowerEndpoint n emb hinj (baseline n p) t ht ell he u j,P_baseline_eq]
      change HeterogeneousSetup.lowerEndpoint (learner n p emb) (modelData n emb) t ht ell he u j = 1
      exact HeterogeneousSharpness.selected_lowerEndpoint_eq_one n R hR B emb hinj t ht ell he
        hmark hunmark u j (hrows u hu j hjF)
    have hmarg : Y n (baseline n p) u j+1 ≤ aggregate n (baseline n p) false u j
        (fun v => Setup.innerIndex (n v).val (t v) (ht v)) (Setup.lowerIndex m ell he) := by
      rw [hlbase,Y_baseline]
      norm_num
    have hstrict := hpres u j (fun v => Setup.innerIndex (n v).val (t v) (ht v))
      (Setup.lowerIndex m ell he) hmarg
    rw [← vector_lowerEndpoint n emb hinj z t ht ell he u j] at hstrict
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    intro hc
    have hcle : HeterogeneousSetup.lowerEndpoint A Z t ht ell he u j ≤ Y n z u j := hc.1
    exact (not_le_of_gt hstrict) hcle
  have hl := Finset.card_le_card hsel
  rw [hS] at hl
  have hu := learner_failure_count_le_sStar A Z F t ht ell he
  exact ⟨p,z,hp,hz,htf,le_antisymm hu hl⟩

end Attainment

/-- The disjoint-union sigma algebra makes each singleton measurable whenever
every fiber has measurable singletons. -/
local instance sigmaMeasurableSingleton {I : Type*} {β : I → Type*}
    [mb : ∀ i, MeasurableSpace (β i)] [∀ i, MeasurableSingletonClass (β i)] :
    MeasurableSingletonClass (Sigma β) := by
  constructor
  rintro ⟨u,q⟩
  change MeasurableSet[⨅ i, (mb i).map (Sigma.mk i)] {⟨u,q⟩}
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro i
  change MeasurableSet ((Sigma.mk i) ⁻¹' {⟨u,q⟩})
  by_cases hi : i = u
  · subst i
    have hs : (Sigma.mk u) ⁻¹' ({⟨u,q⟩} : Set (Sigma β)) = {q} := by
      ext j
      simp only [Set.mem_preimage,Set.mem_singleton_iff,Sigma.mk.inj_iff,true_and,heq_iff_eq]
    rw [hs]
    exact measurableSet_singleton q
  · have hs : (Sigma.mk i) ⁻¹' ({⟨u,q⟩} : Set (Sigma β)) = ∅ := by
      ext j
      simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_empty_iff_false,iff_false]
      intro hh
      exact hi (congrArg Sigma.fst hh)
    rw [hs]
    exact MeasurableSet.empty

local instance : MeasurableSpace (Equiv.Perm (Fin (m+1))) := ⊤
local instance : MeasurableSingletonClass (Equiv.Perm (Fin (m+1))) := ⟨fun _ => trivial⟩

/-- Actual no-tie assertions hold almost surely under the actual finite
exchangeable block law, not just for a primitive table or one base labeling. -/
theorem actualTieFree_ae_permutationLaw [MeasurableSingletonClass X]
    {A : Learner X} {Z : Fin (m+1) → Block X} {a : ℝ} {ell : ℕ}
    {he : 1 ≤ ell ∧ ell ≤ m} (h : ActualTieFree A Z a ell he) :
    ∀ᵐ W ∂FiniteExchangeable.blockPermutationLaw Z, ActualTieFree A W a ell he := by
  let f : Equiv.Perm (Fin (m+1)) → (Fin (m+1) → Block X) := fun p => Z ∘ p
  have hμ : FiniteExchangeable.blockPermutationLaw Z =
      (FiniteExchangeable.permutationMeasure (Fin (m+1))).map f := by
    unfold FiniteExchangeable.blockPermutationLaw FiniteExchangeable.uniformPermutationLaw
    rw [Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
    rfl
  rw [hμ]
  have hrange := ae_map_mem_range f (Set.finite_range f).measurableSet
    (FiniteExchangeable.permutationMeasure (Fin (m+1)))
  filter_upwards [hrange] with W hW
  obtain ⟨p,rfl⟩ := hW
  exact h.relabel p.symm

/-- The source's exact heterogeneous lower law admits an actual tie-free
finite exchangeable attaining model, for every prescribed positive size vector. -/
theorem source_exists_tieFree_attaining_law [MeasurableSingletonClass X] [Nonempty X]
    (n : Fin (m+1) → ℕ+) (alpha a : ℝ) (hα : 0 ≤ alpha) (hα1 : alpha < 1)
    (ht : ∀ u, 1 ≤ ⌊a*((n u).val+1)⌋₊ ∧ ⌊a*((n u).val+1)⌋₊ ≤ (n u).val)
    (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) (emb : CovariateTable n → X)
    (hinj : Function.Injective emb) (η : ℝ) (hη : 0 < η) (hη' : η < 1/4) :
    ∃ (A : Learner X) (data : Fin (m+1) → Block X),
      (∀ u, (data u).1 = n u) ∧
      (FiniteExchangeable.blockPermutationLaw data).real
        {Z | HeterogeneousProbability.finiteFailure A Z alpha a ell he (Fin.last m)} =
        (HeterogeneousFrontier.sStar (fun u => sizeDemand m alpha a ell (n u).val) : ℝ)/(m+1 : ℕ) ∧
      (∀ᵐ Z ∂FiniteExchangeable.blockPermutationLaw data, ActualTieFree A Z a ell he) := by
  let F : Fin (m+1) → ℕ := fun u => ⌊alpha*(n u).val⌋₊+1
  let t : Fin (m+1) → ℕ := fun u => ⌊a*((n u).val+1)⌋₊
  have hF : ∀ u, 1 ≤ F u ∧ F u ≤ (n u).val := by
    intro u
    have hn : (0 : ℝ) < (n u).val := by exact_mod_cast (n u).property
    have hx : alpha*(n u).val < (n u).val := by nlinarith
    have hh := (Nat.floor_lt (mul_nonneg hα hn.le)).mpr hx
    dsimp [F]
    omega
  obtain ⟨p,z,hp,hz,htf,hcount⟩ := exists_quantitative_tieFree_model n F t hF ht ell he emb hinj η hη hη'
  let A := learner n (P n z) emb
  let data := vectorData n emb z
  have hactual : ActualTieFree A data a ell he := actualTieFree_of_table n emb hinj z htf a ht ell he
  have hfinite : finiteDomain data a := by intro u; exact ht u
  have hc : (univ.filter fun u => HeterogeneousProbability.finiteFailure A data alpha a ell he u).card =
      HeterogeneousFrontier.sStar (demand F t ell) := by
    have hs : (univ.filter fun u => HeterogeneousProbability.finiteFailure A data alpha a ell he u) =
        univ.filter (fun u => learnerFailure A data F t ht ell he u) := by
      ext u
      simp only [mem_filter,mem_univ,true_and]
      exact HeterogeneousProbability.finiteFailure_iff A data alpha a ell he u hfinite
    rw [hs]
    exact hcount
  have hprob := FiniteExchangeable.blockPermutationLaw_equivariant_probability data
    (fun Z i => HeterogeneousProbability.finiteFailure A Z alpha a ell he i)
    (fun i => HeterogeneousProbability.measurableSet_finiteFailure A alpha a ell he i)
    (HeterogeneousEquivariance.finiteFailure_equivariant A alpha a ell he) (Fin.last m)
  refine ⟨A,data,(fun _ => rfl),?_,actualTieFree_ae_permutationLaw hactual⟩
  rw [hc] at hprob
  simpa only [Fintype.card_fin,demand,sizeDemand,F,t] using hprob

/-- No embedding or no-tie assumption is added to the paper's fixed universal
sample space: the concrete finite embedding and primitive perturbation are
constructed, and the actual fixed-multiset statistical supremum is attained. -/
theorem source_exists_tieFree_minimax_law (n : Fin (m+1) → ℕ+) (alpha a : ℝ)
    (hα : 0 ≤ alpha) (hα1 : alpha < 1)
    (ht : ∀ u, 1 ≤ ⌊a*((n u).val+1)⌋₊ ∧ ⌊a*((n u).val+1)⌋₊ ≤ (n u).val)
    (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) :
    ∃ (A : Learner Setup.UniversalCovariate)
      (data : Fin (m+1) → Block Setup.UniversalCovariate),
      (∀ u, (data u).1 = n u) ∧
      (FiniteExchangeable.blockPermutationLaw data).real
        {Z | sizeMultiset Z = univ.val.map (fun u => (n u).val)} = 1 ∧
      (FiniteExchangeable.blockPermutationLaw data).real
        {Z | HeterogeneousProbability.finiteFailure A Z alpha a ell he (Fin.last m)} =
        HeterogeneousProbability.gamma n alpha a ell he ∧
      (∀ᵐ Z ∂FiniteExchangeable.blockPermutationLaw data, ActualTieFree A Z a ell he) := by
  let emb := HeterogeneousLearner.unitEmbedding n
  obtain ⟨A,data,hsize,hprob,hties⟩ := source_exists_tieFree_attaining_law
    n alpha a hα hα1 ht ell he emb emb.injective (1/8) (by norm_num) (by norm_num)
  have hdata : sizeMultiset data = univ.val.map (fun u => (n u).val) := by
    unfold sizeMultiset
    apply Multiset.map_congr rfl
    intro u _
    exact congrArg PNat.val (hsize u)
  have hsizeLaw := HeterogeneousProbability.permutationLaw_sizeMultiset data
  rw [hdata] at hsizeLaw
  have hΓ := HeterogeneousProbability.gamma_eq n alpha a hα hα1 ht ell he
  rw [HeterogeneousProbability.frontierOfMultiset_eq] at hΓ
  refine ⟨A,data,hsize,hsizeLaw,?_,hties⟩
  rw [hΓ]
  exact hprob

end
end MEJF.HeterogeneousTieFree
