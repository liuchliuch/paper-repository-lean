import MEJF.ResponsePerturbation
import MEJF.TieFreeTable
import MEJF.MainExact

/-! # Actual tie-free attaining models (Proposition 5.3)

The primitive general-position perturbation is realized by a jointly measurable
multiset learner on the full ambient covariate space. All four no-tie properties
are stated for the actual residuals, radii, candidates, and aggregate endpoints.
-/
namespace MEJF.TieFreeSharpness

open Finset MeasureTheory MEJF.Setup MEJF.Exchangeability MEJF.PredictionTable
noncomputable section
attribute [local instance] Classical.propDecidable

variable {X : Type*} [MeasurableSpace X] {m n : ℕ}

/-- An actual fitted endpoint candidate, before the outer order statistic. -/
def candidate (A : Learner X n) (Z : Fin (m+1) → Block X n) (upper : Bool)
    (u v : Fin (m+1)) (j : Fin n) (t : ℕ) (ht : 1 ≤ t ∧ t ≤ n) : ℝ :=
  if upper then pairPrediction A Z u v (Z u j).1 + radius A Z v u t ht
  else pairPrediction A Z u v (Z u j).1 - radius A Z v u t ht

/-- Both actual aggregate endpoints, with the paper's positive finite ranks. -/
def aggregate (A : Learner X n) (Z : Fin (m+1) → Block X n) (upper : Bool)
    (u : Fin (m+1)) (j : Fin n) (t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) : ℝ :=
  if upper then upperEndpoint A Z u j t ell ht he else lowerEndpoint A Z u j t ell ht he

/-- The four no-tie assertions in Proposition 5.3, for actual statistical objects. -/
structure ActualTieFree (A : Learner X n) (Z : Fin (m+1) → Block X n)
    (t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) : Prop where
  residuals : ∀ u v, u ≠ v → Function.Injective
    (fun j => |(Z u j).2 - pairPrediction A Z u v (Z u j).1|)
  comparisons : ∀ u v, u ≠ v → radius A Z u v t ht ≠ radius A Z v u t ht
  candidates : ∀ upper u v w, u ≠ v → u ≠ w → v ≠ w → ∀ j,
    candidate A Z upper u v j t ht ≠ candidate A Z upper u w j t ht
  endpoints : ∀ upper u j, aggregate A Z upper u j t ell ht he ≠ (Z u j).2

/-- Interpret the primitive perturbation vector as a prediction table. -/
def vectorPredictions (z : TieFreeTable.Vector (m+1) n) : Fin (m+1) → Fin (m+1) → Fin n → ℝ :=
  fun u v j => TieFreeTable.prediction u v j z

/-- Interpret the same vector as perturbed complete response blocks. -/
def vectorData (emb : Fin (m+1) × Fin n → X) (z : TieFreeTable.Vector (m+1) n) :
    Fin (m+1) → Block X n := modelDataWithResponses emb (fun u j => TieFreeTable.response u j z)

section Model
variable [MeasurableSingletonClass X]

lemma vector_pairPrediction (emb : Fin (m+1) × Fin n → X) (hinj : Function.Injective emb)
    (z : TieFreeTable.Vector (m+1) n) (hn : 0 < n) (u v : Fin (m+1)) (huv : u ≠ v) (j : Fin n) :
    pairPrediction (tableLearner (vectorPredictions z) emb) (vectorData emb z) u v (emb (u,j)) =
      TieFreeTable.prediction u v j z :=
  modelResponses_pairPrediction _ emb hinj hn _ u v huv j

lemma vector_radius (emb : Fin (m+1) × Fin n → X) (hinj : Function.Injective emb)
    (z : TieFreeTable.Vector (m+1) n) (t : ℕ) (ht : 1 ≤ t ∧ t ≤ n)
    (u v : Fin (m+1)) (huv : u ≠ v) :
    radius (tableLearner (vectorPredictions z) emb) (vectorData emb z) u v t ht =
      TieFreeTable.radius z u v (innerIndex n t ht) :=
  modelResponses_radius _ emb hinj (by omega) _ u v huv t ht

lemma vector_candidate (emb : Fin (m+1) × Fin n → X) (hinj : Function.Injective emb)
    (z : TieFreeTable.Vector (m+1) n) (upper : Bool) (t : ℕ) (ht : 1 ≤ t ∧ t ≤ n)
    (u v : Fin (m+1)) (huv : u ≠ v) (j : Fin n) :
    candidate (tableLearner (vectorPredictions z) emb) (vectorData emb z) upper u v j t ht =
      TieFreeTable.candidate z upper u v j (innerIndex n t ht) := by
  unfold candidate
  change (if upper then pairPrediction _ _ u v (emb (u,j)) + _ else pairPrediction _ _ u v (emb (u,j)) - _) = _
  rw [vector_pairPrediction emb hinj z (by omega) u v huv j,
    vector_radius emb hinj z t ht v u (Ne.symm huv)]
  rfl

lemma vector_lowerEndpoint (emb : Fin (m+1) × Fin n → X) (hinj : Function.Injective emb)
    (z : TieFreeTable.Vector (m+1) n) (t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) (u : Fin (m+1)) (j : Fin n) :
    lowerEndpoint (tableLearner (vectorPredictions z) emb) (vectorData emb z) u j t ell ht he =
      TieFreeTable.aggregate z false u j (innerIndex n t ht) (lowerIndex m ell he) := by
  unfold lowerEndpoint TieFreeTable.aggregate
  congr 1
  funext k
  exact vector_candidate emb hinj z false t ht u (u.succAbove k) (u.ne_succAbove k) j

lemma vector_upperEndpoint (emb : Fin (m+1) × Fin n → X) (hinj : Function.Injective emb)
    (z : TieFreeTable.Vector (m+1) n) (t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) (u : Fin (m+1)) (j : Fin n) :
    upperEndpoint (tableLearner (vectorPredictions z) emb) (vectorData emb z) u j t ell ht he =
      TieFreeTable.aggregate z true u j (innerIndex n t ht) (upperIndex m ell he) := by
  unfold upperEndpoint TieFreeTable.aggregate
  congr 1
  funext k
  exact vector_candidate emb hinj z true t ht u (u.succAbove k) (u.ne_succAbove k) j

/-- Primitive table no-ties imply all the actual learner's no-tie assertions. -/
theorem actualTieFree_of_table (emb : Fin (m+1) × Fin n → X) (hinj : Function.Injective emb)
    (z : TieFreeTable.Vector (m+1) n) (hz : TieFreeTable.TieFree z)
    (t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    ActualTieFree (tableLearner (vectorPredictions z) emb) (vectorData emb z) t ell ht he := by
  constructor
  · intro u v huv j q hjq
    apply hz.residuals u v
    change |TieFreeTable.response u j z - pairPrediction _ _ u v (emb (u,j))| =
      |TieFreeTable.response u q z - pairPrediction _ _ u v (emb (u,q))| at hjq
    simpa only [vector_pairPrediction emb hinj z (by omega) u v huv] using hjq
  · intro u v huv
    rw [vector_radius emb hinj z t ht u v huv, vector_radius emb hinj z t ht v u (Ne.symm huv)]
    exact hz.comparisons u v huv _
  · intro upper u v w huv huw hvw j
    rw [vector_candidate emb hinj z upper t ht u v huv j,
      vector_candidate emb hinj z upper t ht u w huw j]
    exact hz.candidates upper u v w huv huw hvw j _
  · intro upper u j
    cases upper
    · change lowerEndpoint _ _ _ _ _ _ _ _ ≠ _
      rw [vector_lowerEndpoint emb hinj z t ell ht he u j]
      exact hz.endpoints false u j _ _
    · change upperEndpoint _ _ _ _ _ _ _ _ ≠ _
      rw [vector_upperEndpoint emb hinj z t ell ht he u j]
      exact hz.endpoints true u j _ _

end Model

lemma candidate_relabel (A : Learner X n) (Z : Fin (m+1) → Block X n)
    (e : Equiv.Perm (Fin (m+1))) (upper : Bool) (u v : Fin (m+1)) (j : Fin n)
    (t : ℕ) (ht : 1 ≤ t ∧ t ≤ n) :
    candidate A (relabel e Z) upper (e u) (e v) j t ht = candidate A Z upper u v j t ht := by
  have hZu : relabel e Z (e u) = Z u := by simp [relabel]
  unfold candidate
  rw [hZu, SetupEquivariance.pairPrediction_relabel, SetupEquivariance.radius_relabel]

lemma aggregate_relabel (A : Learner X n) (Z : Fin (m+1) → Block X n)
    (e : Equiv.Perm (Fin (m+1))) (upper : Bool) (u : Fin (m+1)) (j : Fin n)
    (t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    aggregate A (relabel e Z) upper (e u) j t ell ht he = aggregate A Z upper u j t ell ht he := by
  cases upper <;> simp only [aggregate, Bool.false_eq_true, ↓reduceIte,
    SetupEquivariance.lowerEndpoint_relabel, SetupEquivariance.upperEndpoint_relabel]

/-- The actual no-tie property survives every block permutation. -/
theorem ActualTieFree.relabel {A : Learner X n} {Z : Fin (m+1) → Block X n}
    {t ell : ℕ} {ht : 1 ≤ t ∧ t ≤ n} {he : 1 ≤ ell ∧ ell ≤ m}
    (h : ActualTieFree A Z t ell ht he) (e : Equiv.Perm (Fin (m+1))) :
    ActualTieFree A (Exchangeability.relabel e Z) t ell ht he := by
  constructor
  · intro u v huv
    obtain ⟨u, rfl⟩ := e.surjective u
    obtain ⟨v, rfl⟩ := e.surjective v
    have hZu : Exchangeability.relabel e Z (e u) = Z u := by simp [Exchangeability.relabel]
    simpa only [hZu, SetupEquivariance.pairPrediction_relabel] using
      h.residuals u v (fun h => huv (congrArg e h))
  · intro u v huv
    obtain ⟨u, rfl⟩ := e.surjective u
    obtain ⟨v, rfl⟩ := e.surjective v
    rw [SetupEquivariance.radius_relabel, SetupEquivariance.radius_relabel]
    exact h.comparisons u v (fun hh => huv (congrArg e hh))
  · intro upper u v w huv huw hvw j
    obtain ⟨u, rfl⟩ := e.surjective u
    obtain ⟨v, rfl⟩ := e.surjective v
    obtain ⟨w, rfl⟩ := e.surjective w
    rw [candidate_relabel, candidate_relabel]
    exact h.candidates upper u v w (fun hh => huv (congrArg e hh))
      (fun hh => huw (congrArg e hh)) (fun hh => hvw (congrArg e hh)) j
  · intro upper u j
    obtain ⟨u, rfl⟩ := e.surjective u
    rw [aggregate_relabel]
    have hZu : Exchangeability.relabel e Z (e u) = Z u := by simp [Exchangeability.relabel]
    rw [hZu]
    exact h.endpoints upper u j

local instance : MeasurableSpace (Equiv.Perm (Fin (m+1))) := ⊤
local instance : MeasurableSingletonClass (Equiv.Perm (Fin (m+1))) := ⟨fun _ => trivial⟩

/-- The finite permutation law is concentrated on the actual no-tie arrays. -/
theorem actualTieFree_ae_permutationLaw [MeasurableSingletonClass X]
    {A : Learner X n} {Z : Fin (m+1) → Block X n} {t ell : ℕ}
    {ht : 1 ≤ t ∧ t ≤ n} {he : 1 ≤ ell ∧ ell ≤ m}
    (h : ActualTieFree A Z t ell ht he) :
    ∀ᵐ W ∂FiniteExchangeable.blockPermutationLaw Z, ActualTieFree A W t ell ht he := by
  let f : Equiv.Perm (Fin (m+1)) → (Fin (m+1) → Block X n) := fun p => Z ∘ p
  have hμ : FiniteExchangeable.blockPermutationLaw Z =
      (FiniteExchangeable.permutationMeasure (Fin (m+1))).map f := by
    unfold FiniteExchangeable.blockPermutationLaw FiniteExchangeable.uniformPermutationLaw
    rw [Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
    rfl
  rw [hμ]
  have hrange := ae_map_mem_range f (Set.finite_range f).measurableSet
    (FiniteExchangeable.permutationMeasure (Fin (m+1)))
  filter_upwards [hrange] with W hW
  obtain ⟨p, rfl⟩ := hW
  exact h.relabel p.symm

/-- Proposition 5.3 on the original objects: every primitive perturbation is
bounded by `eta`, the actual fitted model has no relevant ties, and the original
selected labels are exactly the failing labels after perturbation. -/
theorem exists_quantitative_tieFree_model [MeasurableSingletonClass X]
    (m n F t ell : ℕ) (hm : 1 ≤ m) (hF : 1 ≤ F) (hFn : F ≤ n)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m)
    (emb : Fin (m+1) × Fin n → X) (hinj : Function.Injective emb)
    (eta : ℝ) (heta : 0 < eta) (heta' : eta < 1/4) :
    ∃ (R : Fin (m+1) → Fin (m+1) → Prop)
      (B : Fin (m+1) → Fin n → Fin (m+1) → Bool)
      (S : Finset (Fin (m+1))) (z : TieFreeTable.Vector (m+1) n),
      S.card = RankFrontier.failureCount m F t ell ∧
      (∀ a, |z a - TieFreeTable.baseline (incidenceTable R B) a| ≤ eta) ∧
      ActualTieFree (tableLearner (vectorPredictions z) emb) (vectorData emb z) t ell ht he ∧
      ∀ u, Setup.failure (tableLearner (vectorPredictions z) emb) (vectorData emb z) u F t ell ht he ↔ u ∈ S := by
  obtain ⟨R, S, B, hasym, hScard, hmark, hunmark, hrows, hzero⟩ :=
    Sharpness.exists_sharpness_array m n F t ell hm hFn ht.1 he
  let p := incidenceTable R B
  have hp : ∀ u v j, 1 ≤ p u v j := incidenceTable_ge_one R B
  obtain ⟨z, hz, htf, hpres⟩ := TieFreeTable.quantitative_tie_removal p hp eta heta heta'
  let A := tableLearner (vectorPredictions z) emb
  let Z := vectorData emb z
  have hsize : S.card = RankFrontier.failureCount m F t ell := by
    simpa only [RankFrontier.failureCount, RankFrontier.capacity] using
      hScard.trans (Sharpness.graph_size_formula m F t ell he)
  have hlow : ∀ u ∈ S, ∀ j : Fin n, j.val < F →
      TieFreeTable.aggregate (TieFreeTable.baseline p) false u j (innerIndex n t ht) (lowerIndex m ell he) = 1 := by
    intro u hu j hj
    rw [← vector_lowerEndpoint emb hinj (TieFreeTable.baseline p) t ell ht he u j]
    change lowerEndpoint (tableLearner p emb) (modelData emb) u j t ell ht he = 1
    rw [model_lowerEndpoint_incidence R (fun {u v} => hasym u v) B emb hinj t ell ht he hmark hunmark]
    exact incidence_lower_endpoint R B u j u.succAbove (by omega) he.2 (hrows u hu j hj)
  have hselected : S ⊆ univ.filter (fun u => Setup.failure A Z u F t ell ht he) := by
    intro u hu
    simp only [mem_filter, mem_univ, true_and]
    have hs : Sharpness.firstRows F n ⊆ (univ.filter fun j => ¬ Setup.covered A Z u j t ell ht he) := by
      intro j hj
      have hjF : j.val < F := by simpa [Sharpness.firstRows] using hj
      have hmargin : TieFreeTable.response u j (TieFreeTable.baseline p) + 1 ≤
          TieFreeTable.aggregate (TieFreeTable.baseline p) false u j (innerIndex n t ht) (lowerIndex m ell he) := by
        rw [hlow u hu j hjF]
        norm_num [TieFreeTable.response, TieFreeTable.baseline]
      have hstrict := hpres u j (innerIndex n t ht) (lowerIndex m ell he) hmargin
      rw [← vector_lowerEndpoint emb hinj z t ell ht he u j] at hstrict
      simp only [mem_filter, mem_univ, true_and]
      intro hc
      exact (not_le_of_gt hstrict) hc.1
    have hc := Finset.card_mono hs
    rw [Sharpness.firstRows_card hFn] at hc
    exact hc
  have hupper : (univ.filter fun u => Setup.failure A Z u F t ell ht he).card ≤ S.card := by
    rw [hsize]
    simpa only [RankFrontier.failureCount, RankFrontier.capacity] using
      DeterministicUpper.learner_failure_label_count_le A Z F t ell ht he
  have hset : S = univ.filter (fun u => Setup.failure A Z u F t ell ht he) :=
    Finset.eq_of_subset_of_card_le hselected hupper
  refine ⟨R, B, S, z, hsize, hz, actualTieFree_of_table emb hinj z htf t ell ht he, ?_⟩
  intro u
  rw [hset]
  simp only [mem_filter, mem_univ, true_and]
  rfl

/-- The attaining experiment can be chosen with an actual admissible learner
and an exchangeable law concentrated on arrays with all relevant ties absent. -/
theorem exists_tieFree_attaining_model (m n F t ell : ℕ) (hm : 1 ≤ m)
    (hF : 1 ≤ F) (hFn : F ≤ n) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m)
    (eta : ℝ) (heta : 0 < eta) (heta' : eta < 1/4) :
    ∃ (A : Learner UniversalCovariate n) (Z : Fin (m+1) → Block UniversalCovariate n),
      (∀ᵐ W ∂FiniteExchangeable.blockPermutationLaw Z, ActualTieFree A W t ell ht he) ∧
      (FiniteExchangeable.blockPermutationLaw Z).real
        {W | Setup.failure A W (Fin.last m) F t ell ht he} = RankFrontier.failureRate m F t ell := by
  let emb := unitEmbedding (m+1) n
  obtain ⟨R, B, S, z, hsize, hz, htf, hfail⟩ := exists_quantitative_tieFree_model
    m n F t ell hm hF hFn ht he emb emb.injective eta heta heta'
  let A := tableLearner (vectorPredictions z) emb
  let Z := vectorData emb z
  refine ⟨A, Z, actualTieFree_ae_permutationLaw htf, ?_⟩
  have hset : (univ.filter fun u => Setup.failure A Z u F t ell ht he) = S := by
    ext u
    simpa only [mem_filter, mem_univ, true_and] using hfail u
  have hp := FiniteExchangeable.blockPermutationLaw_equivariant_probability Z
    (fun W i => Setup.failure A W i F t ell ht he)
    (fun i => Setup.measurableSet_failure A i F t ell ht he)
    (SetupEquivariance.failure_equivariant A F t ell ht he) (Fin.last m)
  simpa only [hset, hsize, Fintype.card_fin, RankFrontier.failureRate] using hp

end
end MEJF.TieFreeSharpness
