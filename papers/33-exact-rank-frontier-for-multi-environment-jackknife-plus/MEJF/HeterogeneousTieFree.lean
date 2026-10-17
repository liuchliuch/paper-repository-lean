import MEJF.HeterogeneousLearner
import MEJF.TieFreeTable
import MEJF.FiniteExchangeable

/-! General-position perturbation for truly different block lengths. Every
actual coordinate is embedded in one finite rectangular primitive table. Inner
radii still sort only their own row coordinates, never padded coordinates. -/
namespace MEJF.HeterogeneousTieFree
open Finset MeasureTheory HeterogeneousSetup HeterogeneousLearner
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N : ℕ}

def padSize (n : Fin N → ℕ+) : ℕ := Fintype.card (CovariateTable n)
def pad (n : Fin N → ℕ+) (u : Fin N) (j : Fin (n u).val) : Fin (padSize n) :=
  Fintype.equivFin (CovariateTable n) ⟨u,j⟩

lemma pad_injective (n : Fin N → ℕ+) (u : Fin N) : Function.Injective (pad n u) := by
  intro j q h
  have hh := (Fintype.equivFin (CovariateTable n)).injective h
  exact eq_of_heq (Sigma.mk.inj_iff.mp hh).2

def paddedTable (n : Fin N → ℕ+) (p : PredictionTable n)
    (u v : Fin N) (j : Fin (padSize n)) : ℝ :=
  let q := (Fintype.equivFin (CovariateTable n)).symm j
  if q.1 = u then p q.1 v q.2 else 1

@[simp] lemma paddedTable_pad (n : Fin N → ℕ+) (p : PredictionTable n)
    (u v : Fin N) (j : Fin (n u).val) : paddedTable n p u v (pad n u j) = p u v j := by
  dsimp only [paddedTable,pad]
  rw [Equiv.symm_apply_apply]
  simp

lemma paddedTable_ge_one (n : Fin N → ℕ+) (p : PredictionTable n)
    (hp : ∀ u v j, 1 ≤ p u v j) : ∀ u v j, 1 ≤ paddedTable n p u v j := by
  intro u v j
  dsimp [paddedTable]
  split_ifs
  · exact hp _ _ _
  · exact le_rfl

abbrev Vector (n : Fin N → ℕ+) := TieFreeTable.Vector N (padSize n)
def Y (n : Fin N → ℕ+) (z : Vector n) (u : Fin N) (j : Fin (n u).val) : ℝ :=
  TieFreeTable.response u (pad n u j) z
def P (n : Fin N → ℕ+) (z : Vector n) : PredictionTable n :=
  fun u v j => TieFreeTable.prediction u v (pad n u j) z

def baseline (n : Fin N → ℕ+) (p : PredictionTable n) : Vector n :=
  TieFreeTable.baseline (paddedTable n p)

@[simp] lemma Y_baseline (n : Fin N → ℕ+) (p : PredictionTable n) (u : Fin N) (j : Fin (n u).val) :
    Y n (baseline n p) u j = 0 := rfl
@[simp] lemma P_baseline (n : Fin N → ℕ+) (p : PredictionTable n) (u v : Fin N) (j : Fin (n u).val) :
    P n (baseline n p) u v j = p u v j := by
  exact paddedTable_pad n p u v j

def radius (n : Fin N → ℕ+) (z : Vector n) (u v : Fin N) (k : Fin (n u).val) : ℝ :=
  OrderStatistics.stat (fun j => |Y n z u j-P n z u v j|) k

def candidate (n : Fin N → ℕ+) (z : Vector n) (upper : Bool)
    (u v : Fin N) (j : Fin (n u).val) (k : Fin (n v).val) : ℝ :=
  if upper then P n z u v j+radius n z v u k else P n z u v j-radius n z v u k

def aggregate {m : ℕ} (n : Fin (m+1) → ℕ+) (z : Vector n) (upper : Bool)
    (u : Fin (m+1)) (j : Fin (n u).val) (k : ∀ v, Fin (n v).val) (outer : Fin m) : ℝ :=
  OrderStatistics.stat (fun v : Fin m => candidate n z upper u (u.succAbove v) j (k _)) outer

lemma radius_eq_residual (n : Fin N → ℕ+) (z : Vector n)
    (hpos : ∀ u v j, Y n z u j ≤ P n z u v j) (u v : Fin N) (k : Fin (n u).val) :
    ∃ q : Fin (n u).val, radius n z u v k = TieFreeTable.residual u v (pad n u q) z := by
  unfold radius OrderStatistics.stat
  refine ⟨(Tuple.sort (fun j => |Y n z u j-P n z u v j|)) k, ?_⟩
  exact TieFreeTable.abs_residual_eq z u v _ (hpos u v _)

lemma candidate_eq_endpoint (n : Fin N → ℕ+) (z : Vector n)
    (hpos : ∀ u v j, Y n z u j ≤ P n z u v j) (upper : Bool)
    (u v : Fin N) (j : Fin (n u).val) (k : Fin (n v).val) :
    ∃ q : Fin (n v).val, candidate n z upper u v j k =
      TieFreeTable.endpoint upper u v (pad n u j) (pad n v q) z := by
  obtain ⟨q,hq⟩ := radius_eq_residual n z hpos v u k
  refine ⟨q, ?_⟩
  cases upper <;> simp [candidate,TieFreeTable.endpoint,P,hq]

/-- Actual dependent row radii and candidate endpoints, simultaneously at all ranks. -/
structure TieFree {m : ℕ} (n : Fin (m+1) → ℕ+) (z : Vector n) : Prop where
  residuals : ∀ u v, Function.Injective (fun j => |Y n z u j-P n z u v j|)
  comparisons : ∀ u v, u ≠ v → ∀ ku : Fin (n u).val, ∀ kv : Fin (n v).val,
    radius n z u v ku ≠ radius n z v u kv
  candidates : ∀ upper u v w, u ≠ v → u ≠ w → v ≠ w →
    ∀ j : Fin (n u).val, ∀ kv : Fin (n v).val, ∀ kw : Fin (n w).val,
      candidate n z upper u v j kv ≠ candidate n z upper u w j kw
  endpoints : ∀ upper u (j : Fin (n u).val) (k : ∀ v, Fin (n v).val) outer,
    aggregate n z upper u j k outer ≠ Y n z u j

lemma tieFree_of_generalPosition {m : ℕ} (n : Fin (m+1) → ℕ+) (z : Vector n)
    (hgp : TieFreeTable.GeneralPosition z)
    (hpos : ∀ u v j, Y n z u j ≤ P n z u v j) : TieFree n z := by
  constructor
  · intro u v j q he
    by_contra hjq
    apply TieFreeTable.residual_ne hgp u v (pad n u j) (pad n u q)
      (fun h => hjq (pad_injective n u h))
    simpa only [Y,P,TieFreeTable.abs_residual_eq _ _ _ _ (hpos _ _ _)] using he
  · intro u v huv ku kv
    obtain ⟨q,hq⟩ := radius_eq_residual n z hpos u v ku
    obtain ⟨r,hr⟩ := radius_eq_residual n z hpos v u kv
    rw [hq,hr]
    exact TieFreeTable.comparison_ne hgp u v huv _ _
  · intro upper u v w huv huw hvw j kv kw
    obtain ⟨q,hq⟩ := candidate_eq_endpoint n z hpos upper u v j kv
    obtain ⟨r,hr⟩ := candidate_eq_endpoint n z hpos upper u w j kw
    rw [hq,hr]
    exact TieFreeTable.endpoint_ne hgp upper u v w huv huw hvw _ _ _
  · intro upper u j k outer
    let v := (Tuple.sort (fun v : Fin m => candidate n z upper u (u.succAbove v) j (k _))) outer
    change candidate n z upper u (u.succAbove v) j (k _) ≠ Y n z u j
    obtain ⟨q,hq⟩ := candidate_eq_endpoint n z hpos upper u (u.succAbove v) j (k _)
    rw [hq]
    exact TieFreeTable.endpoint_ne_response hgp upper u _ (Fin.succAbove_ne _ _).symm _ _

lemma radius_perturbation (n : Fin N → ℕ+) (z z' : Vector n) (η : ℝ)
    (hz : ∀ a, |z' a-z a| ≤ η) (u v : Fin N) (k : Fin (n u).val) :
    |radius n z' u v k-radius n z u v k| ≤ 2*η :=
  TieRemoval.radius_perturbation _ _ _ _ k η
    (fun j => hz (.inl (u,pad n u j))) (fun j => hz (.inr (u,v,pad n u j)))

lemma candidate_perturbation (n : Fin N → ℕ+) (z z' : Vector n) (η : ℝ)
    (hz : ∀ a, |z' a-z a| ≤ η) (upper : Bool) (u v : Fin N)
    (j : Fin (n u).val) (k : Fin (n v).val) :
    |candidate n z' upper u v j k-candidate n z upper u v j k| ≤ 3*η := by
  cases upper
  · exact TieRemoval.lower_candidate_perturbation _ _ _ _ η
      (hz (.inr (u,v,pad n u j))) (radius_perturbation n z z' η hz v u k)
  · exact TieRemoval.upper_candidate_perturbation _ _ _ _ η
      (hz (.inr (u,v,pad n u j))) (radius_perturbation n z z' η hz v u k)

lemma aggregate_perturbation {m : ℕ} (n : Fin (m+1) → ℕ+) (z z' : Vector n) (η : ℝ)
    (hz : ∀ a, |z' a-z a| ≤ η) (upper : Bool) (u : Fin (m+1))
    (j : Fin (n u).val) (k : ∀ v, Fin (n v).val) (outer : Fin m) :
    |aggregate n z' upper u j k outer-aggregate n z upper u j k outer| ≤ 3*η :=
  OrderStatistics.stat_lipschitz _ _ outer _
    (fun v => candidate_perturbation n z z' η hz upper u (u.succAbove v) j _)

/-- One primitive perturbation works for unequal sizes, every inner rank tuple,
every outer rank, and every original lower unit-margin miss simultaneously. -/
theorem quantitative_tie_removal {m : ℕ} (n : Fin (m+1) → ℕ+) (p : PredictionTable n)
    (hp : ∀ u v j, 1 ≤ p u v j) (η : ℝ) (hη : 0 < η) (hη' : η < 1/4) :
    ∃ z : Vector n, (∀ a, |z a-baseline n p a| ≤ η) ∧ TieFree n z ∧
      ∀ u (j : Fin (n u).val) (k : ∀ v, Fin (n v).val) outer,
        Y n (baseline n p) u j+1 ≤ aggregate n (baseline n p) false u j k outer →
          Y n z u j < aggregate n z false u j k outer := by
  obtain ⟨z,hz,hgp⟩ := TieFreeTable.exists_general_position (baseline n p) η hη
  have hpos : ∀ u v j, Y n z u j ≤ P n z u v j := by
    intro u v j
    have hy := hz (.inl (u,pad n u j))
    have hpz := hz (.inr (u,v,pad n u j))
    change |Y n z u j-0| < η at hy
    change |P n z u v j-paddedTable n p u v (pad n u j)| < η at hpz
    rw [paddedTable_pad] at hpz
    have hh := hp u v j
    have hy' := (abs_lt.mp hy).2
    have hp' := (abs_lt.mp hpz).1
    linarith
  have hclose : ∀ a, |z a-baseline n p a| ≤ η := fun a => (hz a).le
  refine ⟨z,hclose,tieFree_of_generalPosition n z hgp hpos,?_⟩
  intro u j k outer hmarg
  exact TieRemoval.unit_failure_margin _ _ _ _ η hη' hmarg
    (aggregate_perturbation n _ z η hclose false u j k outer)
    (hclose (.inl (u,pad n u j)))

/-- Dependent complete blocks with the same covariates and arbitrary responses. -/
def modelDataWithResponses {X : Type*} (n : Fin N → ℕ+) (emb : CovariateTable n → X)
    (y : (u : Fin N) → Fin (n u).val → ℝ) : Fin N → Block X :=
  fun u => ⟨n u,fun j => (emb ⟨u,j⟩,y u j)⟩

def vectorData {X : Type*} (n : Fin N → ℕ+) (emb : CovariateTable n → X) (z : Vector n) :
    Fin N → Block X := modelDataWithResponses n emb (Y n z)

lemma contribution_congr_firstCov {X : Type*} (n : Fin N → ℕ+) (p : PredictionTable n)
    (emb : CovariateTable n → X) (Z W : Block X) (h : firstCov Z = firstCov W)
    (u : Fin N) (j : Fin (n u).val) :
    contribution n p emb Z u j = contribution n p emb W u j := by
  simp only [contribution,recognizes,h]

lemma tableAt_map_congr_firstCov {I X : Type*} (n : Fin N → ℕ+) (p : PredictionTable n)
    (emb : CovariateTable n → X) (s : Multiset I) (Z W : I → Block X)
    (h : ∀ i, firstCov (Z i) = firstCov (W i)) (u : Fin N) (j : Fin (n u).val) :
    tableAt n p emb (s.map Z) u j = tableAt n p emb (s.map W) u j := by
  unfold tableAt
  congr 1
  apply congrArg Multiset.sum
  simp only [Multiset.map_map,Function.comp_apply]
  apply Multiset.map_congr rfl
  intro i _
  exact contribution_congr_firstCov n p emb (Z i) (W i) (h i) u j

lemma predict_map_congr_firstCov {I X : Type*} (n : Fin N → ℕ+) (p : PredictionTable n)
    (emb : CovariateTable n → X) (s : Multiset I) (Z W : I → Block X)
    (h : ∀ i, firstCov (Z i) = firstCov (W i)) (x : X) :
    predict n p emb (s.map Z) x = predict n p emb (s.map W) x := by
  unfold predict
  apply Finset.sum_congr rfl
  intro q _
  rw [tableAt_map_congr_firstCov n p emb s Z W h]

section ActualModel
variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

/-- The all-arity dependent learner ignores every perturbed response. -/
lemma modelResponses_pairPrediction (n : Fin N → ℕ+) (p : PredictionTable n)
    (emb : CovariateTable n → X) (hinj : Function.Injective emb)
    (y : (u : Fin N) → Fin (n u).val → ℝ) (u v : Fin N) (huv : u ≠ v) (j : Fin (n u).val) :
    pairPrediction (learner n p emb) (modelDataWithResponses n emb y) u v (emb ⟨u,j⟩) = p u v j := by
  change predict n p emb (((univ.erase u).erase v).val.map (modelDataWithResponses n emb y))
    (emb ⟨u,j⟩) = _
  rw [predict_map_congr_firstCov n p emb _ (modelDataWithResponses n emb y) (modelData n emb)
    (by intro i; rfl)]
  exact model_pairPrediction n p emb hinj u v huv j

lemma vector_pairPrediction (n : Fin N → ℕ+) (emb : CovariateTable n → X)
    (hinj : Function.Injective emb) (z : Vector n) (u v : Fin N) (huv : u ≠ v) (j : Fin (n u).val) :
    pairPrediction (learner n (P n z) emb) (vectorData n emb z) u v (emb ⟨u,j⟩) = P n z u v j :=
  modelResponses_pairPrediction n _ emb hinj _ u v huv j

lemma vector_radius {m : ℕ} (n : Fin (m+1) → ℕ+) (emb : CovariateTable n → X)
    (hinj : Function.Injective emb) (z : Vector n) (t : Fin (m+1) → ℕ)
    (ht : ∀ u, 1 ≤ t u ∧ t u ≤ (n u).val) (u v : Fin (m+1)) (huv : u ≠ v) :
    HeterogeneousSetup.radius (learner n (P n z) emb) (vectorData n emb z) t ht u v =
      radius n z u v (Setup.innerIndex (n u).val (t u) (ht u)) := by
  unfold HeterogeneousSetup.radius HeterogeneousSetup.score
  change OrderStatistics.stat (fun j => |Y n z u j-
    pairPrediction (learner n (P n z) emb) (vectorData n emb z) u v (emb ⟨u,j⟩)|) _ = _
  simp_rw [vector_pairPrediction n emb hinj z u v huv]
  rfl

lemma vector_lowerEndpoint {m : ℕ} (n : Fin (m+1) → ℕ+) (emb : CovariateTable n → X)
    (hinj : Function.Injective emb) (z : Vector n) (t : Fin (m+1) → ℕ)
    (ht : ∀ u, 1 ≤ t u ∧ t u ≤ (n u).val) (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m)
    (u : Fin (m+1)) (j : Fin (n u).val) :
    HeterogeneousSetup.lowerEndpoint (learner n (P n z) emb) (vectorData n emb z) t ht ell he u j =
      aggregate n z false u j (fun v => Setup.innerIndex (n v).val (t v) (ht v)) (Setup.lowerIndex m ell he) := by
  unfold HeterogeneousSetup.lowerEndpoint HeterogeneousSetup.lower aggregate
  apply congrArg (fun q : Fin m → ℝ => OrderStatistics.stat q (Setup.lowerIndex m ell he))
  funext v
  change pairPrediction (learner n (P n z) emb) (vectorData n emb z) u (u.succAbove v) (emb ⟨u,j⟩)-
    HeterogeneousSetup.radius (learner n (P n z) emb) (vectorData n emb z) t ht (u.succAbove v) u = _
  rw [vector_pairPrediction n emb hinj z u _ (Fin.succAbove_ne _ _).symm,
    vector_radius n emb hinj z t ht _ u (Fin.succAbove_ne _ _)]
  rfl

lemma vector_upperEndpoint {m : ℕ} (n : Fin (m+1) → ℕ+) (emb : CovariateTable n → X)
    (hinj : Function.Injective emb) (z : Vector n) (t : Fin (m+1) → ℕ)
    (ht : ∀ u, 1 ≤ t u ∧ t u ≤ (n u).val) (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m)
    (u : Fin (m+1)) (j : Fin (n u).val) :
    HeterogeneousSetup.upperEndpoint (learner n (P n z) emb) (vectorData n emb z) t ht ell he u j =
      aggregate n z true u j (fun v => Setup.innerIndex (n v).val (t v) (ht v)) (Setup.upperIndex m ell he) := by
  unfold HeterogeneousSetup.upperEndpoint HeterogeneousSetup.upper aggregate
  apply congrArg (fun q : Fin m → ℝ => OrderStatistics.stat q (Setup.upperIndex m ell he))
  funext v
  change pairPrediction (learner n (P n z) emb) (vectorData n emb z) u (u.succAbove v) (emb ⟨u,j⟩)+
    HeterogeneousSetup.radius (learner n (P n z) emb) (vectorData n emb z) t ht (u.succAbove v) u = _
  rw [vector_pairPrediction n emb hinj z u _ (Fin.succAbove_ne _ _).symm,
    vector_radius n emb hinj z t ht _ u (Fin.succAbove_ne _ _)]
  rfl

end ActualModel

end
end MEJF.HeterogeneousTieFree
