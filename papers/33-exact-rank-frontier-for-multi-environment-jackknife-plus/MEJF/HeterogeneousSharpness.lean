import MEJF.HeterogeneousLearner
import MEJF.Sharpness

/-! Exact heterogeneous incidence extremizers and their actual fitted learner. -/
namespace MEJF.HeterogeneousSharpness
open Finset Incidence HeterogeneousSetup HeterogeneousLearner OrderStatistics
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {m : ℕ}

/-- The sorted Hall maximum is realized together with one genuine incidence
matrix of the correct dimensions for every selected size type. -/
theorem exists_graph_matrices (F t : Fin (m+1) → ℕ)
    (ht : ∀ i, 1 ≤ t i) (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) :
    ∃ (R : Fin (m+1) → Fin (m+1) → Prop) (S : Finset (Fin (m+1)))
      (A : (u : Fin (m+1)) → Fin (F u) → Fin m → Prop),
      (∀ u v, R u v → ¬ R v u) ∧ S.card = HeterogeneousFrontier.sStar (demand F t ell) ∧
      (∀ u ∈ S, ∀ r, rowSum (A u) r = m+1-ell) ∧
      (∀ u k, R u (u.succAbove k) → t u ≤ colSum (A u) k) ∧
      (∀ u k, ¬ R u (u.succAbove k) → colSum (A u) k < t u) ∧
      (∀ u ∉ S, ∀ r k, ¬ A u r k) := by
  classical
  obtain ⟨S,hScard,R,hR,hdeg,hzero⟩ := HeterogeneousFrontier.sStar_attained (demand F t ell)
  have hno : ∀ u ∉ S, ∀ v, ¬ R u v := by
    intro u hu v hv
    have hp : 0 < GraphBound.outDegree R u := by
      exact card_pos.mpr ⟨v,mem_filter.mpr ⟨mem_univ _,hv⟩⟩
    rw [hzero u hu] at hp
    omega
  have hmats : ∀ u : Fin (m+1), ∃ M : Fin (F u) → Fin m → Prop,
      (u ∈ S → (∀ r, rowSum M r = m+1-ell) ∧
        (∀ k, R u (u.succAbove k) → t u ≤ colSum M k) ∧
        (∀ k, ¬ R u (u.succAbove k) → colSum M k < t u)) ∧
      (u ∉ S → ∀ r k, ¬ M r k) := by
    intro u
    by_cases hu : u ∈ S
    · let marked : Finset (Fin m) := univ.filter fun k => R u (u.succAbove k)
      have hmarked : marked.card = if F u < t u then 0 else
          threshold (F u) (Fintype.card (Fin m)) (m+1-ell) (t u) := by
        have hd := Sharpness.marked_card_eq_degree R hR u
        change marked.card = _ at hd
        have hdegu : ExtremalGraph.outdegree R u = demand F t ell u := hdeg u hu
        simpa only [demand,Fintype.card_fin] using hd.trans hdegu
      obtain ⟨M,hrow,hmark,hunmark⟩ := realize_frontier (F u) (m+1-ell) (t u) marked
        (ht u) (by simp; omega) hmarked
      refine ⟨M,fun _ => ⟨hrow,?_,?_⟩,by simp [hu]⟩
      · intro k hk
        exact hmark k (by simp [marked,hk])
      · intro k hk
        have h := hunmark k (by simp [marked,hk])
        have := ht u
        omega
    · exact ⟨fun _ _ => False,by simp [hu],by simp⟩
  choose A hA using hmats
  refine ⟨R,S,A,hR,hScard,?_,?_,?_,?_⟩
  · intro u hu
    exact ((hA u).1 hu).1
  · intro u k hk
    by_cases hu : u ∈ S
    · exact ((hA u).1 hu).2.1 k hk
    · exact False.elim (hno u hu _ hk)
  · intro u k hk
    by_cases hu : u ∈ S
    · exact ((hA u).1 hu).2.2 k hk
    · have hz : colSum (A u) k = 0 := by simp [colSum,(hA u).2 hu]
      rw [hz]
      exact ht u
  · intro u hu
    exact (hA u).2 hu

/-- Extend every size type's incidence matrix to its own full coordinate set. -/
def bits (n : Fin (m+1) → ℕ+) (F : Fin (m+1) → ℕ)
    (A : (u : Fin (m+1)) → Fin (F u) → Fin m → Prop)
    (u : Fin (m+1)) (j : Fin (n u).val) (v : Fin (m+1)) : Bool :=
  if hv : v ≠ u then Sharpness.extendRows (A u) j ((Sharpness.otherEquiv u).symm ⟨v,hv⟩)
  else false

lemma bits_other (n : Fin (m+1) → ℕ+) (F : Fin (m+1) → ℕ)
    (A : (u : Fin (m+1)) → Fin (F u) → Fin m → Prop)
    (u : Fin (m+1)) (j : Fin (n u).val) (k : Fin m) :
    bits n F A u j (u.succAbove k) = Sharpness.extendRows (A u) j k := by
  simp [bits]

lemma bits_column (n : Fin (m+1) → ℕ+) (F : Fin (m+1) → ℕ)
    (hFn : ∀ u, F u ≤ (n u).val)
    (A : (u : Fin (m+1)) → Fin (F u) → Fin m → Prop) (u : Fin (m+1)) (k : Fin m) :
    (univ.filter fun j => bits n F A u j (u.succAbove k) = true).card = colSum (A u) k := by
  simp only [bits_other]
  exact Sharpness.extendRows_column (hFn u) (A u) k

/-- The original 1/2/3 prediction table with the actual label-dependent dimensions. -/
def table (n : Fin (m+1) → ℕ+) (R : Fin (m+1) → Fin (m+1) → Prop)
    (B : (u : Fin (m+1)) → Fin (n u).val → Fin (m+1) → Bool) : PredictionTable n :=
  fun u v j => if B u j v then if R v u then 3 else 2 else 1

lemma table_pos (n : Fin (m+1) → ℕ+) (R : Fin (m+1) → Fin (m+1) → Prop)
    (B : (u : Fin (m+1)) → Fin (n u).val → Fin (m+1) → Bool)
    (u v : Fin (m+1)) (j : Fin (n u).val) : 0 < table n R B u v j := by
  unfold table
  split_ifs <;> norm_num

lemma table_ge_one (n : Fin (m+1) → ℕ+) (R : Fin (m+1) → Fin (m+1) → Prop)
    (B : (u : Fin (m+1)) → Fin (n u).val → Fin (m+1) → Bool)
    (u v : Fin (m+1)) (j : Fin (n u).val) : 1 ≤ table n R B u v j := by
  unfold table
  split_ifs <;> norm_num

lemma table_count_gt_one (n : Fin (m+1) → ℕ+) (R : Fin (m+1) → Fin (m+1) → Prop)
    (B : (u : Fin (m+1)) → Fin (n u).val → Fin (m+1) → Bool) (u v : Fin (m+1)) :
    count (table n R B u v) (1 < ·) = (univ.filter fun j => B u j v = true).card := by
  unfold count
  congr 1
  ext j
  simp only [mem_filter,mem_univ,true_and]
  by_cases hR : R v u <;> cases hB : B u j v <;> simp [table,hR,hB]

lemma table_radius (n : Fin (m+1) → ℕ+) (R : Fin (m+1) → Fin (m+1) → Prop)
    (hR : ∀ u v, R u v → ¬ R v u)
    (B : (u : Fin (m+1)) → Fin (n u).val → Fin (m+1) → Bool)
    (t : Fin (m+1) → ℕ) (ht : ∀ u, 1 ≤ t u ∧ t u ≤ (n u).val)
    (hmark : ∀ u v, R u v → t u ≤ (univ.filter fun j => B u j v = true).card)
    (hunmark : ∀ u v, ¬ R u v → (univ.filter fun j => B u j v = true).card < t u)
    (u v : Fin (m+1)) :
    stat (table n R B u v) (Setup.innerIndex (n u).val (t u) (ht u)) =
      if R u v then 2 else 1 := by
  by_cases huv : R u v
  · simp only [if_pos huv]
    apply PredictionTable.stat_eq_two_of_many _ (ht u).1 (ht u).2
    · intro j
      cases hB : B u j v <;> simp [table,hB,hR u v huv]
    · rw [table_count_gt_one]
      exact hmark u v huv
  · simp only [if_neg huv]
    apply PredictionTable.stat_eq_one_of_few_above _ (ht u).1 (ht u).2
    · exact table_ge_one n R B u v
    · rw [table_count_gt_one]
      exact hunmark u v huv

/-- All incidence constraints for the exact Hall maximum, with each label's own
coordinate and rank dimensions. -/
theorem exists_sharpness_bits (n : Fin (m+1) → ℕ+) (F t : Fin (m+1) → ℕ)
    (hFn : ∀ u, F u ≤ (n u).val) (ht : ∀ u, 1 ≤ t u)
    (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) :
    ∃ (R : Fin (m+1) → Fin (m+1) → Prop) (S : Finset (Fin (m+1)))
      (B : (u : Fin (m+1)) → Fin (n u).val → Fin (m+1) → Bool),
      (∀ u v, R u v → ¬ R v u) ∧ S.card = HeterogeneousFrontier.sStar (demand F t ell) ∧
      (∀ u v, R u v → t u ≤ (univ.filter fun j => B u j v = true).card) ∧
      (∀ u v, ¬ R u v → (univ.filter fun j => B u j v = true).card < t u) ∧
      (∀ u ∈ S, ∀ j, j.val < F u →
        (univ.filter fun k : Fin m => B u j (u.succAbove k) = false).card = ell-1) ∧
      (∀ u j, u ∉ S ∨ F u ≤ j.val → ∀ k : Fin m, B u j (u.succAbove k) = false) := by
  obtain ⟨R,S,A,hR,hS,hrow,hmark,hunmark,hzero⟩ := exists_graph_matrices F t ht ell he
  refine ⟨R,S,bits n F A,hR,hS,?_,?_,?_,?_⟩
  · intro u v huv
    have hvu : v ≠ u := by intro h; subst v; exact hR u u huv huv
    obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hvu
    rw [bits_column n F hFn A]
    exact hmark u k huv
  · intro u v huv
    by_cases hvu : v = u
    · subst v
      have hz : (univ.filter fun j => bits n F A u j u = true).card = 0 := by simp [bits]
      rw [hz]
      exact ht u
    · obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hvu
      rw [bits_column n F hFn A]
      exact hunmark u k huv
  · intro u hu j hj
    have htrue : (univ.filter fun k : Fin m => bits n F A u j (u.succAbove k) = true).card =
        m+1-ell := by
      simpa [bits_other,Sharpness.extendRows,hj,rowSum] using hrow u hu ⟨j.val,hj⟩
    have hpart := filter_card_add_filter_neg_card_eq_card
      (s := (univ : Finset (Fin m)))
      (p := fun k => bits n F A u j (u.succAbove k) = true)
    simp only [Bool.not_eq_true,card_univ,Fintype.card_fin] at hpart
    omega
  · intro u j hor k
    rcases hor with hu | hj
    · rw [bits_other]
      unfold Sharpness.extendRows
      split_ifs with hj
      · simp [hzero u hu]
      · rfl
    · rw [bits_other]
      simp [Sharpness.extendRows,show ¬ j.val < F u by omega]


section Model
variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

/-- Actual residual order statistics for an arbitrary dependent prediction table. -/
theorem model_radius (n : Fin (m+1) → ℕ+) (p : PredictionTable n)
    (emb : CovariateTable n → X) (hinj : Function.Injective emb)
    (t : Fin (m+1) → ℕ) (ht : ∀ u, 1 ≤ t u ∧ t u ≤ (n u).val)
    (u v : Fin (m+1)) (huv : u ≠ v) :
    radius (learner n p emb) (modelData n emb) t ht u v =
      stat (fun j => |p u v j|) (Setup.innerIndex (n u).val (t u) (ht u)) := by
  unfold radius score learnerResponses learnerPredictions
  change stat (fun j => |0-pairPrediction (learner n p emb) (modelData n emb) u v (emb ⟨u,j⟩)|) _ = _
  simp_rw [HeterogeneousLearner.model_pairPrediction n p emb hinj u v huv]
  simp only [zero_sub,abs_neg]
  rfl

/-- Every actual inner score equals the prescribed one/two graph score. -/
theorem model_radius_incidence (n : Fin (m+1) → ℕ+)
    (R : Fin (m+1) → Fin (m+1) → Prop) (hR : ∀ u v, R u v → ¬ R v u)
    (B : (u : Fin (m+1)) → Fin (n u).val → Fin (m+1) → Bool)
    (emb : CovariateTable n → X) (hinj : Function.Injective emb)
    (t : Fin (m+1) → ℕ) (ht : ∀ u, 1 ≤ t u ∧ t u ≤ (n u).val)
    (hmark : ∀ u v, R u v → t u ≤ (univ.filter fun j => B u j v = true).card)
    (hunmark : ∀ u v, ¬ R u v → (univ.filter fun j => B u j v = true).card < t u)
    (u v : Fin (m+1)) (huv : u ≠ v) :
    radius (learner n (table n R B) emb) (modelData n emb) t ht u v = if R u v then 2 else 1 := by
  rw [model_radius n (table n R B) emb hinj t ht u v huv]
  simp_rw [abs_of_pos (table_pos n R B u v _)]
  exact table_radius n R hR B t ht hmark hunmark u v

/-- Substitution of the actual fitted predictions and opposite-label scores. -/
theorem model_lowerEndpoint (n : Fin (m+1) → ℕ+)
    (R : Fin (m+1) → Fin (m+1) → Prop) (hR : ∀ u v, R u v → ¬ R v u)
    (B : (u : Fin (m+1)) → Fin (n u).val → Fin (m+1) → Bool)
    (emb : CovariateTable n → X) (hinj : Function.Injective emb)
    (t : Fin (m+1) → ℕ) (ht : ∀ u, 1 ≤ t u ∧ t u ≤ (n u).val)
    (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m)
    (hmark : ∀ u v, R u v → t u ≤ (univ.filter fun j => B u j v = true).card)
    (hunmark : ∀ u v, ¬ R u v → (univ.filter fun j => B u j v = true).card < t u)
    (u : Fin (m+1)) (j : Fin (n u).val) :
    lowerEndpoint (learner n (table n R B) emb) (modelData n emb) t ht ell he u j =
      stat (fun k : Fin m => table n R B u (u.succAbove k) j-
        if R (u.succAbove k) u then 2 else 1) (Setup.lowerIndex m ell he) := by
  unfold lowerEndpoint lower
  congr 1
  funext k
  change pairPrediction (learner n (table n R B) emb) (modelData n emb)
    u (u.succAbove k) (emb ⟨u,j⟩)-radius (learner n (table n R B) emb) (modelData n emb)
      t ht (u.succAbove k) u = _
  rw [HeterogeneousLearner.model_pairPrediction n (table n R B) emb hinj u (u.succAbove k)
    (u.ne_succAbove k) j,model_radius_incidence n R hR B emb hinj t ht hmark hunmark
      (u.succAbove k) u (u.succAbove_ne k)]

theorem model_upperEndpoint (n : Fin (m+1) → ℕ+)
    (R : Fin (m+1) → Fin (m+1) → Prop) (hR : ∀ u v, R u v → ¬ R v u)
    (B : (u : Fin (m+1)) → Fin (n u).val → Fin (m+1) → Bool)
    (emb : CovariateTable n → X) (hinj : Function.Injective emb)
    (t : Fin (m+1) → ℕ) (ht : ∀ u, 1 ≤ t u ∧ t u ≤ (n u).val)
    (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m)
    (hmark : ∀ u v, R u v → t u ≤ (univ.filter fun j => B u j v = true).card)
    (hunmark : ∀ u v, ¬ R u v → (univ.filter fun j => B u j v = true).card < t u)
    (u : Fin (m+1)) (j : Fin (n u).val) :
    upperEndpoint (learner n (table n R B) emb) (modelData n emb) t ht ell he u j =
      stat (fun k : Fin m => table n R B u (u.succAbove k) j+
        if R (u.succAbove k) u then 2 else 1) (Setup.upperIndex m ell he) := by
  unfold upperEndpoint upper
  congr 1
  funext k
  change pairPrediction (learner n (table n R B) emb) (modelData n emb)
    u (u.succAbove k) (emb ⟨u,j⟩)+radius (learner n (table n R B) emb) (modelData n emb)
      t ht (u.succAbove k) u = _
  rw [HeterogeneousLearner.model_pairPrediction n (table n R B) emb hinj u (u.succAbove k)
    (u.ne_succAbove k) j,model_radius_incidence n R hR B emb hinj t ht hmark hunmark
      (u.succAbove k) u (u.succAbove_ne k)]

/-- Unit lower-endpoint separation on every selected coordinate of a model. -/
theorem selected_lowerEndpoint_eq_one (n : Fin (m+1) → ℕ+)
    (R : Fin (m+1) → Fin (m+1) → Prop) (hR : ∀ u v, R u v → ¬ R v u)
    (B : (u : Fin (m+1)) → Fin (n u).val → Fin (m+1) → Bool)
    (emb : CovariateTable n → X) (hinj : Function.Injective emb)
    (t : Fin (m+1) → ℕ) (ht : ∀ u, 1 ≤ t u ∧ t u ≤ (n u).val)
    (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m)
    (hmark : ∀ u v, R u v → t u ≤ (univ.filter fun j => B u j v = true).card)
    (hunmark : ∀ u v, ¬ R u v → (univ.filter fun j => B u j v = true).card < t u)
    (u : Fin (m+1)) (j : Fin (n u).val)
    (hrow : (univ.filter fun k : Fin m => B u j (u.succAbove k) = false).card = ell-1) :
    lowerEndpoint (learner n (table n R B) emb) (modelData n emb) t ht ell he u j = 1 := by
  rw [model_lowerEndpoint n R hR B emb hinj t ht ell he hmark hunmark u j]
  exact PredictionTable.incidence_lower_endpoint R (fun _ j v => B u j v) u j u.succAbove
    he.1 he.2 hrow

/-- Zero-incidence coordinates cover the zero response under actual endpoints. -/
theorem zero_coordinate_covered (n : Fin (m+1) → ℕ+)
    (R : Fin (m+1) → Fin (m+1) → Prop) (hR : ∀ u v, R u v → ¬ R v u)
    (B : (u : Fin (m+1)) → Fin (n u).val → Fin (m+1) → Bool)
    (emb : CovariateTable n → X) (hinj : Function.Injective emb)
    (t : Fin (m+1) → ℕ) (ht : ∀ u, 1 ≤ t u ∧ t u ≤ (n u).val)
    (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m)
    (hmark : ∀ u v, R u v → t u ≤ (univ.filter fun j => B u j v = true).card)
    (hunmark : ∀ u v, ¬ R u v → (univ.filter fun j => B u j v = true).card < t u)
    (u : Fin (m+1)) (j : Fin (n u).val) (hzero : ∀ k : Fin m, B u j (u.succAbove k) = false) :
    lowerEndpoint (learner n (table n R B) emb) (modelData n emb) t ht ell he u j ≤ 0 ∧
      0 ≤ upperEndpoint (learner n (table n R B) emb) (modelData n emb) t ht ell he u j := by
  rw [model_lowerEndpoint n R hR B emb hinj t ht ell he hmark hunmark u j,
    model_upperEndpoint n R hR B emb hinj t ht ell he hmark hunmark u j]
  exact PredictionTable.incidence_zero_coordinate_covered R (fun _ j v => B u j v) u j
    u.succAbove hzero (Setup.lowerIndex m ell he) (Setup.upperIndex m ell he)

/-- The exact sorted frontier is attained by an actual all-arity measurable
learner and the original variable-length zero-response block types. -/
theorem exists_exact_failure_count_model (n : Fin (m+1) → ℕ+) (F t : Fin (m+1) → ℕ)
    (hF : ∀ u, 1 ≤ F u ∧ F u ≤ (n u).val)
    (ht : ∀ u, 1 ≤ t u ∧ t u ≤ (n u).val) (ell : ℕ)
    (he : 1 ≤ ell ∧ ell ≤ m) (emb : CovariateTable n → X) (hinj : Function.Injective emb) :
    ∃ A : Learner X,
      (univ.filter fun u => learnerFailure A (modelData n emb) F t ht ell he u).card =
        HeterogeneousFrontier.sStar (demand F t ell) := by
  obtain ⟨R,S,B,hR,hS,hmark,hunmark,hrows,hzero⟩ := exists_sharpness_bits n F t
    (fun u => (hF u).2) (fun u => (ht u).1) ell he
  let A := learner n (table n R B) emb
  have hfail : ∀ u, learnerFailure A (modelData n emb) F t ht ell he u ↔ u ∈ S := by
    intro u
    by_cases hu : u ∈ S
    · constructor
      · intro _; exact hu
      · intro _
        unfold learnerFailure HeterogeneousSetup.failure
        rw [← Sharpness.firstRows_card (hF u).2]
        apply card_le_card
        intro j hj
        have hjF : j.val < F u := (mem_filter.mp hj).2
        have hl := selected_lowerEndpoint_eq_one n R hR B emb hinj t ht ell he hmark hunmark
          u j (hrows u hu j hjF)
        apply mem_filter.mpr
        refine ⟨mem_univ _,?_⟩
        intro hc
        have hc' : lowerEndpoint A (modelData n emb) t ht ell he u j ≤ 0 := hc.1
        rw [hl] at hc'
        norm_num at hc'
    · constructor
      · intro hf
        have hall : ∀ j, covered (fun k => size (modelData n emb k))
            (learnerResponses (modelData n emb)) (learnerPredictions A (modelData n emb))
            t ht ell he u j := by
          intro j
          exact zero_coordinate_covered n R hR B emb hinj t ht ell he hmark hunmark u j
            (hzero u j (Or.inl hu))
        unfold learnerFailure HeterogeneousSetup.failure at hf
        have hemt : (univ.filter fun j => ¬ covered (fun k => size (modelData n emb k))
            (learnerResponses (modelData n emb)) (learnerPredictions A (modelData n emb))
            t ht ell he u j) = ∅ := by
          ext j
          simp [hall j]
        rw [hemt] at hf
        simp only [card_empty] at hf
        have := (hF u).1
        omega
      · intro hu'; exact False.elim (hu hu')
  refine ⟨A,?_⟩
  have hset : (univ.filter fun u => learnerFailure A (modelData n emb) F t ht ell he u) = S := by
    ext u
    simpa only [mem_filter,mem_univ,true_and] using hfail u
  rw [hset]
  exact hS


/-- The same attaining model with the original source floor ranks, rather than
independently supplied integer vectors. -/
theorem source_exists_exact_failure_count_model (n : Fin (m+1) → ℕ+)
    (alpha a : ℝ) (ha : 0 ≤ alpha) (ha1 : alpha < 1) (ell : ℕ)
    (ht : ∀ u, 1 ≤ ⌊a*((n u).val+1)⌋₊ ∧ ⌊a*((n u).val+1)⌋₊ ≤ (n u).val)
    (he : 1 ≤ ell ∧ ell ≤ m) (emb : CovariateTable n → X) (hinj : Function.Injective emb) :
    ∃ A : Learner X,
      (univ.filter fun u => learnerFailure A (modelData n emb)
        (failureRank alpha (modelData n emb)) (innerRank a (modelData n emb)) ht ell he u).card =
      realizedFrontier alpha a ell (modelData n emb) := by
  let F : Fin (m+1) → ℕ := fun u => ⌊alpha*(n u).val⌋₊+1
  let t : Fin (m+1) → ℕ := fun u => ⌊a*((n u).val+1)⌋₊
  have hF : ∀ u, 1 ≤ F u ∧ F u ≤ (n u).val := by
    intro u
    have hn : (0:ℝ) < (n u).val := by exact_mod_cast (n u).property
    have hx : alpha*(n u).val < (n u).val := by nlinarith
    have hh := (Nat.floor_lt (mul_nonneg ha hn.le)).mpr hx
    dsimp [F]
    omega
  obtain ⟨A,hA⟩ := exists_exact_failure_count_model n F t hF ht ell he emb hinj
  exact ⟨A,hA⟩

end Model

end
end MEJF.HeterogeneousSharpness
