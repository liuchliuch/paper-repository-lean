import MEJF.HeterogeneousSetup
import MEJF.MeasurableSigma
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Positivity

/-! A genuine all-arity measurable variable-block learner realizing every
finite dependent pair-prediction table. -/
namespace MEJF.HeterogeneousLearner
open Finset MeasureTheory HeterogeneousSetup
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N : ℕ} (n : Fin N → ℕ+) {X : Type*}

abbrev CovariateTable := Σ u : Fin N, Fin (n u).val
abbrev PredictionTable := (u v : Fin N) → Fin (n u).val → ℝ

/-- A measurable type probe available on every positive-length complete block. -/
def firstCov (Z : Block X) : X := (Z.2 ⟨0,Z.1.property⟩).1

lemma measurable_firstCov [MeasurableSpace X] : Measurable (firstCov : Block X → X) := by
  apply MEJF.MeasurableSigma.measurable_sigma_iff.mpr
  intro r
  exact (measurable_pi_apply (⟨0,r.property⟩ : Fin r.val)).fst

def modelData (emb : CovariateTable n → X) : Fin N → Block X :=
  fun u => ⟨n u,fun j => (emb ⟨u,j⟩,0)⟩

def recognizes (emb : CovariateTable n → X) (Z : Block X) (u : Fin N) : Prop :=
  firstCov Z = emb ⟨u,⟨0,(n u).property⟩⟩

lemma recognizes_modelData (emb : CovariateTable n → X) (hinj : Function.Injective emb)
    (u v : Fin N) : recognizes n emb (modelData n emb u) v ↔ u = v := by
  constructor
  · intro h
    exact congrArg Sigma.fst (hinj h)
  · rintro rfl
    rfl

def tableConstant (p : PredictionTable n) (u : Fin N) (j : Fin (n u).val) : ℝ :=
  ∑ v ∈ univ.erase u, p u v j

def contribution (p : PredictionTable n) (emb : CovariateTable n → X)
    (Z : Block X) (u : Fin N) (j : Fin (n u).val) : ℝ :=
  ∑ v ∈ univ.erase u, if recognizes n emb Z v then p u v j else 0

def tableAt (p : PredictionTable n) (emb : CovariateTable n → X)
    (T : Multiset (Block X)) (u : Fin N) (j : Fin (n u).val) : ℝ :=
  tableConstant n p u j-(T.map fun Z => contribution n p emb Z u j).sum

def predict (p : PredictionTable n) (emb : CovariateTable n → X)
    (T : Multiset (Block X)) (x : X) : ℝ :=
  ∑ q : CovariateTable n, if emb q = x then tableAt n p emb T q.1 q.2 else 0

lemma predict_at (p : PredictionTable n) (emb : CovariateTable n → X)
    (hinj : Function.Injective emb) (T : Multiset (Block X)) (u : Fin N) (j : Fin (n u).val) :
    predict n p emb T (emb ⟨u,j⟩) = tableAt n p emb T u j := by
  simp [predict,hinj.eq_iff]

lemma contribution_modelData (p : PredictionTable n) (emb : CovariateTable n → X)
    (hinj : Function.Injective emb) (u v : Fin N) (j : Fin (n u).val) :
    contribution n p emb (modelData n emb v) u j = if v = u then 0 else p u v j := by
  simp only [contribution,recognizes_modelData n emb hinj]
  by_cases h : v = u
  · subst v; simp
  · simp [h]

section Measurable
variable [MeasurableSpace X] [MeasurableSingletonClass X]

lemma measurable_contribution (p : PredictionTable n) (emb : CovariateTable n → X)
    (u : Fin N) (j : Fin (n u).val) :
    Measurable (fun Z : Block X => contribution n p emb Z u j) := by
  unfold contribution
  apply Finset.measurable_sum
  intro v hv
  apply Measurable.ite _ measurable_const measurable_const
  exact (measurableSet_singleton (emb ⟨v,⟨0,(n v).property⟩⟩)).preimage measurable_firstCov

lemma measurable_at (p : PredictionTable n) (emb : CovariateTable n → X)
    (r : ℕ) (u : Fin N) (j : Fin (n u).val) :
    Measurable (fun T : Fin r → Block X =>
      tableAt n p emb ((List.ofFn T : List (Block X)) : Multiset (Block X)) u j) := by
  have hform : (fun T : Fin r → Block X =>
      tableAt n p emb ((List.ofFn T : List (Block X)) : Multiset (Block X)) u j) =
      fun T => tableConstant n p u j-∑ i, contribution n p emb (T i) u j := by
    funext T
    simp [tableAt,List.map_ofFn,List.sum_ofFn]
  rw [hform]
  apply measurable_const.sub
  apply Finset.measurable_sum
  intro i hi
  exact (measurable_contribution n p emb u j).comp (measurable_pi_apply i)

lemma measurable_predict (p : PredictionTable n) (emb : CovariateTable n → X) (r : ℕ) :
    Measurable (fun q : (Fin r → Block X) × X =>
      predict n p emb ((List.ofFn q.1 : List (Block X)) : Multiset (Block X)) q.2) := by
  unfold predict
  apply Finset.measurable_sum
  intro uj huj
  apply Measurable.ite
  · simpa only [eq_comm] using (measurableSet_singleton (emb uj)).preimage measurable_snd
  · exact (measurable_at n p emb r uj.1 uj.2).comp measurable_fst
  · exact measurable_const

/-- One admissible learner on all positive-size complete blocks, retaining
multiplicities and measurable jointly tableAt every training arity. -/
def learner (p : PredictionTable n) (emb : CovariateTable n → X) : Learner X where
  predict := predict n p emb
  measurable_predict := measurable_predict n p emb

/-- All pair-deletion fits return the prescribed dependent table entries. -/
theorem model_pairPrediction (p : PredictionTable n) (emb : CovariateTable n → X)
    (hinj : Function.Injective emb) (u v : Fin N) (huv : u ≠ v) (j : Fin (n u).val) :
    pairPrediction (learner n p emb) (modelData n emb) u v (emb ⟨u,j⟩) = p u v j := by
  have hv : v ∈ (univ : Finset (Fin N)).erase u := by simp [Ne.symm huv]
  have hsum : (∑ w ∈ ((univ : Finset (Fin N)).erase u).erase v, p u w j)+p u v j =
      tableConstant n p u j := sum_erase_add _ _ hv
  change predict n p emb _ (emb ⟨u,j⟩) = _
  rw [predict_at n p emb hinj]
  unfold tableAt
  simp only [Multiset.map_map,Function.comp_apply,contribution_modelData n p emb hinj]
  have hterm : ∀ w ∈ ((univ : Finset (Fin N)).erase u).erase v,
      (if w = u then (0:ℝ) else p u w j) = p u w j := by
    intro w hw
    have hwu : w ≠ u := (mem_erase.mp (mem_erase.mp hw).2).1
    simp [hwu]
  change tableConstant n p u j-(∑ w ∈ ((univ : Finset (Fin N)).erase u).erase v,
    if w = u then (0:ℝ) else p u w j) = _
  rw [Finset.sum_congr rfl hterm]
  linarith

end Measurable

/-- Embed all dependent finite coordinates into the paper's universal [0,1]. -/
def unitEmbedding : CovariateTable n ↪ Setup.UniversalCovariate where
  toFun q := ⟨((Fintype.equivFin (CovariateTable n) q).val : ℝ) /
      (Fintype.card (CovariateTable n)+1),by
    have hd : (0:ℝ) < Fintype.card (CovariateTable n)+1 := by positivity
    constructor
    · positivity
    · apply (div_le_one hd).mpr
      have hlt := (Fintype.equivFin (CovariateTable n) q).isLt
      exact_mod_cast (show (Fintype.equivFin (CovariateTable n) q).val ≤
        Fintype.card (CovariateTable n)+1 by omega)⟩
  inj' := by
    intro a b hab
    apply (Fintype.equivFin (CovariateTable n)).injective
    apply Fin.ext
    have hval := congrArg (fun z : Setup.UniversalCovariate => (z:ℝ)) hab
    have hd : (Fintype.card (CovariateTable n):ℝ)+1 ≠ 0 := by positivity
    have hcast := (div_left_inj' hd).mp hval
    exact_mod_cast hcast

end
end MEJF.HeterogeneousLearner
