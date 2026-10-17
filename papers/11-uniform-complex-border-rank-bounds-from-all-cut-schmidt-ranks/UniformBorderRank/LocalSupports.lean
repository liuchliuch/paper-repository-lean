import UniformBorderRank.LocalMaps
import UniformBorderRank.Faithful
import UniformBorderRank.SupportRank
import UniformBorderRank.FlatteningFacts
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Local support spaces, their cut-rank bounds, and coordinate retractions. -/
noncomputable section
namespace UniformBorderRank
open Finset Module

def localSupport {N : ℕ} {d : Fin N → ℕ} (T : Coeffs d) (i : Fin N) :
    Submodule ℂ (Fin (d i) → ℂ) :=
  Submodule.span ℂ (Set.range (fun u : ∀ j, Fin (d j) => fun a => T (Function.update u i a)))

/-- A singleton cut bounds the dimension of the actual local support. -/
theorem finrank_localSupport_le {N : ℕ} {d : Fin N → ℕ}
    (T : Coeffs d) (hT : T ≠ 0) (i : Fin N) :
    Module.finrank ℂ (localSupport T i) ≤ schmidtRank d T ({i}ᶜ : Finset (Fin N)) := by
  classical
  obtain ⟨u₀, _hu⟩ : ∃ u, T u ≠ 0 := by
    by_contra! h
    exact hT (funext h)
  let S : Finset (Fin N) := {i}ᶜ
  let F : ((∀ j ∈ Sᶜ, Fin (d j)) → ℂ) →ₗ[ℂ] (Fin (d i) → ℂ) :=
    { toFun := fun f a => f (fun j _ => Function.update u₀ i a j)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let W := Submodule.span ℂ (Set.range (fun row : ∀ j ∈ S, Fin (d j) =>
    fun col : ∀ j ∈ Sᶜ, Fin (d j) => flatCoeff d T S row col))
  have hsub : localSupport T i ≤ W.map F := by
    apply Submodule.span_le.mpr
    rintro _ ⟨u, rfl⟩
    refine ⟨(fun col => flatCoeff d T S (fun j _ => u j) col),
      Submodule.subset_span ⟨(fun j _ => u j), rfl⟩, ?_⟩
    ext a
    change T (fun j => if h : j ∈ S then u j else Function.update u₀ i a j) =
      T (Function.update u i a)
    apply congrArg T
    funext j
    by_cases hj : j = i
    · subst j; simp [S]
    · simp [S, hj]
  exact (Submodule.finrank_mono hsub).trans (Submodule.finrank_map_le F W)

lemma finrank_localSupport_le_of_allCutLe {N : ℕ} {d : Fin N → ℕ}
    (hN : 2 ≤ N) (T : Coeffs d) (hT : T ≠ 0) (r : ℕ) (h : allCutLe d T r) (i : Fin N) :
    Module.finrank ℂ (localSupport T i) ≤ r := by
  apply (finrank_localSupport_le T hT i).trans
  apply h {i}ᶜ
  · intro he
    have he' : ({i} : Finset (Fin N)) = univ := compl_eq_bot.mp he
    have hc := congrArg Finset.card he'
    simp only [card_singleton, card_univ, Fintype.card_fin] at hc
    omega
  · intro he
    have he' : ({i} : Finset (Fin N)) = ∅ := compl_eq_top.mp he
    exact (singleton_ne_empty i) he'

def siteLinearMap {N : ℕ} {d : Fin N → ℕ} (i : Fin N)
    (P : (Fin (d i) → ℂ) →ₗ[ℂ] (Fin (d i) → ℂ)) : Coeffs d →ₗ[ℂ] Coeffs d where
  toFun T u := P (fun a => T (Function.update u i a)) (u i)
  map_add' T U := by ext u; exact congrFun (P.map_add _ _) (u i)
  map_smul' c T := by ext u; exact congrFun (P.map_smul c _) (u i)

/-- A local projection that fixes the local support fixes the original tensor. -/
lemma siteLinearMap_eq_of_support {N : ℕ} {d : Fin N → ℕ} (T : Coeffs d) (i : Fin N)
    (P : (Fin (d i) → ℂ) →ₗ[ℂ] (Fin (d i) → ℂ))
    (hP : ∀ x : localSupport T i, P x.val = x.val) : siteLinearMap i P T = T := by
  ext u
  have hx : (fun a => T (Function.update u i a)) ∈ localSupport T i :=
    Submodule.subset_span ⟨u, rfl⟩
  have h := congrFun (hP ⟨_, hx⟩) (u i)
  simpa only [siteLinearMap, LinearMap.coe_mk, AddHom.coe_mk, Function.update_eq_self] using h

/-- Coordinates and inclusion for the local support. Their composite fixes
all vectors in that support; the target dimension is its actual finrank. -/
theorem exists_local_support_coordinates {N : ℕ} {d : Fin N → ℕ} (T : Coeffs d) (i : Fin N) :
    ∃ (p : (Fin (d i) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℂ (localSupport T i)) → ℂ))
      (q : (Fin (Module.finrank ℂ (localSupport T i)) → ℂ) →ₗ[ℂ] (Fin (d i) → ℂ)),
      (∀ x : localSupport T i, q (p x.val) = x.val) ∧ Function.Injective q := by
  let E := localSupport T i
  let B := Module.finBasis ℂ E
  obtain ⟨s, hs⟩ := LinearMap.exists_leftInverse_of_injective E.subtype E.ker_subtype
  let p := B.equivFun.toLinearMap.comp s
  let q := E.subtype.comp B.equivFun.symm.toLinearMap
  refine ⟨p, q, ?_, ?_⟩
  · intro x
    have he : s x.val = x := LinearMap.congr_fun hs x
    simp [p, q, he]
  · exact E.subtype_injective.comp B.equivFun.symm.injective

def localMatrix {N : ℕ} {d e : Fin N → ℕ}
    (P : ∀ i, (Fin (d i) → ℂ) →ₗ[ℂ] (Fin (e i) → ℂ)) :
    ∀ i, Fin (e i) → Fin (d i) → ℂ := fun i a b => P i (Pi.single b 1) a

def partialLocalAction {N : ℕ} {d : Fin N → ℕ}
    (P : ∀ i, (Fin (d i) → ℂ) →ₗ[ℂ] (Fin (d i) → ℂ))
    (J : Finset (Fin N)) (T : Coeffs d) : Coeffs d := fun u =>
  fullContract T Jᶜ (fun i a => localMatrix P i (u i) a) u

lemma partialLocalAction_empty {N : ℕ} {d : Fin N → ℕ}
    (P : ∀ i, (Fin (d i) → ℂ) →ₗ[ℂ] (Fin (d i) → ℂ)) (T : Coeffs d) :
    partialLocalAction P ∅ T = T := by
  ext u
  change fullContract T (∅ : Finset (Fin N))ᶜ _ u = T u
  rw [compl_empty, fullContract_univ]

lemma partialLocalAction_insert {N : ℕ} {d : Fin N → ℕ}
    (P : ∀ i, (Fin (d i) → ℂ) →ₗ[ℂ] (Fin (d i) → ℂ))
    (J : Finset (Fin N)) (i : Fin N) (hi : i ∉ J) (T : Coeffs d) :
    partialLocalAction P (insert i J) T = siteLinearMap i (P i) (partialLocalAction P J T) := by
  classical
  ext u
  let K := (insert i J)ᶜ
  let b : Covectors d := fun j a => localMatrix P j (u j) a
  have hiK : i ∉ K := by simp [K]
  have hK : insert i K = Jᶜ := by
    ext j
    by_cases hj : j = i
    · subst j; simp [K, hi]
    · simp [K, hj]
  have hh := fullContract_update T K i hiK b (b i) u
  simp only [Function.update_eq_self, hK] at hh
  have hc (a : Fin (d i)) : partialLocalAction P J T (Function.update u i a) =
      fullContract T Jᶜ b (Function.update u i a) := by
    have hb : (fun j x => localMatrix P j (Function.update u i a j) x) =
        Function.update b i (fun x => localMatrix P i a x) := by
      funext j x
      by_cases hj : j = i
      · subst j; simp [b]
      · simp [b, hj]
    change fullContract T Jᶜ _ (Function.update u i a) = _
    rw [hb, fullContract_update_of_mem T Jᶜ i (mem_compl.mpr hi)]
  change fullContract T K b u = (P i) (fun a => partialLocalAction P J T (Function.update u i a)) (u i)
  rw [hh, linearMap_apply_eq_sum_single]
  apply sum_congr rfl
  intro a _
  rw [hc]
  dsimp [b, localMatrix]
  ring

/-- Simultaneous local maps fix `T` when each local map fixes its actual
support. No tensor-product support membership is assumed. -/
theorem tensorMap_eq_of_localSupport {N : ℕ} {d : Fin N → ℕ}
    (T : Coeffs d) (P : ∀ i, (Fin (d i) → ℂ) →ₗ[ℂ] (Fin (d i) → ℂ))
    (hP : ∀ i, ∀ x : localSupport T i, P i x.val = x.val) :
    tensorMap (localMatrix P) T = T := by
  classical
  have hJ : ∀ J : Finset (Fin N), partialLocalAction P J T = T := by
    intro J
    induction J using Finset.induction_on with
    | empty => exact partialLocalAction_empty P T
    | @insert i J hi ih =>
      rw [partialLocalAction_insert P J i hi, ih]
      exact siteLinearMap_eq_of_support T i (P i) (hP i)
  have he : partialLocalAction P univ T = tensorMap (localMatrix P) T := by
    ext u
    simp [partialLocalAction, fullContract, contractionWeight, tensorMap]
  rw [← he]
  exact hJ univ

lemma tensorMap_comp {N : ℕ} {d e f : Fin N → ℕ}
    (A : ∀ i, Fin (e i) → Fin (d i) → ℂ)
    (B : ∀ i, Fin (f i) → Fin (e i) → ℂ) (T : Coeffs d) :
    tensorMap B (tensorMap A T) = tensorMap (fun i a b => ∑ c, B i a c * A i c b) T := by
  classical
  ext u
  unfold tensorMap
  simp_rw [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  simp only [mul_assoc]
  rw [← mul_sum, Fintype.prod_sum]
  congr 1
  apply sum_congr rfl
  intro w _
  rw [Finset.prod_mul_distrib]
  ring

/-- Actual local support reduction: dimensions are at most the all-cut
bound; inclusion reconstructs `T`; all cut ranks and all border-rank bounds
are preserved. -/
theorem exists_local_support_reduction {N : ℕ} {d : Fin N → ℕ}
    (hN : 2 ≤ N) (T : Coeffs d) (hT : T ≠ 0) (r : ℕ) (hcut : allCutLe d T r) :
    ∃ (e : Fin N → ℕ) (U : Coeffs e)
      (A : ∀ i, Fin (e i) → Fin (d i) → ℂ)
      (B : ∀ i, Fin (d i) → Fin (e i) → ℂ),
      (∀ i, e i ≤ r) ∧ U ≠ 0 ∧ U = tensorMap A T ∧ T = tensorMap B U ∧
      (∀ S, schmidtRank e U S = schmidtRank d T S) ∧
      (∀ b, borderRankLe U b ↔ borderRankLe T b) := by
  classical
  choose p q hfix hq using exists_local_support_coordinates T
  let e : Fin N → ℕ := fun i => Module.finrank ℂ (localSupport T i)
  let A := localMatrix p
  let B := localMatrix q
  let P := fun i => (q i).comp (p i)
  have he : (fun i a b => ∑ c, B i a c * A i c b) = localMatrix P := by
    funext i a b
    have h := linearMap_apply_eq_sum_single (q i) (p i (Pi.single b 1)) a
    dsimp [A, B, P, localMatrix, LinearMap.comp_apply]
    rw [h]
    apply sum_congr rfl
    intro c _
    ring
  have hrec : tensorMap B (tensorMap A T) = T := by
    rw [tensorMap_comp, he]
    exact tensorMap_eq_of_localSupport T P hfix
  refine ⟨e, tensorMap A T, A, B, ?_, ?_, rfl, hrec.symm, ?_, ?_⟩
  · intro i
    exact finrank_localSupport_le_of_allCutLe hN T hT r hcut i
  · intro hz
    apply hT
    rw [← hrec, hz]
    exact (tensorLinearMap B).map_zero
  · intro S
    apply le_antisymm (schmidtRank_tensorMap_le A T S)
    have hh := schmidtRank_tensorMap_le B (tensorMap A T) S
    rwa [hrec] at hh
  · intro b
    exact ⟨fun h => hrec ▸ borderRankLe_tensorMap B h, fun h => borderRankLe_tensorMap A h⟩

end UniformBorderRank
