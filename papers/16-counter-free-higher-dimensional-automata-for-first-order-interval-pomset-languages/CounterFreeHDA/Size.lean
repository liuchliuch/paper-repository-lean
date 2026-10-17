import CounterFreeHDA.IdealDiagram
import CounterFreeHDA.Track
import Mathlib.Data.Finset.Sort

namespace CounterFreeHDA.Cubical
universe u v
variable {Lab : Type u} {k : ℕ}

namespace Face

noncomputable def activeSet {U V : Cube Lab k} (f : Face U V) : Finset (Fin V.dim) := by
  classical
  exact Finset.univ.filter (fun j => f.status j = Status.star)

theorem position_mem {U V : Cube Lab k} (f : Face U V) (i : Fin U.dim) :
    f.position i ∈ f.activeSet := by
  classical
  simp only [activeSet,Finset.mem_filter,Finset.mem_univ,true_and,status,position_spec]

theorem active_card {U V : Cube Lab k} (f : Face U V) : f.activeSet.card = U.dim := by
  classical
  let p : Fin U.dim → f.activeSet := fun i => ⟨f.position i,f.position_mem i⟩
  have hp : Function.Bijective p := by
    constructor
    · intro i j h
      exact f.position_injective (congrArg Subtype.val h)
    · intro j
      have hj : f.status j.val = Status.star := (Finset.mem_filter.mp j.property).2
      cases hs : f.sub j.val with
      | inl i => exact ⟨i,Subtype.ext (f.position_unique hs).symm⟩
      | inr b =>
        cases b <;> simp only [status,hs] at hj <;>
          have hh := congrArg Fin.val hj <;> norm_num at hh
  simpa only [Fintype.card_fin,Fintype.card_coe] using
    (Fintype.card_congr (Equiv.ofBijective p hp)).symm

theorem position_canonical {U V : Cube Lab k} (f : Face U V) :
    f.position = f.activeSet.orderEmbOfFin f.active_card :=
  Finset.orderEmbOfFin_unique f.active_card f.position_mem f.position_strictMono

private theorem constant_ne_star (b : Bool) :
    (match b with | false => Status.zero | true => Status.one) ≠ Status.star := by
  cases b <;> decide

/-- All faces of a fixed cube inject into its 3^dimension status assignments.
Both their type and ordered variable names are recovered from these statuses. -/
theorem total_status_injective (V : Cube Lab k) :
    Function.Injective (fun z : Σ U, Face U V => z.2.status) := by
  classical
  rintro ⟨U,f⟩ ⟨W,g⟩ hh
  have hactive : f.activeSet = g.activeSet := by
    ext j
    simp only [activeSet,Finset.mem_filter,Finset.mem_univ,true_and,congrFun hh j]
  have hdim : U.dim = W.dim := by rw [← f.active_card,← g.active_card,hactive]
  rcases U with ⟨n,lu⟩
  rcases W with ⟨m,lw⟩
  have hnm : n = m := Fin.ext hdim
  subst m
  have hpos : f.position = g.position := by
    rw [f.position_canonical,g.position_canonical]
    congr
  have hlab : lu = lw := by
    funext i
    have hf := f.labels (f.position_spec i)
    have hg := g.labels (g.position_spec i)
    rw [hpos] at hf
    exact hf.symm.trans hg
  subst lw
  have hfg : f = g := by
    apply Face.ext
    funext j
    have hj := congrFun hh j
    cases hf : f.sub j with
    | inl i =>
      have hjpos := f.position_unique hf
      have hg : g.sub j = Sum.inl i := by rw [hjpos,hpos]; exact g.position_spec i
      exact hg.symm
    | inr b =>
      cases hg : g.sub j with
      | inl i =>
        cases b <;> simp only [status,hf,hg] at hj <;>
          have hval := congrArg Fin.val hj <;> norm_num at hval
      | inr c =>
        have hbc : b = c := by
          cases b <;> cases c <;> try rfl
          all_goals simp only [status,hf,hg] at hj
          all_goals have hval := congrArg Fin.val hj
          all_goals norm_num at hval
        exact congrArg Sum.inr hbc
  cases hfg
  rfl

theorem total_faces_card_le [Fintype Lab] (V : Cube Lab k) :
    Fintype.card (Σ U, Face U V) ≤ 3 ^ V.dim := by
  have h := Fintype.card_le_of_injective _ (total_status_injective V)
  simpa only [Fintype.card_fun,Fintype.card_fin] using h

end Face

variable [Fintype Lab] (C : FinCat.{u,v} (Cube Lab k)) (ord : C.IsOrdered)
variable (image : ∀ {U V}, Step U V → C.Hom U V)

abbrev AllMor := Σ S : Cube Lab k, Σ U : Cube Lab k, C.Hom S U

noncomputable def diagramEncode {S U : Cube Lab k} (z : IdealDiagram C ord image S U) :
    (Σ V, Face V U) → Set (AllMor C) :=
  fun f => (fun a => ⟨S,f.1,a⟩) '' z.val f.2

theorem diagramEncode_injective (S U : Cube Lab k) :
    Function.Injective (diagramEncode C ord image (S := S) (U := U)) := by
  intro z z' h
  apply IdealDiagram.ext
  funext V f
  have hf := congrFun h ⟨V,f⟩
  have hinj : Function.Injective (fun a : C.Hom S V => (⟨S,V,a⟩ : AllMor C)) := by
    intro a b hab
    simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using hab
  exact Set.image_injective.mpr hinj hf

/-- The per-cell part of the actual construction-size estimate. -/
theorem diagram_card_bound (S U : Cube Lab k) :
    Fintype.card (IdealDiagram C ord image S U) ≤
      2 ^ (Fintype.card (AllMor C) * 3 ^ k) := by
  classical
  have hi := Fintype.card_le_of_injective _ (diagramEncode_injective C ord image S U)
  have hf := Face.total_faces_card_le U
  have hu : U.dim ≤ k := Nat.le_of_lt_succ U.1.isLt
  calc
    Fintype.card (IdealDiagram C ord image S U) ≤
        Fintype.card ((Σ V, Face V U) → Set (AllMor C)) := hi
    _ = 2 ^ (Fintype.card (AllMor C) * Fintype.card (Σ V, Face V U)) := by
      rw [Fintype.card_fun,Fintype.card_set,Nat.pow_mul]
    _ ≤ 2 ^ (Fintype.card (AllMor C) * 3 ^ k) := by
      gcongr
      · norm_num
      · exact le_trans hf (Nat.pow_le_pow_right (by decide) hu)

/-- **Remark 2.4**, the displayed bound for the actual ideal-diagram HDA. -/
theorem remark_2_4 (J : ∀ {S U}, Set (C.Hom S U)) :
    Fintype.card (Σ U, (idealHDA C ord image J).Cell U) ≤
      (Fintype.card (Cube Lab k)) ^ 2 * 2 ^ (Fintype.card (AllMor C) * 3 ^ k) := by
  change Fintype.card (Σ U : Cube Lab k, Σ S : Cube Lab k, IdealDiagram C ord image S U) ≤ _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_sigma]
  calc
    (∑ U : Cube Lab k, ∑ S : Cube Lab k, Fintype.card (IdealDiagram C ord image S U)) ≤
      ∑ _U : Cube Lab k, ∑ _S : Cube Lab k, 2 ^ (Fintype.card (AllMor C) * 3 ^ k) := by
        apply Finset.sum_le_sum
        intro U hU
        exact Finset.sum_le_sum (fun S hS => diagram_card_bound C ord image S U)
    _ = _ := by simp; ring

end CounterFreeHDA.Cubical
