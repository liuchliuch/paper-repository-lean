import Paper12.Circuit
import Paper12.Qubit

/-!
# Necessity (Lemma 2.2)

Every unitary implemented by a clean `Γ`-symmetric circuit is `Γ`-equivariant.
Relabelling preserves each layer, commuting gates yield circuit commutation
with `R(γ̃)`, and the lift preserves active and workspace wires separately,
so the clean implementation identity forces `U R_X(γ) = R_X(γ) U`.
-/

noncomputable section

namespace Paper12

open Matrix Complex
open scoped Function
open Classical

variable {X W : Type*} [Fintype X] [Fintype W]

theorem permBasis_symm {J : Type*} (γ : J ≃ J) (b : Basis J) :
    permBasis γ (permBasis γ.symm b) = b := by
  funext x; simp [permBasis]

theorem permBasis_symm_eq {J : Type*} (e : J ≃ J) (i : Basis J) :
    permBasis e.symm i = fun x => i (e x) := by
  show (fun x => i ((e.symm).symm x)) = _
  rw [Equiv.symm_symm]

def conjRHom {J : Type*} [Fintype J] (e : J ≃ J) : Op J →* Op J where
  toFun := conjR e
  map_one' := conjR_one e
  map_mul' := conjR_mul e

/-! ## Conjugation by `R` reindexes matrix entries -/

theorem R_mul_left {J : Type*} [Fintype J] (γ : J ≃ J) (M : Op J) (i j : Basis J) :
    (R γ * M) i j = M (permBasis γ.symm i) j := by
  simp only [Matrix.mul_apply, R_apply]
  have hsum : ∑ k : Basis J, (if permBasis γ k = i then (1 : ℂ) else 0) * M k j
      = M (permBasis γ.symm i) j := by
    rw [Finset.sum_eq_single (a := permBasis γ.symm i)]
    · rw [if_pos (permBasis_symm γ i), one_mul]
    · intro b _ hb
      by_cases hi : permBasis γ b = i
      · exfalso
        apply hb
        have : permBasis γ b = permBasis γ (permBasis γ.symm i) := by
          rw [hi, permBasis_symm]
        exact permBasis_injective γ this
      · rw [if_neg hi, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  exact hsum

theorem R_mul_right {J : Type*} [Fintype J] (M : Op J) (γ : J ≃ J) (i j : Basis J) :
    (M * (R γ)ᴴ) i j = M i (permBasis γ.symm j) := by
  simp only [Matrix.mul_apply, R_adj_apply]
  have hsum : ∑ k : Basis J, M i k * (if permBasis γ k = j then (1 : ℂ) else 0)
      = M i (permBasis γ.symm j) := by
    rw [Finset.sum_eq_single (a := permBasis γ.symm j)]
    · rw [if_pos (permBasis_symm γ j), mul_one]
    · intro b _ hb
      by_cases hj : permBasis γ b = j
      · exfalso
        apply hb
        have : permBasis γ b = permBasis γ (permBasis γ.symm j) := by
          rw [hj, permBasis_symm]
        exact permBasis_injective γ this
      · rw [if_neg hj, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  exact hsum

/-- Key entrywise formula for conjugation. -/
theorem conjR_apply_nec {J : Type*} [Fintype J] (e : J ≃ J) (U : Op J) (i j : Basis J) :
    conjR e U i j = U (fun x => i (e x)) (fun x => j (e x)) := by
  unfold conjR
  rw [Matrix.mul_assoc]
  set M : Op J := fun a b => U a (permBasis e.symm b) with hM
  have hright : ∀ a b, (U * (R e)ᴴ) a b = M a b := by
    intro a b
    rw [R_mul_right]
  have hext : U * (R e)ᴴ = M := by
    funext a b; exact hright a b
  rw [hext]
  have hleft : (R e * M) i j = M (permBasis e.symm i) j := R_mul_left e M i j
  rw [hleft, hM]
  show U (fun x => i (e x)) (permBasis e.symm j) = _
  rw [permBasis_symm_eq]

theorem OneQubit.map_unitary_of {J : Type*} [Fintype J] (e : J ≃ J) (g : OneQubit J) :
    OneQubit.unitary (g.map e) = conjR e (OneQubit.unitary g) :=
  OneQubit.map_unitary e g

theorem Threshold.map_unitary_of {J : Type*} [Fintype J] (e : J ≃ J) (g : Threshold J) :
    Threshold.unitary (g.map e) = conjR e (Threshold.unitary g) :=
  Threshold.map_unitary e g

theorem Gate.map_unitary_of {J : Type*} [Fintype J] (e : J ≃ J) (g : Gate J) :
    Gate.unitary (Gate.map e g) = conjR e (Gate.unitary g) :=
  Gate.map_unitary e g

theorem Layer.commute_of_preserved {J : Type*} [Fintype J] (e : J ≃ J) (L : Layer J)
    (h : Layer.map e L = L) :
    Layer.unitary (Layer.map e L) = Layer.unitary L := by
  rw [h]

theorem Layer.unitary_map {J : Type*} [Fintype J] (e : J ≃ J) (L : Layer J) :
    Layer.unitary (Layer.map e L) = conjR e (Layer.unitary L) := by
  have hp : ((L.gates : Set (Gate J)).Pairwise (Commute on Gate.unitary)) :=
    pairwiseCommute_to_set L.gates L.commute
  have hp2 : (((Layer.map e L).gates : Set (Gate J)).Pairwise (Commute on Gate.unitary)) :=
    pairwiseCommute_to_set (Layer.map e L).gates (Layer.map e L).commute
  have hL : Layer.unitary L = L.gates.noncommProd Gate.unitary hp := by
    unfold Layer.unitary
    rw [dif_pos hp]
  have hL2 : Layer.unitary (Layer.map e L)
      = (Layer.map e L).gates.noncommProd Gate.unitary hp2 := by
    unfold Layer.unitary
    rw [dif_pos hp2]
  rw [hL, hL2]
  show (Layer.map e L).gates.noncommProd Gate.unitary hp2
      = conjR e (L.gates.noncommProd Gate.unitary hp)
  have hcomp : ∀ g : Gate J, Gate.unitary (Gate.map e g) = conjR e (Gate.unitary g) :=
    fun g => Gate.map_unitary e g
  have hpmap : ((L.gates : Set (Gate J)).Pairwise
      (Commute on fun g => Gate.unitary (Gate.map e g))) := by
    intro a ha b hb _
    change Gate.unitary (Gate.map e a) * Gate.unitary (Gate.map e b) =
      Gate.unitary (Gate.map e b) * Gate.unitary (Gate.map e a)
    rw [Gate.map_unitary, Gate.map_unitary, ← conjR_mul, ← conjR_mul,
      L.commute a ha b hb]
  have step1 : (Layer.map e L).gates.noncommProd Gate.unitary hp2
      = L.gates.noncommProd (fun g => Gate.unitary (Gate.map e g)) hpmap := by
    simp only [Finset.noncommProd, Layer.map, relabelGates,
      Finset.map_val, Multiset.map_map]
    rfl
  rw [step1]
  have step2 := Finset.noncommProd_congr (s₁ := L.gates) (s₂ := L.gates)
    rfl (fun g _ => hcomp g) hpmap
  rw [step2]
  exact (Finset.map_noncommProd L.gates Gate.unitary hp (conjRHom e)).symm

/-- A layer preserved by `e` has unitary commuting with `R e`. -/
theorem Layer.unitary_commute {J : Type*} [Fintype J] (e : J ≃ J) (L : Layer J)
    (h : Layer.map e L = L) :
    Layer.unitary L * R e = R e * Layer.unitary L := by
  have hmap := Layer.unitary_map e L
  rw [h] at hmap
  have h2 : (R e * Layer.unitary L * (R e)ᴴ) * R e = R e * Layer.unitary L := by
    calc (R e * Layer.unitary L * (R e)ᴴ) * R e
        = R e * Layer.unitary L * ((R e)ᴴ * R e) := by ac_rfl
      _ = R e * Layer.unitary L * (1 : Op J) := by rw [R_unitary]
      _ = R e * Layer.unitary L := by rw [Matrix.mul_one]
  conv_lhs =>
    rw [hmap]
  unfold conjR
  exact h2

theorem commute_of_layers {J : Type*} [Fintype J] (ls : List (Op J)) (e : J ≃ J)
    (h : ∀ U ∈ ls, U * R e = R e * U) :
    (ls.foldr (· * ·) 1) * R e = R e * (ls.foldr (· * ·) 1) := by
  induction ls with
  | nil =>
    rw [List.foldr_nil, one_mul, mul_one]
  | cons U rest ih =>
    rw [List.foldr_cons]
    have hU : U * R e = R e * U := h U (by simp)
    have hr : ∀ V ∈ rest, V * R e = R e * V := fun V hv => h V (List.mem_cons_of_mem U hv)
    specialize ih hr
    calc (U * List.foldr (· * ·) 1 rest) * R e
        = U * (List.foldr (· * ·) 1 rest * R e) := by rw [Matrix.mul_assoc]
      _ = U * (R e * List.foldr (· * ·) 1 rest) := by rw [ih]
      _ = (U * R e) * List.foldr (· * ·) 1 rest := by rw [Matrix.mul_assoc]
      _ = (R e * U) * List.foldr (· * ·) 1 rest := by rw [hU]
      _ = R e * (U * List.foldr (· * ·) 1 rest) := by rw [Matrix.mul_assoc]

/-- A circuit whose layers are preserved by `e` has unitary commuting with `R e`. -/
theorem Circuit.commute_of_symmetric {J : Type*} [Fintype J] (C : Circuit J) (e : J ≃ J)
    (h : ∀ L ∈ C.layers, Layer.map e L = L) :
    C.unitary * R e = R e * C.unitary := by
  unfold Circuit.unitary
  apply commute_of_layers
  intro U hU
  simp only [List.mem_map] at hU
  obtain ⟨L, hL, rfl⟩ := hU
  exact Layer.unitary_commute e L (h L hL)

/-! ## Embedding and the action of `R` on workspace-zero states -/

theorem applyOp_R {X : Type*} [Fintype X] (γ : X ≃ X) (ψ : Vec X) (b : Basis X) :
    applyOp (R γ) ψ b = ψ (fun x => b (γ x)) := by
  simp only [applyOp, R_apply]
  rw [Finset.sum_eq_single (a := permBasis γ.symm b)]
  · rw [if_pos (permBasis_symm γ b), one_mul]
    exact congrArg ψ (permBasis_symm_eq γ b)
  · intro a _ ha
    by_cases hi : permBasis γ a = b
    · exfalso
      apply ha
      have : permBasis γ a = permBasis γ (permBasis γ.symm b) := by
        rw [hi, permBasis_symm]
      exact permBasis_injective γ this
    · rw [if_neg hi, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem applyOp_mul {X : Type*} [Fintype X] (A B : Op X) (ψ : Vec X) :
    applyOp (A * B) ψ = applyOp A (applyOp B ψ) := by
  funext b
  simp only [applyOp, Matrix.mul_apply]
  have rearrange :
      ∑ c : Basis X, (∑ k : Basis X, A b k * B k c) * ψ c =
        ∑ k : Basis X, A b k * (∑ c : Basis X, B k c * ψ c) := by
    calc ∑ c : Basis X, (∑ k : Basis X, A b k * B k c) * ψ c
        = ∑ c : Basis X, ∑ k : Basis X, A b k * B k c * ψ c := by
          apply Finset.sum_congr rfl
          intro c _
          exact Finset.sum_mul _ _ _
      _ = ∑ k : Basis X, ∑ c : Basis X, A b k * B k c * ψ c := Finset.sum_comm
      _ = ∑ k : Basis X, A b k * (∑ c : Basis X, B k c * ψ c) := by
          apply Finset.sum_congr rfl
          intro k _
          have h1 : ∑ c : Basis X, A b k * B k c * ψ c
              = A b k * ∑ c : Basis X, B k c * ψ c := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro c _
            ring
          exact h1
  exact rearrange

/-- Standard basis vector. -/
def eBasis {X : Type*} [Fintype X] (j : Basis X) : Vec X :=
  fun k => if k = j then 1 else 0

theorem applyOp_eBasis {X : Type*} [Fintype X] (M : Op X) (j i : Basis X) :
    applyOp M (eBasis j) i = M i j := by
  simp only [applyOp, eBasis]
  rw [Finset.sum_eq_single j]
  · rw [if_pos rfl, mul_one]
  · intro b _ hb
    rw [if_neg hb, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem embedZero_injective {X W : Type*} :
    Function.Injective (embedZero (X := X) (W := W)) := by
  intro ψ χ h
  funext β
  let b : Basis (X ⊕ W) := fun z =>
    Sum.casesOn z (fun x => β x) (fun _ => 0)
  have hz : ∀ r : W, b (Sum.inr r) = 0 := fun _ => rfl
  have hβ : (fun x => b (Sum.inl x)) = β := funext fun _ => rfl
  have := congrFun h b
  simp only [embedZero] at this
  rw [if_pos hz, if_pos hz] at this
  rw [hβ] at this
  exact this

theorem embedZero_R {X : Type*} [Fintype X] {W : Type*} {γ : X ≃ X} (ψ : Vec X) :
    embedZero (X := X) (W := W) (applyOp (R γ) ψ) =
      fun b => if ∀ r : W, b (Sum.inr r) = 0 then
        ψ (fun x => b (Sum.inl (γ x))) else 0 := by
  funext b
  simp only [embedZero]
  by_cases h : ∀ r : W, b (Sum.inr r) = 0
  · rw [if_pos h, if_pos h, applyOp_R]
  · rw [if_neg h, if_neg h]

/-- `e` restricts to `γ` on active wires ⟹ it maps workspace wires to workspace wires. -/
theorem lift_inr_map {X W : Type*} {γ : X ≃ X} (e : (X ⊕ W) ≃ (X ⊕ W))
    (hrestr : ∀ x : X, e (Sum.inl x) = Sum.inl (γ x)) (r : W) :
    ∃ r' : W, e (Sum.inr r) = Sum.inr r' := by
  generalize hz : e (Sum.inr r) = z
  cases z with
  | inl x =>
    have h1 : e (Sum.inl (γ.symm x)) = Sum.inl x := by simp [hrestr]
    have h2 : e (Sum.inl (γ.symm x)) = e (Sum.inr r) := by rw [h1, ← hz]
    have h3 : Sum.inl (γ.symm x) = Sum.inr r := e.injective h2
    cases h3
  | inr r' =>
    exact ⟨r', rfl⟩

theorem lift_inr_surj {X W : Type*} {γ : X ≃ X} (e : (X ⊕ W) ≃ (X ⊕ W))
    (hrestr : ∀ x : X, e (Sum.inl x) = Sum.inl (γ x)) (r : W) :
    ∃ r' : W, e (Sum.inr r') = Sum.inr r := by
  obtain ⟨z, hz⟩ := e.surjective (Sum.inr r)
  cases z with
  | inl x =>
    rw [hrestr] at hz
    cases hz
  | inr r' => exact ⟨r', hz⟩

/-- The lift acts as `R γ` on the active part and preserves the workspace-zero slice. -/
theorem R_lift_embedZero {X W : Type*} [Fintype X] [Fintype W] {γ : X ≃ X}
    (e : (X ⊕ W) ≃ (X ⊕ W))
    (hrestr : ∀ x : X, e (Sum.inl x) = Sum.inl (γ x))
    (ψ : Vec X) :
    applyOp (R e) (embedZero (X := X) (W := W) ψ) =
      embedZero (applyOp (R γ) ψ) := by
  funext c
  rw [applyOp_R]
  simp only [embedZero]
  have hw : (∀ r : W, c (e (Sum.inr r)) = 0) ↔ (∀ r : W, c (Sum.inr r) = 0) := by
    constructor
    · intro h r
      obtain ⟨r', he⟩ := lift_inr_surj e hrestr r
      rw [← he]
      exact h r'
    · intro h r
      obtain ⟨r', he⟩ := lift_inr_map e hrestr r
      rw [he]
      exact h r'
  by_cases h : ∀ r : W, c (Sum.inr r) = 0
  · have h2 : ∀ r : W, c (e (Sum.inr r)) = 0 := hw.mpr h
    have hact : (fun x => c (e (Sum.inl x))) = (fun x => c (Sum.inl (γ x))) := by
      funext x; rw [hrestr]
    rw [if_pos h2, if_pos h, hact, applyOp_R]
  · have h2 : ¬ ∀ r : W, c (e (Sum.inr r)) = 0 := fun hh => h (hw.mp hh)
    rw [if_neg h2, if_neg h]

/-! ## Lemma 2.2 -/

/-- Lemma 2.2: clean `Γ`-symmetric implementation forces equivariance. -/
theorem lemma_2_2 {Γ : Subgroup (X ≃ X)} {U : Op X} {C : Circuit (X ⊕ W)}
    (hsym : Symmetric Γ C) (hclean : CleanImplements C U) :
    Equivariant Γ U := by
  intro γ hγ
  let g : Γ := ⟨γ, hγ⟩
  let e := hsym.lift g
  have hrestr : ∀ x : X, e (Sum.inl x) = Sum.inl (γ x) := hsym.restrict g
  have hcomm : C.unitary * R e = R e * C.unitary := by
    apply Circuit.commute_of_symmetric
    intro L hL
    exact hsym.preserves g L hL
  have happly : ∀ φ : Vec (X ⊕ W),
      applyOp C.unitary (applyOp (R e) φ) = applyOp (R e) (applyOp C.unitary φ) := by
    intro φ
    rw [← applyOp_mul, ← applyOp_mul, hcomm]
  have key : ∀ ψ : Vec X,
      applyOp U (applyOp (R γ) ψ) = applyOp (R γ) (applyOp U ψ) := by
    intro ψ
    have h1 : embedZero (X := X) (W := W) (applyOp U (applyOp (R γ) ψ))
        = applyOp C.unitary (embedZero (applyOp (R γ) ψ)) := (hclean _).symm
    have h2 : embedZero (X := X) (W := W) (applyOp (R γ) ψ)
        = applyOp (R e) (embedZero ψ) := (R_lift_embedZero e hrestr ψ).symm
    have h3 : applyOp C.unitary (embedZero (applyOp (R γ) ψ))
        = applyOp C.unitary (applyOp (R e) (embedZero ψ)) := by rw [h2]
    have h4 : applyOp C.unitary (applyOp (R e) (embedZero ψ))
        = applyOp (R e) (applyOp C.unitary (embedZero ψ)) := happly _
    have h5 : applyOp C.unitary (embedZero ψ) = embedZero (applyOp U ψ) := hclean _
    have h6 : applyOp (R e) (applyOp C.unitary (embedZero ψ))
        = applyOp (R e) (embedZero (X := X) (W := W) (applyOp U ψ)) := by rw [h5]
    have h7 : applyOp (R e) (embedZero (X := X) (W := W) (applyOp U ψ))
        = embedZero (applyOp (R γ) (applyOp U ψ)) := R_lift_embedZero e hrestr _
    have hchain : embedZero (X := X) (W := W) (applyOp U (applyOp (R γ) ψ))
        = embedZero (applyOp (R γ) (applyOp U ψ)) := by
      calc embedZero (X := X) (W := W) (applyOp U (applyOp (R γ) ψ))
          = applyOp C.unitary (embedZero (applyOp (R γ) ψ)) := h1
        _ = applyOp C.unitary (applyOp (R e) (embedZero ψ)) := h3
        _ = applyOp (R e) (applyOp C.unitary (embedZero ψ)) := h4
        _ = applyOp (R e) (embedZero (X := X) (W := W) (applyOp U ψ)) := h6
        _ = embedZero (applyOp (R γ) (applyOp U ψ)) := h7
    exact embedZero_injective hchain
  have hmat : applyOp (U * R γ) = applyOp (R γ * U) := by
    funext ψ
    rw [applyOp_mul, applyOp_mul, key]
  ext i j
  have := congrFun (congrFun hmat (eBasis j)) i
  rw [applyOp_eBasis, applyOp_eBasis] at this
  exact this

end Paper12
