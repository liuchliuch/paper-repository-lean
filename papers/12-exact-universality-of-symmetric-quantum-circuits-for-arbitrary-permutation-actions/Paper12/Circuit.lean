import Paper12.Qubit
import Paper12.Ops

/-!
# Circuit model: elementary gates, layers, symmetry, clean implementation

An elementary gate is either an arbitrary one-qubit unitary on one wire or a
reversible unbounded-fan-in threshold gate.  A layer is a finite set of
pairwise commuting elementary gates.  A circuit is a sequence of layers.
Circuit symmetry requires, for every active-wire permutation in `Γ`, a lift
to all wires that preserves each layer as a set of labelled gates.  Clean
implementation returns the workspace to zero on every active input.
-/

noncomputable section

namespace Paper12

open Matrix Complex
open Classical
open scoped Function

/-- A one-qubit elementary gate on a single wire. -/
structure OneQubit (J : Type*) where
  wire : J
  u : Matrix (Fin 2) (Fin 2) ℂ
  isUnitary : uᴴ * u = 1

/-- A reversible threshold gate: flip `head` iff the Hamming weight of
`controls` is at least `threshold`.  The head is not a control. -/
structure Threshold (J : Type*) where
  head : J
  controls : Finset J
  threshold : ℕ
  head_not : head ∉ controls

/-- Elementary gates. -/
inductive Gate (J : Type*)
  | one (g : OneQubit J)
  | thr (g : Threshold J)

/-- Relabelling of a one-qubit gate. -/
def OneQubit.map {J J' : Type*} (e : J ≃ J') (g : OneQubit J) : OneQubit J' where
  wire := e g.wire
  u := g.u
  isUnitary := g.isUnitary

/-- Relabelling of a threshold gate. -/
def Threshold.map {J J' : Type*} (e : J ≃ J') (g : Threshold J) : Threshold J' where
  head := e g.head
  controls := g.controls.map e.toEmbedding
  threshold := g.threshold
  head_not := by
    intro hin
    rw [Finset.mem_map] at hin
    obtain ⟨a, ha, heq⟩ := hin
    have : a = g.head := e.injective heq
    subst this
    exact g.head_not ha

/-- Relabelling of an elementary gate. -/
def Gate.map {J J' : Type*} (e : J ≃ J') : Gate J → Gate J'
  | .one g => .one (g.map e)
  | .thr g => .thr (g.map e)

/-- Relabelling as an embedding of gate types. -/
def Gate.mapEmb {J J' : Type*} (e : J ≃ J') : Gate J ↪ Gate J' where
  toFun := Gate.map e
  inj' := by
    intro a b h
    cases a with
    | one g =>
      cases b with
      | one g' =>
        have h' : g.map e = g'.map e := by simpa [Gate.map] using h
        have hw : e g.wire = e g'.wire := congrArg OneQubit.wire h'
        have : g = g' := by
          have hwe : g.wire = g'.wire := e.injective hw
          cases g; cases g'; simp [OneQubit.map] at h' ⊢; subst hwe; exact h'
        exact congrArg Gate.one this
      | thr g' => simp [Gate.map] at h
    | thr g =>
      cases b with
      | one g' => simp [Gate.map] at h
      | thr g' =>
        have h' : g.map e = g'.map e := by simpa [Gate.map] using h
        have hh : e g.head = e g'.head := congrArg Threshold.head h'
        have : g = g' := by
          have he : g.head = g'.head := e.injective hh
          cases g; cases g'; simp [Threshold.map] at h' ⊢
          subst he
          exact h'
        exact congrArg Gate.thr this

/-- Classical action of a threshold gate on computational basis states. -/
def Threshold.act {J : Type*} (g : Threshold J) (b : Basis J) : Basis J :=
  if (∑ w ∈ g.controls, (b w : ℕ)) ≥ g.threshold then
    Function.update b g.head (1 - b g.head)
  else b

/-- Unitary of a threshold gate (a permutation matrix on the basis). -/
def Threshold.unitary {J : Type*} (g : Threshold J) : Op J :=
  Matrix.of fun i j => if g.act j = i then (1 : ℂ) else 0

/-- Unitary of a one-qubit gate tensored with identity on other wires. -/
def OneQubit.unitary {J : Type*} (g : OneQubit J) : Op J :=
  Matrix.of fun i j =>
    if (∀ w, w ≠ g.wire → i w = j w) then g.u (i g.wire) (j g.wire) else 0

/-- Semantics of an elementary gate as an operator on the full register. -/
def Gate.unitary {J : Type*} : Gate J → Op J
  | .one g => OneQubit.unitary g
  | .thr g => Threshold.unitary g

/-- Conjugation of an operator by the permutation representation of `e`. -/
def conjR {J : Type*} [Fintype J] (e : J ≃ J) (U : Op J) : Op J :=
  R e * U * (R e)ᴴ

theorem permBasis_symm' {J : Type*} (γ : J ≃ J) (b : Basis J) :
    permBasis γ (permBasis γ.symm b) = b := by
  funext x; simp [permBasis]

theorem permBasis_symm_eq' {J : Type*} (e : J ≃ J) (i : Basis J) :
    permBasis e.symm i = fun x => i (e x) := by
  show (fun x => i ((e.symm).symm x)) = _
  rw [Equiv.symm_symm]

theorem R_mul_left' {J : Type*} [Fintype J] (γ : J ≃ J) (M : Op J) (i j : Basis J) :
    (R γ * M) i j = M (permBasis γ.symm i) j := by
  haveI : DecidableEq (Basis J) := Classical.decEq _
  simp only [Matrix.mul_apply, R_apply]
  have hsum : ∑ k : Basis J, (if permBasis γ k = i then (1 : ℂ) else 0) * M k j
      = M (permBasis γ.symm i) j := by
    rw [Finset.sum_eq_single (a := permBasis γ.symm i)]
    · rw [if_pos (permBasis_symm' γ i), one_mul]
    · intro b _ hb
      by_cases hi : permBasis γ b = i
      · exfalso
        apply hb
        have : permBasis γ b = permBasis γ (permBasis γ.symm i) := by
          rw [hi, permBasis_symm']
        exact permBasis_injective γ this
      · rw [if_neg hi, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  simpa using hsum

theorem R_mul_right' {J : Type*} [Fintype J] (M : Op J) (γ : J ≃ J) (i j : Basis J) :
    (M * (R γ)ᴴ) i j = M i (permBasis γ.symm j) := by
  haveI : DecidableEq (Basis J) := Classical.decEq _
  simp only [Matrix.mul_apply, R_adj_apply]
  have hsum : ∑ k : Basis J, M i k * (if permBasis γ k = j then (1 : ℂ) else 0)
      = M i (permBasis γ.symm j) := by
    rw [Finset.sum_eq_single (a := permBasis γ.symm j)]
    · rw [if_pos (permBasis_symm' γ j), mul_one]
    · intro b _ hb
      by_cases hj : permBasis γ b = j
      · exfalso
        apply hb
        have : permBasis γ b = permBasis γ (permBasis γ.symm j) := by
          rw [hj, permBasis_symm']
        exact permBasis_injective γ this
      · rw [if_neg hj, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  simpa using hsum

/-- Entrywise action of conjugation by `R e`. -/
theorem conjR_apply {J : Type*} [Fintype J] (e : J ≃ J) (U : Op J) (i j : Basis J) :
    conjR e U i j = U (fun x => i (e x)) (fun x => j (e x)) := by
  unfold conjR
  rw [Matrix.mul_assoc]
  set M : Op J := fun a b => U a (permBasis e.symm b) with hM
  have hext : U * (R e)ᴴ = M := by
    funext a b
    rw [R_mul_right']
  rw [hext]
  have hleft : (R e * M) i j = M (permBasis e.symm i) j := R_mul_left' e M i j
  rw [hleft, hM]
  show U (fun x => i (e x)) (permBasis e.symm j) = _
  rw [permBasis_symm_eq']

/-- One-qubit unitary is functorial under wire relabelling. -/
theorem OneQubit.map_unitary {J : Type*} [Fintype J] (e : J ≃ J) (g : OneQubit J) :
    OneQubit.unitary (g.map e) = conjR e (OneQubit.unitary g) := by
  ext i j
  rw [conjR_apply]
  simp only [OneQubit.unitary, OneQubit.map, Matrix.of_apply]
  have hcond : (∀ w, w ≠ e g.wire → i w = j w) ↔ (∀ w, w ≠ g.wire → i (e w) = j (e w)) := by
    constructor
    · intro h w hw
      exact h (e w) (fun he => hw (e.injective he))
    · intro h w' hw'
      obtain ⟨w, rfl⟩ := e.surjective w'
      exact h w (fun he => hw' (by rw [he]))
  by_cases h : ∀ w, w ≠ e g.wire → i w = j w
  · rw [if_pos h, if_pos (hcond.mp h)]
  · rw [if_neg h, if_neg]
    exact fun he => h (hcond.mpr he)

/-- Threshold unitary is functorial under wire relabelling. -/
theorem Threshold.map_unitary {J : Type*} [Fintype J] (e : J ≃ J) (g : Threshold J) :
    Threshold.unitary (g.map e) = conjR e (Threshold.unitary g) := by
  ext i j
  rw [conjR_apply]
  simp only [Threshold.unitary, Matrix.of_apply, Threshold.act, Threshold.map]
  have hsum : (∑ w ∈ Finset.map e.toEmbedding g.controls, (j w : ℕ))
      = ∑ x ∈ g.controls, (j (e x) : ℕ) := by
    rw [Finset.sum_map]
    rfl
  rw [hsum]
  have hupd_gen : ∀ (v : Fin 2) (y : J),
      Function.update j (e g.head) v y
        = Function.update (fun x => j (e x)) g.head v (e.symm y) := by
    intro v y
    by_cases hy : e.symm y = g.head
    · have hy2 : y = e g.head := by
        have := congrArg e hy
        simpa using this
      subst hy2
      simp [Function.update, hy]
    · have hy2 : y ≠ e g.head := by
        intro h
        apply hy
        have := congrArg e.symm h
        simpa using this
      simp [Function.update, hy, hy2]
  have hupd_iff : ∀ (v : Fin 2),
      (Function.update j (e g.head) v = i) ↔
        (Function.update (fun x => j (e x)) g.head v = (fun x => i (e x))) := by
    intro v
    constructor
    · intro h
      funext x
      have := congrFun h (e x)
      rw [hupd_gen] at this
      rw [Equiv.symm_apply_apply] at this
      exact this
    · intro h
      funext y
      have := congrFun h (e.symm y)
      rw [← hupd_gen] at this
      rw [Equiv.apply_symm_apply] at this
      exact this
  by_cases hc : g.threshold ≤ ∑ x ∈ g.controls, (j (e x) : ℕ)
  · rw [if_pos hc, if_pos hc]
    by_cases hi : Function.update j (e g.head) (1 - j (e g.head)) = i
    · rw [if_pos hi, if_pos ((hupd_iff _).mp hi)]
    · rw [if_neg hi, if_neg]
      exact fun he => hi ((hupd_iff _).mpr he)
  · rw [if_neg hc, if_neg hc]
    have heq : (j = i) ↔ ((fun x => j (e x)) = (fun x => i (e x))) := by
      constructor
      · intro h; rw [h]
      · intro h
        funext y
        obtain ⟨x, rfl⟩ := e.surjective y
        exact congrFun h x
    by_cases hj : j = i
    · rw [if_pos hj, if_pos (heq.mp hj)]
    · rw [if_neg hj, if_neg]
      exact fun he => hj (heq.mpr he)


theorem Gate.map_unitary {J : Type*} [Fintype J] (e : J ≃ J) (g : Gate J) :
    Gate.unitary (Gate.map e g) = conjR e (Gate.unitary g) := by
  cases g with
  | one g => exact OneQubit.map_unitary e g
  | thr g => exact Threshold.map_unitary e g

/-- Pairwise commutation of gate unitaries. -/
def PairwiseCommute {J : Type*} [Fintype J] (s : Finset (Gate J)) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, Gate.unitary a * Gate.unitary b = Gate.unitary b * Gate.unitary a

theorem pairwiseCommute_to_set {J : Type*} [Fintype J] (s : Finset (Gate J))
    (h : PairwiseCommute s) :
    (s : Set (Gate J)).Pairwise (Commute on Gate.unitary) := by
  intro a ha b hb _
  exact h a ha b hb

/-- A layer is a finite set of pairwise commuting elementary gates. -/
structure Layer (J : Type*) [Fintype J] where
  gates : Finset (Gate J)
  commute : PairwiseCommute gates

/-- A circuit is a sequence of layers.  Layers are written in operator-product order: the rightmost acts first. -/
structure Circuit (J : Type*) [Fintype J] where
  layers : List (Layer J)

/-- Unitary of a layer: the product of its commuting gates.
Defined via a classical commutativity test so that it does not depend on the
particular `commute` proof carried by the layer. -/
def Layer.unitary {J : Type*} [Fintype J] (L : Layer J) : Op J :=
  if h : ((L.gates : Set (Gate J)).Pairwise (Commute on Gate.unitary)) then
    L.gates.noncommProd Gate.unitary h
  else 1

/-- Unitary of a circuit: the rightmost layer acts first. -/
def Circuit.unitary {J : Type*} [Fintype J] (C : Circuit J) : Op J :=
  (C.layers.map Layer.unitary).foldr (· * ·) 1

/-- Number of elementary gates in a circuit. -/
def Circuit.size {J : Type*} [Fintype J] (C : Circuit J) : ℕ :=
  (C.layers.map (fun L => L.gates.card)).sum

/-- Relabelling of a gate set. -/
def relabelGates {J : Type*} [Fintype J] (e : J ≃ J) (s : Finset (Gate J)) :
    Finset (Gate J) :=
  s.map (Gate.mapEmb e)

/-- Conjugation by `R e` transports products. -/
theorem conjR_mul {J : Type*} [Fintype J] (e : J ≃ J) (U V : Op J) :
    conjR e (U * V) = conjR e U * conjR e V := by
  unfold conjR
  have hunit : (R e)ᴴ * R e = (1 : Op J) := R_unitary e
  -- R e * (U * V) * (R e)ᴴ = (R e * U * (R e)ᴴ) * (R e * V * (R e)ᴴ)
  have h1 : R e * (U * V) * (R e)ᴴ = R e * U * V * (R e)ᴴ := by ac_rfl
  have h2 : R e * U * V * (R e)ᴴ = (R e * U * (R e)ᴴ) * (R e * V * (R e)ᴴ) := by
    calc R e * U * V * (R e)ᴴ
        = R e * U * ((R e)ᴴ * R e) * V * (R e)ᴴ := by rw [hunit, Matrix.mul_one]
      _ = (R e * U * (R e)ᴴ) * (R e * V * (R e)ᴴ) := by ac_rfl
  rw [h1, h2]

theorem conjR_one {J : Type*} [Fintype J] (e : J ≃ J) : conjR e 1 = (1 : Op J) := by
  unfold conjR
  rw [Matrix.mul_one, R_mul_adj e]

/-- Relabelling preserves commutation, by functoriality of gate unitaries. -/
theorem relabel_commute {J : Type*} [Fintype J] (e : J ≃ J) (s : Finset (Gate J))
    (h : PairwiseCommute s) : PairwiseCommute (relabelGates e s) := by
  intro a ha b hb
  simp only [relabelGates, Finset.mem_map] at ha hb
  obtain ⟨a₀, ha₀, rfl⟩ := ha
  obtain ⟨b₀, hb₀, rfl⟩ := hb
  show Gate.unitary (Gate.map e a₀) * Gate.unitary (Gate.map e b₀) =
    Gate.unitary (Gate.map e b₀) * Gate.unitary (Gate.map e a₀)
  rw [Gate.map_unitary, Gate.map_unitary, ← conjR_mul, ← conjR_mul, h a₀ ha₀ b₀ hb₀]

/-- Relabelling of a layer. -/
def Layer.map {J : Type*} [Fintype J] (e : J ≃ J) (L : Layer J) : Layer J where
  gates := relabelGates e L.gates
  commute := relabel_commute e L.gates L.commute

/-- Lift of an active permutation to all wires by fixing workspace. -/
def liftFixW {X W : Type*} (γ : X ≃ X) : (X ⊕ W) ≃ (X ⊕ W) :=
  γ.sumCongr (Equiv.refl W)

/-- A circuit is `Γ`-symmetric when every `γ ∈ Γ` admits a lift `γ̃` that
preserves each layer as a set of labelled gates. -/
structure Symmetric {X W : Type*} [Fintype X] [Fintype W]
    (Γ : Subgroup (X ≃ X)) (C : Circuit (X ⊕ W)) where
  lift : ∀ γ : Γ, (X ⊕ W) ≃ (X ⊕ W)
  restrict : ∀ (γ : Γ) (x : X), lift γ (Sum.inl x) = Sum.inl (γ.val x)
  preserves : ∀ (γ : Γ) (L : Layer (X ⊕ W)), L ∈ C.layers →
    Layer.map (lift γ) L = L

/-- Embed an active vector into the joint register with workspace zero. -/
def embedZero {X W : Type*} (ψ : Vec X) : Vec (X ⊕ W) :=
  fun b => if ∀ r : W, b (Sum.inr r) = 0 then ψ (fun x => b (Sum.inl x)) else 0

/-- Apply an operator to a vector. -/
def applyOp {X : Type*} [Fintype X] (U : Op X) (ψ : Vec X) : Vec X :=
  fun b => ∑ b' : Basis X, U b b' * ψ b'

/-- Clean implementation of `U`: workspace returns to zero on every input. -/
def CleanImplements {X W : Type*} [Fintype X] [Fintype W]
    (C : Circuit (X ⊕ W)) (U : Op X) : Prop :=
  ∀ ψ : Vec X, applyOp C.unitary (embedZero ψ) = embedZero (applyOp U ψ)

/-- `U` has a `Γ`-symmetric clean circuit with at most `nW` workspace qubits
and at most `s` gates. -/
def HasCleanSymmetricCircuit {X : Type*} [Fintype X]
    (Γ : Subgroup (X ≃ X)) (U : Op X) (nW s : ℕ) : Prop :=
  ∃ (W : Type) (hW : Fintype W) (C : Circuit (X ⊕ W)),
    @CleanImplements X W _ hW C U ∧
    Fintype.card W ≤ nW ∧
    C.size ≤ s ∧
    Nonempty (@Symmetric X W _ hW Γ C)

/-- Commutation with the permutation representation. -/
def Equivariant {X : Type*} [Fintype X] (Γ : Subgroup (X ≃ X)) (U : Op X) : Prop :=
  ∀ γ ∈ Γ, U * R γ = R γ * U

end Paper12
