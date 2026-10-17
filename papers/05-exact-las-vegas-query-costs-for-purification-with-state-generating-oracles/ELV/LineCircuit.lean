import ELV.LpHilbert
import ELV.QueryCircuit

/-! Fixed two-query line walk. All work operations use only a known closed
subspace K and coordinate permutations. They never use the unknown plane's t. -/
noncomputable section
namespace ELV.Line
open ELV.Stabilize ELV.Query
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

abbrev Sites := ℕ ⊕ ℕ
abbrev LineSpace (E : Type*) [NormedAddCommGroup E] := lp (fun _ : Sites => E) 2
abbrev Channel (E : Type*) [NormedAddCommGroup E] := lp (fun _ : ℕ => E) 2

/-- Orthogonal decomposition in every counter coordinate. -/
def lpOrthogonalSplit (K : Submodule ℂ E) [CompleteSpace K] :
    lp (fun _ : Sites => E) 2 ≃ₗᵢ[ℂ]
      HilbertPair (lp (fun _ : Sites => K) 2) (lp (fun _ : Sites => Kᗮ) 2) :=
  (lpCongr (orthogonalSplit K)).trans lpPair

/-- A coordinate permutation controlled by the known projector onto K. -/
def controlledPermutation (K : Submodule ℂ E) [CompleteSpace K] (e : Sites ≃ Sites) :
    LineSpace E ≃ₗᵢ[ℂ] LineSpace E :=
  (lpOrthogonalSplit K).trans
    ((pairCongr (lpReindex e) (LinearIsometryEquiv.refl ℂ _)).trans (lpOrthogonalSplit K).symm)

@[simp] theorem controlledPermutation_apply (K : Submodule ℂ E) [CompleteSpace K]
    (e : Sites ≃ Sites) (v : LineSpace E) (i : Sites) :
    controlledPermutation K e v i = K.starProjection (v (e.symm i)) + Kᗮ.starProjection (v i) := rfl

/-- Swap the even and odd sites in each first-reflection pair. -/
def firstPairs : Sites ≃ Sites := Equiv.sumComm ℕ ℕ

/-- Swap odd k with even (k+1), leaving the public even 0 unpaired. -/
def nextPair : Sites → Sites
  | .inl 0 => .inl 0
  | .inl (k+1) => .inr k
  | .inr k => .inl (k+1)

lemma nextPair_involutive : Function.Involutive nextPair := by
  intro i
  cases i with
  | inl k => cases k <;> rfl
  | inr k => rfl

def secondPairs : Sites ≃ Sites where
  toFun := nextPair
  invFun := nextPair
  left_inv := nextPair_involutive
  right_inv := nextPair_involutive

@[simp] lemma secondPairs_zero : secondPairs (Sum.inl 0) = Sum.inl 0 := rfl
@[simp] lemma secondPairs_even (k : ℕ) : secondPairs (Sum.inl (k+1)) = Sum.inr k := rfl
@[simp] lemma secondPairs_odd (k : ℕ) : secondPairs (Sum.inr k) = Sum.inl (k+1) := rfl

/-- First work permutation, controlled only by the known input subspace. -/
def shiftKnown (K : Submodule ℂ E) [CompleteSpace K] : LineSpace E ≃ₗᵢ[ℂ] LineSpace E :=
  controlledPermutation K firstPairs

/-- Second work permutation, controlled only by its orthogonal complement. -/
def shiftPerp (K : Submodule ℂ E) [CompleteSpace K] : LineSpace E ≃ₗᵢ[ℂ] LineSpace E :=
  (lpOrthogonalSplit K).trans
    ((pairCongr (LinearIsometryEquiv.refl ℂ _) (lpReindex secondPairs)).trans (lpOrthogonalSplit K).symm)

@[simp] theorem shiftPerp_apply (K : Submodule ℂ E) [CompleteSpace K]
    (v : LineSpace E) (i : Sites) :
    shiftPerp K v i = K.starProjection (v i) + Kᗮ.starProjection (v (secondPairs.symm i)) := rfl

/-- Query all odd sites at the first reflection. -/
def firstLayout : LineSpace E ≃ₗᵢ[ℂ] HilbertPair (Channel E) (Channel E) := lpSum

/-- Query all positive even sites at the second reflection. -/
def secondLayout : LineSpace E ≃ₗᵢ[ℂ] HilbertPair (Channel E) (Channel E) :=
  (lpReindex secondPairs).trans lpSum

/-- Known minus sign on the second query branch, independent of the oracle. -/
def secondMinus : LineSpace E ≃ₗᵢ[ℂ] LineSpace E :=
  secondLayout.trans ((pairCongr (LinearIsometryEquiv.refl ℂ _) (LinearIsometryEquiv.neg ℂ)).trans secondLayout.symm)

/-- One fixed finite circuit, queried with the amplification of R. The two
query supports and all work gates are independent of p and t. -/
def phaseCircuit (K : Submodule ℂ E) [CompleteSpace K] :
    Circuit (LineSpace E) (Channel E) (Channel E) :=
  [.work (shiftKnown K), .query firstLayout, .work (shiftKnown K).symm,
   .work (shiftPerp K), .work secondMinus, .query secondLayout, .work (shiftPerp K).symm]

@[simp] lemma firstLayout_fst (v : LineSpace E) (k : ℕ) : (firstLayout v).fst k = v (Sum.inl k) := rfl
@[simp] lemma firstLayout_snd (v : LineSpace E) (k : ℕ) : (firstLayout v).snd k = v (Sum.inr k) := rfl
@[simp] lemma secondLayout_fst_zero (v : LineSpace E) :
    (secondLayout v).fst 0 = v (Sum.inl 0) := rfl
@[simp] lemma secondLayout_fst_succ (v : LineSpace E) (k : ℕ) :
    (secondLayout v).fst (k+1) = v (Sum.inr k) := rfl
@[simp] lemma secondLayout_snd (v : LineSpace E) (k : ℕ) :
    (secondLayout v).snd k = v (Sum.inl (k+1)) := rfl

@[simp] lemma firstQuery_even (R : E ≃ₗᵢ[ℂ] E) (v : LineSpace E) (k : ℕ) :
    (Gate.query firstLayout).unitary (lpCongr R) v (Sum.inl k) = v (Sum.inl k) := rfl
@[simp] lemma firstQuery_odd (R : E ≃ₗᵢ[ℂ] E) (v : LineSpace E) (k : ℕ) :
    (Gate.query firstLayout).unitary (lpCongr R) v (Sum.inr k) = R (v (Sum.inr k)) := rfl

@[simp] lemma secondQuery_origin (R : E ≃ₗᵢ[ℂ] E) (v : LineSpace E) :
    (Gate.query secondLayout).unitary (lpCongr R) v (Sum.inl 0) = v (Sum.inl 0) := rfl
@[simp] lemma secondQuery_even (R : E ≃ₗᵢ[ℂ] E) (v : LineSpace E) (k : ℕ) :
    (Gate.query secondLayout).unitary (lpCongr R) v (Sum.inl (k+1)) = R (v (Sum.inl (k+1))) := rfl
@[simp] lemma secondQuery_odd (R : E ≃ₗᵢ[ℂ] E) (v : LineSpace E) (k : ℕ) :
    (Gate.query secondLayout).unitary (lpCongr R) v (Sum.inr k) = v (Sum.inr k) := rfl

@[simp] lemma secondMinus_origin (v : LineSpace E) : secondMinus v (Sum.inl 0) = v (Sum.inl 0) := rfl
@[simp] lemma secondMinus_even (v : LineSpace E) (k : ℕ) :
    secondMinus v (Sum.inl (k+1)) = -v (Sum.inl (k+1)) := rfl
@[simp] lemma secondMinus_odd (v : LineSpace E) (k : ℕ) : secondMinus v (Sum.inr k) = v (Sum.inr k) := rfl

lemma secondMinus_query (v : LineSpace E) :
    (secondLayout (secondMinus v)).snd = -(secondLayout v).snd := by
  change (secondLayout (secondLayout.symm
    (pairCongr (LinearIsometryEquiv.refl ℂ _) (LinearIsometryEquiv.neg ℂ) (secondLayout v)))).snd = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

end ELV.Line
