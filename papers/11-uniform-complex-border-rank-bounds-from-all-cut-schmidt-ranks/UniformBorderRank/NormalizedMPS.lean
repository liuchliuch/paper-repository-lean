import UniformBorderRank.Anchored
import UniformBorderRank.MPSBound
import Mathlib.LinearAlgebra.Multilinear.Basic

/-! The normalized matrix-product part of Proposition 2.2.  The original-tensor
construction and support reconstruction are supplied by `RawCore`,
`AnchoredRepresentation`, and `OriginalPresentation`.
The rank assumption below concerns actual evaluated block matrices. -/
noncomputable section
namespace UniformBorderRank
open Finset

variable {N r : ℕ} {V : Fin N → Type*}

def mixArguments (x b : ∀ i, V i) (S : Finset (Fin N)) : ∀ i, V i :=
  fun i => if i ∈ S then x i else b i

@[simp] lemma mixArguments_empty (x b : ∀ i, V i) : mixArguments x b ∅ = b := by
  ext i; simp [mixArguments]
@[simp] lemma mixArguments_univ (x b : ∀ i, V i) : mixArguments x b univ = x := by
  ext i; simp [mixArguments]

/-- Two choices of covectors on each side of a cut produce a 2-by-2 block
matrix with `r`-by-`r` blocks. -/
def evaluatedCutBlocks (Phi : (∀ i, V i) → EndMat r) (b x : ∀ i, V i)
    (S : Finset (Fin N)) : (Fin 2 × Fin r) → (Fin 2 × Fin r) → ℂ :=
  fun p q => Phi (fun i => if i ∈ S then
    (if p.1 = 0 then b i else x i) else (if q.1 = 0 then b i else x i)) p.2 q.2

theorem normalized_cut_identity (Phi : (∀ i, V i) → EndMat r) (b : ∀ i, V i)
    (hcore : Phi b = 1)
    (hrank : ∀ (x : ∀ i, V i) (S : Finset (Fin N)),
      Module.finrank ℂ (Submodule.span ℂ (Set.range (evaluatedCutBlocks Phi b x S))) ≤ r)
    (x : ∀ i, V i) (S : Finset (Fin N)) :
    Phi x = Phi (mixArguments x b S) * Phi (mixArguments b x S) := by
  classical
  have h0 : ∀ a c, evaluatedCutBlocks Phi b x S (0, a) (0, c) =
      if a = c then 1 else 0 := by
    intro a c
    have he : (fun i => if i ∈ S then (if (0 : Fin 2) = 0 then b i else x i)
      else (if (0 : Fin 2) = 0 then b i else x i)) = b := by ext i; simp
    change Phi _ a c = _
    rw [he, hcore]
    rfl
  have hh := identity_block_factorization r (evaluatedCutBlocks Phi b x S) 0 0 h0 (hrank x S)
  ext a c
  have hx : (fun i => if i ∈ S then (if (1 : Fin 2) = 0 then b i else x i)
    else (if (1 : Fin 2) = 0 then b i else x i)) = x := by ext i; simp
  have h1 : (fun i => if i ∈ S then (if (1 : Fin 2) = 0 then b i else x i)
    else (if (0 : Fin 2) = 0 then b i else x i)) = mixArguments x b S := by
      ext i; simp [mixArguments]
  have h2 : (fun i => if i ∈ S then (if (0 : Fin 2) = 0 then b i else x i)
    else (if (1 : Fin 2) = 0 then b i else x i)) = mixArguments b x S := by
      ext i; simp [mixArguments]
  have h := hh 1 1 a c
  simp only [evaluatedCutBlocks, hx] at h
  exact h

lemma mixArguments_insert (x b : ∀ i, V i) (S : Finset (Fin N)) (i : Fin N) :
    mixArguments x b (insert i S) = Function.update (mixArguments x b S) i (x i) := by
  ext j
  by_cases hj : j = i
  · subst j; simp [mixArguments]
  · simp [mixArguments, hj]

/-- Extract one singleton from a partial product. -/
lemma normalized_extract_singleton (Phi : (∀ i, V i) → EndMat r) (b : ∀ i, V i)
    (hsplit : ∀ x S, Phi x = Phi (mixArguments x b S) * Phi (mixArguments b x S))
    (x : ∀ i, V i) (S : Finset (Fin N)) (i : Fin N) (hi : i ∉ S) :
    Phi (mixArguments x b (insert i S)) =
      Phi (Function.update b i (x i)) * Phi (mixArguments x b S) := by
  have h := hsplit (mixArguments x b (insert i S)) {i}
  have h1 : mixArguments (mixArguments x b (insert i S)) b {i} = Function.update b i (x i) := by
    ext j
    by_cases hj : j = i
    · subst j; simp [mixArguments]
    · simp [mixArguments, hj]
  have h2 : mixArguments b (mixArguments x b (insert i S)) {i} = mixArguments x b S := by
    ext j
    by_cases hj : j = i
    · subst j; simp [mixArguments, hi]
    · simp [mixArguments, hj]
  rw [h1, h2] at h
  exact h

theorem normalized_any_order_product (Phi : (∀ i, V i) → EndMat r) (b : ∀ i, V i)
    (hcore : Phi b = 1)
    (hsplit : ∀ x S, Phi x = Phi (mixArguments x b S) * Phi (mixArguments b x S))
    (x : ∀ i, V i) (L : List (Fin N)) (hL : L.Nodup) :
    Phi (mixArguments x b L.toFinset) =
      (L.map (fun i => Phi (Function.update b i (x i)))).prod := by
  induction L with
  | nil => simpa using hcore
  | cons i L ih =>
    rw [List.nodup_cons] at hL
    rw [List.toFinset_cons, normalized_extract_singleton Phi b hsplit x L.toFinset i
      (by simpa only [List.mem_toFinset] using hL.1), ih hL.2]
    rfl

/-- Distinct sites commute; no commutativity is imposed on two choices at
one site. -/
theorem normalized_site_commute (Phi : (∀ i, V i) → EndMat r) (b : ∀ i, V i)
    (hsplit : ∀ x S, Phi x = Phi (mixArguments x b S) * Phi (mixArguments b x S))
    (i j : Fin N) (hij : i ≠ j) (x : V i) (y : V j) :
    Phi (Function.update b i x) * Phi (Function.update b j y) =
      Phi (Function.update b j y) * Phi (Function.update b i x) := by
  let z := Function.update (Function.update b i x) j y
  have he₁ := hsplit z {i}
  have he₂ := hsplit z {j}
  have h₁ : mixArguments z b {i} = Function.update b i x := by
    ext k
    by_cases hk : k = i
    · subst k; simp [mixArguments, z, hij]
    · simp [mixArguments, hk]
  have h₂ : mixArguments b z {i} = Function.update b j y := by
    ext k
    by_cases hk : k = i
    · subst k; simp [mixArguments, z, hij]
    · simp only [mixArguments, mem_singleton, if_neg hk]
      by_cases hkj : k = j
      · subst k; simp [z]
      · simp [z, Function.update_of_ne hkj, Function.update_of_ne hk]
  have h₃ : mixArguments z b {j} = Function.update b j y := by
    ext k
    by_cases hk : k = j
    · subst k; simp [mixArguments, z]
    · simp [mixArguments, hk]
  have h₄ : mixArguments b z {j} = Function.update b i x := by
    ext k
    by_cases hk : k = j
    · subst k; simp [mixArguments, z, Ne.symm hij]
    · simp [mixArguments, z, hk]
  rw [h₁, h₂] at he₁
  rw [h₃, h₄] at he₂
  exact he₁.symm.trans he₂

/-- Linear site maps, cross-site commutation, and arbitrary-order product
formula from a normalized core and the evaluated cut-rank constraints. -/
theorem normalized_matrix_product_form
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (Phi : MultilinearMap ℂ V (EndMat r)) (b : ∀ i, V i)
    (hcore : Phi b = 1)
    (hrank : ∀ (x : ∀ i, V i) (S : Finset (Fin N)),
      Module.finrank ℂ (Submodule.span ℂ (Set.range (evaluatedCutBlocks Phi b x S))) ≤ r) :
    (∀ i, Phi.toLinearMap b i (b i) = 1) ∧
    (∀ i j, i ≠ j → ∀ (x : V i) (y : V j),
      Phi.toLinearMap b i x * Phi.toLinearMap b j y =
        Phi.toLinearMap b j y * Phi.toLinearMap b i x) ∧
    (∀ (x : ∀ i, V i) (L : List (Fin N)), L.Nodup → L.toFinset = univ →
      Phi x = (L.map (fun i => Phi.toLinearMap b i (x i))).prod) := by
  have hsplit := normalized_cut_identity Phi b hcore hrank
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simpa [MultilinearMap.toLinearMap] using hcore
  · intro i j hij x y
    exact normalized_site_commute Phi b hsplit i j hij x y
  · intro x L hL hcover
    have hh := normalized_any_order_product Phi b hcore hsplit x L hL
    rw [hcover, mixArguments_univ] at hh
    exact hh

/-- Uniform border-rank estimate for a normalized anchored core. The
construction from the original tensor is proved in `OriginalPresentation`. -/
theorem borderRankLe_normalized_core {N r : ℕ} {d : Fin N → ℕ}
    (hN : 0 < N) (hr : 1 ≤ r) (hd : ∀ i, d i ≤ r)
    (Phi : MultilinearMap ℂ (fun i : Fin N => Fin (d i) → ℂ) (EndMat r))
    (b : ∀ i, Fin (d i) → ℂ) (hcore : Phi b = 1)
    (hrank : ∀ (x : ∀ i, Fin (d i) → ℂ) (S : Finset (Fin N)),
      Module.finrank ℂ (Submodule.span ℂ (Set.range (evaluatedCutBlocks Phi b x S))) ≤ r)
    (ell : EndMat r →ₗ[ℂ] ℂ) :
    borderRankLe (d := d) (fun u => ell (Phi (fun i => Pi.single (u i) 1)))
      (r ^ (r ^ 2 - 1) * F (r ^ 2)) := by
  classical
  let M := fun i => Phi.toLinearMap b i
  let A := fun i => Algebra.adjoin ℂ (Set.range (M i))
  have hsplit := normalized_cut_identity Phi b hcore hrank
  have hcross : ∀ i j, i ≠ j → CrossComm (A i : Set (EndMat r)) (A j : Set (EndMat r)) := by
    intro i j hij
    apply crossComm_adjoin
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact normalized_site_commute Phi b hsplit i j hij x y
  let v : ∀ i, Fin (d i) → EndMat r := fun i x => M i (Pi.single x 1)
  have hv : ∀ i x, v i x ∈ A i := fun i x => Algebra.subset_adjoin ⟨Pi.single x 1, rfl⟩
  have he : (fun u : ∀ i, Fin (d i) => ell (Phi (fun i => Pi.single (u i) 1))) =
      (fun u => ell (univ.noncommProd (fun i => v i (u i))
        (fun i _ j _ hij => hcross i j hij _ (hv i _) _ (hv j _)))) := by
    ext u
    apply congrArg ell
    have hh := normalized_any_order_product Phi b hcore hsplit (fun i => Pi.single (u i) 1)
      (univ : Finset (Fin N)).toList (Finset.nodup_toList _)
    simp only [Finset.toList_toFinset, mixArguments_univ] at hh
    have hp := Finset.noncommProd_toFinset (univ : Finset (Fin N)).toList (fun i => v i (u i))
      (fun i _ j _ hij => hcross i j hij _ (hv i _) _ (hv j _)) (Finset.nodup_toList _)
    simp only [Finset.toList_toFinset] at hp
    exact hh.trans hp.symm
  rw [he]
  exact borderRankLe_cross_commuting_product hN hr hd A hcross v hv ell

end UniformBorderRank
