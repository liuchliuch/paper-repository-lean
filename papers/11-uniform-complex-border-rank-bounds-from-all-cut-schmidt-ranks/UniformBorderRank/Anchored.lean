import UniformBorderRank.Centralizer
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The distinguished identity block argument in Proposition 2.2. -/
noncomputable section
namespace UniformBorderRank
open Finset

/-- An identity block of full allowed rank determines every other block.
This is the exact block identity underlying equation (8). -/
theorem identity_block_factorization {I J : Type*} [Fintype J] (r : ℕ)
    (H : (I × Fin r) → (J × Fin r) → ℂ) (i₀ : I) (j₀ : J)
    (hcore : ∀ a b, H (i₀, a) (j₀, b) = if a = b then 1 else 0)
    (hrank : Module.finrank ℂ (Submodule.span ℂ (Set.range H)) ≤ r) :
    ∀ i j a b, H (i, a) (j, b) =
      ∑ c : Fin r, H (i, a) (j₀, c) * H (i₀, c) (j, b) := by
  classical
  let W := Submodule.span ℂ (Set.range H)
  let p : W →ₗ[ℂ] (Fin r → ℂ) :=
    { toFun := fun x b => x.val (j₀, b)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let s : (Fin r → ℂ) →ₗ[ℂ] W :=
    { toFun := fun x => ∑ a : Fin r, x a • (⟨H (i₀, a), Submodule.subset_span ⟨(i₀, a), rfl⟩⟩ : W)
      map_add' := by
        intro x y
        apply Subtype.ext
        simp [add_smul, sum_add_distrib]
      map_smul' := by intro c x; simp [smul_sum, mul_smul] }
  have hps : Function.LeftInverse p s := by
    intro x
    ext b
    simp [p, s, hcore, mul_ite, Finset.sum_apply]
  have hsurj : Function.Surjective p := hps.surjective
  have hdim : Module.finrank ℂ W = Module.finrank ℂ (Fin r → ℂ) := by
    have hle := s.finrank_le_finrank_of_injective hps.injective
    change Module.finrank ℂ W ≤ r at hrank
    have he : Module.finrank ℂ (Fin r → ℂ) = r := by simp
    omega
  have hinj : Function.Injective p :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj
  have hsp : ∀ x : W, s (p x) = x := by
    intro x
    apply hinj
    exact hps (p x)
  intro i j a b
  let x : W := ⟨H (i, a), Submodule.subset_span ⟨(i, a), rfl⟩⟩
  have he := congrArg (fun y : W => y.val (j, b)) (hsp x)
  simpa [s, p, x, Finset.sum_apply, smul_eq_mul] using he.symm

/-- Linear transformations of the two matrix sides do not increase rank,
with rank measured as the dimension of the actual row span. -/
theorem rowSpan_finrank_transform_le {I J I' J' : Type*}
    [Fintype I] [Fintype J] [Fintype J']
    (H : I → J → ℂ) (L : I' → I → ℂ) (R : J → J' → ℂ) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range (fun i' j' =>
      ∑ i, ∑ j, L i' i * H i j * R j j'))) ≤
      Module.finrank ℂ (Submodule.span ℂ (Set.range H)) := by
  classical
  let f : (J → ℂ) →ₗ[ℂ] (J' → ℂ) :=
    { toFun := fun x j' => ∑ j, x j * R j j'
      map_add' := by intros; ext; simp [add_mul, sum_add_distrib]
      map_smul' := by intros; ext; simp [mul_assoc, mul_sum] }
  let W := Submodule.span ℂ (Set.range H)
  have hsub : Submodule.span ℂ (Set.range (fun i' j' =>
      ∑ i, ∑ j, L i' i * H i j * R j j')) ≤ W.map f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i', rfl⟩
    have he : (fun j' => ∑ i, ∑ j, L i' i * H i j * R j j') =
        ∑ i, L i' i • f (H i) := by
      ext j'
      simp [f, Finset.sum_apply, mul_sum, mul_assoc]
    change (fun j' => ∑ i, ∑ j, L i' i * H i j * R j j') ∈ W.map f
    rw [he]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    exact ⟨H i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩
  exact (Submodule.finrank_mono hsub).trans (Submodule.finrank_map_le f W)

end UniformBorderRank
