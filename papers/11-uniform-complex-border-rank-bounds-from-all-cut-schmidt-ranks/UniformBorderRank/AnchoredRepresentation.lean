import UniformBorderRank.MatrixCore
import UniformBorderRank.SupportRank
import UniformBorderRank.NormalizedMPS

/-! Reconstruction from a full-rank contracted anchor core. -/
noncomputable section
namespace UniformBorderRank
open Finset

/-- A contraction that is split onto all `r` coordinates is faithful on a row
space of dimension at most `r`. This reconstructs the original rows from the
actual normalized anchor rows, rather than assuming a support decomposition. -/
theorem rowSpan_split_reconstruction {I J : Type*} [Fintype I] [Fintype J]
    (M : I → J → ℂ) (r : ℕ)
    (p : (J → ℂ) →ₗ[ℂ] (Fin r → ℂ)) (L : Fin r → I → ℂ)
    (hnorm : ∀ i j, ∑ a, L i a * p (M a) j = if i = j then 1 else 0)
    (hrank : Module.finrank ℂ (Submodule.span ℂ (Set.range M)) ≤ r) :
    ∀ a z, M a z = ∑ i, p (M a) i * (∑ a', L i a' * M a' z) := by
  classical
  let W := Submodule.span ℂ (Set.range M)
  let row (a : I) : W := ⟨M a, Submodule.subset_span ⟨a, rfl⟩⟩
  let q : W →ₗ[ℂ] (Fin r → ℂ) := p.comp W.subtype
  let s : (Fin r → ℂ) →ₗ[ℂ] W :=
    { toFun := fun x => ∑ i, x i • (∑ a, L i a • row a)
      map_add' := by intro x y; simp [add_smul, sum_add_distrib]
      map_smul' := by intro c x; simp [smul_sum, mul_smul] }
  have hqs : Function.LeftInverse q s := by
    intro x
    ext j
    have hqrow (a : I) : q (row a) = p (M a) := rfl
    simp only [s, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul, hqrow, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    simp only [hnorm]
    simp [mul_ite]
  have hdim : Module.finrank ℂ W = Module.finrank ℂ (Fin r → ℂ) := by
    have hle := s.finrank_le_finrank_of_injective hqs.injective
    change Module.finrank ℂ W ≤ r at hrank
    have he : Module.finrank ℂ (Fin r → ℂ) = r := by simp
    omega
  have hqinj : Function.Injective q :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hqs.surjective
  have hsq (x : W) : s (q x) = x := hqinj (hqs (q x))
  intro a z
  have h := congrArg (fun x : W => x.val z) (hsq (row a))
  simpa [s, q, row, Finset.sum_apply, smul_eq_mul] using h.symm

/-- Left and right support reconstruction from the same contracted core.
`P` and `Q` are the actual coefficient contractions on the other indices. -/
theorem anchored_coefficient_reconstruction {I J U : Type*}
    [Fintype I] [Fintype J] [Fintype U]
    (H : I → J → U → ℂ) (w : U → ℂ) (r : ℕ)
    (X : I → Fin r → ℂ) (Y : Fin r → J → ℂ)
    (L : Fin r → I → ℂ) (R : J → Fin r → ℂ)
    (hleft : ∀ a i, ∑ b, ∑ u, H a b u * w u * R b i = X a i)
    (hright : ∀ b j, ∑ a, ∑ u, L j a * H a b u * w u = Y j b)
    (hLX : ∀ i j, ∑ a, L i a * X a j = if i = j then 1 else 0)
    (hYR : ∀ i j, ∑ b, Y i b * R b j = if i = j then 1 else 0)
    (hrow : Module.finrank ℂ (Submodule.span ℂ (Set.range
      (fun a (z : J × U) => H a z.1 z.2))) ≤ r)
    (hcol : Module.finrank ℂ (Submodule.span ℂ (Set.range
      (fun b (z : I × U) => H z.1 b z.2))) ≤ r) :
    ∀ a b u, H a b u = ∑ i, ∑ j, X a i *
      (∑ a', ∑ b', L i a' * H a' b' u * R b' j) * Y j b := by
  classical
  let p : ((J × U) → ℂ) →ₗ[ℂ] (Fin r → ℂ) :=
    { toFun := fun z i => ∑ b, ∑ u, z (b,u) * w u * R b i
      map_add' := by intros; ext; simp [add_mul, sum_add_distrib]
      map_smul' := by intros; ext; simp [mul_assoc, mul_sum] }
  let q : ((I × U) → ℂ) →ₗ[ℂ] (Fin r → ℂ) :=
    { toFun := fun z j => ∑ a, ∑ u, L j a * z (a,u) * w u
      map_add' := by intros; ext; simp [mul_add, add_mul, sum_add_distrib]
      map_smul' := by intros; ext; simp [mul_left_comm, mul_assoc, mul_sum] }
  have hp (a : I) (i : Fin r) : p (fun z => H a z.1 z.2) i = X a i := hleft a i
  have hq (b : J) (j : Fin r) : q (fun z => H z.1 b z.2) j = Y j b := hright b j
  have hl := rowSpan_split_reconstruction (fun a (z : J × U) => H a z.1 z.2)
    r p L (by simpa only [hp] using hLX) hrow
  have hr := rowSpan_split_reconstruction (fun b (z : I × U) => H z.1 b z.2)
    r q (fun j b => R b j)
    (by
      intro i j
      simp only [hq]
      simpa only [mul_comm, eq_comm] using hYR j i) hcol
  have hl' (a : I) (b : J) (u : U) :
      H a b u = ∑ i, X a i * ∑ a', L i a' * H a' b u := by
    simpa only [hp] using hl a (b,u)
  have hr' (a : I) (b : J) (u : U) :
      H a b u = ∑ j, Y j b * ∑ b', R b' j * H a b' u := by
    simpa only [hq] using hr b (a,u)
  have inner (i : Fin r) (b : J) (u : U) :
      (∑ a', L i a' * H a' b u) =
        ∑ j, (∑ a', ∑ b', L i a' * H a' b' u * R b' j) * Y j b := by
    calc
      _ = ∑ a', L i a' * (∑ j, Y j b * ∑ b', R b' j * H a' b' u) := by
        apply sum_congr rfl
        intro a' _
        rw [← hr']
      _ = _ := by
        simp only [mul_sum, sum_mul]
        rw [sum_comm]
        apply sum_congr rfl
        intro j _
        apply sum_congr rfl
        intro a' _
        apply sum_congr rfl
        intro b' _
        ring
  intro a b u
  rw [hl']
  apply sum_congr rfl
  intro i _
  rw [inner, mul_sum]
  apply sum_congr rfl
  intro j _
  ring

end UniformBorderRank
