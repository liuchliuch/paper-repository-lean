import Paper18.Fusion.Basic

/-! Restrictions and products of fusion multiplicity data. These are
operations on the algebraic interface, not constructions of tensor categories. -/

noncomputable section
open Classical
open scoped BigOperators
universe u
namespace Paper18.FusionBasis

variable {ι κ : Type u} [Fintype ι] [Fintype κ]

/-- Restrict a fusion basis to a set closed under unit, duals and constituents. -/
def restrict (B : FusionBasis ι) (s : Set ι)
    (h1 : B.one ∈ s) (hd : ∀ x ∈ s, B.dual x ∈ s)
    (hN : ∀ x y, x ∈ s → y ∈ s → ∀ z, 0 < B.N x y z → z ∈ s) :
    FusionBasis s where
  fpdim x := B.fpdim x
  one := ⟨B.one, h1⟩
  dual x := ⟨B.dual x, hd x x.property⟩
  N x y z := B.N x y z
  fpdim_pos x := B.fpdim_pos x
  fpdim_one := B.fpdim_one
  fpdim_dual x := B.fpdim_dual x
  dual_involutive x := Subtype.ext (B.dual_involutive x)
  dual_one := Subtype.ext B.dual_one
  N_one_left x y := by
    by_cases h : x = y
    · subst y; simp [B.N_one_left]
    · have hv : (x : ι) ≠ y := fun he => h (Subtype.ext he)
      simp [B.N_one_left, h, hv]
  N_one_right x y := by
    by_cases h : x = y
    · subst y; simp [B.N_one_right]
    · have hv : (x : ι) ≠ y := fun he => h (Subtype.ext he)
      simp [B.N_one_right, h, hv]
  N_dual x y z := B.N_dual x y z
  N_right x y z := B.N_right x y z
  fpdim_mul x y := by
    have hsum : (∑ z : ι, (B.N x y z : ℝ) * B.fpdim z) =
        ∑ z : s, (B.N x y z : ℝ) * B.fpdim z := by
      apply Finset.sum_congr_set s _ _ (fun _ _ => rfl)
      intro z hz
      have hn : B.N x y z = 0 := by
        by_contra hn
        exact hz (hN x y x.property y.property z (Nat.pos_of_ne_zero hn))
      simp [hn]
    rw [← hsum]
    exact B.fpdim_mul x y

/-- Multiplicity data for the product of two fusion bases. -/
def prod (B : FusionBasis ι) (D : FusionBasis κ) : FusionBasis (ι × κ) where
  fpdim x := B.fpdim x.1 * D.fpdim x.2
  one := (B.one, D.one)
  dual x := (B.dual x.1, D.dual x.2)
  N x y z := B.N x.1 y.1 z.1 * D.N x.2 y.2 z.2
  fpdim_pos x := mul_pos (B.fpdim_pos _) (D.fpdim_pos _)
  fpdim_one := by simp
  fpdim_dual x := by simp
  dual_involutive x := by simp
  dual_one := by simp
  N_one_left x y := by
    rw [B.N_one_left, D.N_one_left]
    by_cases h : x.1 = y.1 <;> by_cases k : x.2 = y.2 <;> simp [h, k, Prod.ext_iff]
  N_one_right x y := by
    rw [B.N_one_right, D.N_one_right]
    by_cases h : x.1 = y.1 <;> by_cases k : x.2 = y.2 <;> simp [h, k, Prod.ext_iff]
  N_dual x y z := by
    rw [B.N_dual x.1 y.1 z.1, D.N_dual x.2 y.2 z.2]
  N_right x y z := by
    rw [B.N_right x.1 y.1 z.1, D.N_right x.2 y.2 z.2]
  fpdim_mul x y := by
    rw [Fintype.sum_prod_type]
    calc
      _ = (∑ a, (B.N x.1 y.1 a : ℝ) * B.fpdim a) *
          (∑ b, (D.N x.2 y.2 b : ℝ) * D.fpdim b) := by
        rw [Fintype.sum_mul_sum]
        apply Finset.sum_congr rfl; intro a _
        apply Finset.sum_congr rfl; intro b _
        push_cast
        ring
      _ = _ := by rw [B.fpdim_mul, D.fpdim_mul]; ring

lemma prod_integral (B : FusionBasis ι) (D : FusionBasis κ)
    (hB : B.Integral) (hD : D.Integral) : (B.prod D).Integral := by
  intro x
  obtain ⟨n, hn⟩ := hB x.1
  obtain ⟨m, hm⟩ := hD x.2
  refine ⟨n * m, ?_⟩
  change B.fpdim x.1 * D.fpdim x.2 = _
  simp [hn, hm]

end Paper18.FusionBasis
