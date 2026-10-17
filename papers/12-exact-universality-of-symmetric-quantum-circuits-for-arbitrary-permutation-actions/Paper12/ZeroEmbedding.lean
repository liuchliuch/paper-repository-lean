import Paper12.StateVectors
import Paper12.Amplify
import Paper12.CircuitUnitary

noncomputable section
namespace Paper12
open Matrix Classical
variable {X W : Type*} [Fintype X] [Fintype W]

def zeroBasisMap (a : Basis X) : Basis (X ⊕ W) := Sum.elim a (fun _ => 0)

theorem zeroBasisMap_injective : Function.Injective (zeroBasisMap (X := X) (W := W)) := by
  intro a b h
  funext x
  exact congrFun h (Sum.inl x)

theorem zeroBasisMap_match (a : Basis X) (b : Basis (X ⊕ W)) :
    zeroBasisMap a = b ↔ a = b ∘ Sum.inl ∧ b ∘ Sum.inr = fun _ => 0 := by
  constructor
  · intro h
    constructor
    · funext x; exact congrFun h (Sum.inl x)
    · funext x; exact (congrFun h (Sum.inr x)).symm
  · rintro ⟨hL, hR⟩
    funext x
    cases x with
    | inl x => exact congrFun hL x
    | inr x => exact (congrFun hR x).symm

def zeroEmbed : Matrix (Basis (X ⊕ W)) (Basis X) ℂ :=
  fun b a => if zeroBasisMap a = b then 1 else 0

theorem zeroEmbed_left {K : Type*} (M : Matrix (Basis (X ⊕ W)) K ℂ) (a : Basis X) (k : K) :
    ((zeroEmbed (X := X) (W := W))ᴴ * M) a k = M (zeroBasisMap a) k := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, zeroEmbed]
  rw [Finset.sum_eq_single (zeroBasisMap a)]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · intro hb; exact (hb (Finset.mem_univ _)).elim

theorem zeroEmbed_right {K : Type*} (M : Matrix K (Basis (X ⊕ W)) ℂ) (k : K) (a : Basis X) :
    (M * (zeroEmbed (X := X) (W := W))) k a = M k (zeroBasisMap a) := by
  simp only [Matrix.mul_apply, zeroEmbed]
  rw [Finset.sum_eq_single (zeroBasisMap a)]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · intro hb; exact (hb (Finset.mem_univ _)).elim

theorem zeroEmbed_isometry : IsIsometry (zeroEmbed (X := X) (W := W)) := by
  ext a b
  rw [zeroEmbed_left]
  simp only [zeroEmbed, zeroBasisMap_injective.eq_iff, Matrix.one_apply]
  simp only [eq_comm]

theorem zeroEmbed_projector : zeroEmbed (X := X) (W := W) * zeroEmbedᴴ =
    predicateProjector (fun b : Basis (X ⊕ W) => b ∘ Sum.inr = fun _ => 0) := by
  ext b c
  simp only [Matrix.mul_apply, zeroEmbed, Matrix.conjTranspose_apply,
    predicateProjector, Matrix.diagonal_apply]
  by_cases hb : b ∘ Sum.inr = (fun _ : W => (0 : Fin 2))
  · have hz : zeroBasisMap (b ∘ Sum.inl) = b := (zeroBasisMap_match _ _).mpr ⟨rfl, hb⟩
    rw [Finset.sum_eq_single (b ∘ Sum.inl)]
    · by_cases hbc : b = c
      · subst c; simp [hz, hb]
      · have hn : zeroBasisMap (b ∘ Sum.inl) ≠ c := by rwa [hz]
        simp [hz, hn, hbc]
    · intro a _ ha
      have hn : zeroBasisMap a ≠ b := fun h => ha ((zeroBasisMap_match _ _).mp h).1
      simp [hn]
    · intro ha; exact (ha (Finset.mem_univ _)).elim
  · have hzero : (∑ a : Basis X,
        (if zeroBasisMap a = b then (1 : ℂ) else 0) *
          star (if zeroBasisMap a = c then (1 : ℂ) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      have hn : zeroBasisMap a ≠ b := fun h => hb ((zeroBasisMap_match _ _).mp h).2
      simp [hn]
    rw [hzero]
    by_cases hbc : b = c
    · subst c; simp [hb]
    · simp [hbc]

theorem zeroEmbed_column (ψ : Vec X) : zeroEmbed * column ψ = column (embedZero (W := W) ψ) := by
  ext b u
  simp only [Matrix.mul_apply, zeroEmbed, column, embedZero]
  have hwork : (∀ w : W, b (Sum.inr w) = 0) ↔ b ∘ Sum.inr = fun _ => 0 :=
    ⟨fun h => funext h, fun h w => congrFun h w⟩
  by_cases hb : b ∘ Sum.inr = (fun _ : W => (0 : Fin 2))
  · have hz : zeroBasisMap (b ∘ Sum.inl) = b := (zeroBasisMap_match _ _).mpr ⟨rfl, hb⟩
    rw [if_pos (hwork.mpr hb), Finset.sum_eq_single (b ∘ Sum.inl)]
    · simp [hz]; rfl
    · intro a _ ha
      have hn : zeroBasisMap a ≠ b := fun h => ha ((zeroBasisMap_match _ _).mp h).1
      simp [hn]
    · intro ha; exact (ha (Finset.mem_univ _)).elim
  · rw [if_neg (fun h => hb (hwork.mp h))]
    apply Finset.sum_eq_zero
    intro a _
    have hn : zeroBasisMap a ≠ b := fun h => hb ((zeroBasisMap_match _ _).mp h).2
    simp [hn]

theorem zeroEmbed_block (A : Op (X ⊕ W)) :
    (zeroEmbed (X := X) (W := W))ᴴ * A * zeroEmbed (X := X) (W := W) = zeroBlock A := by
  ext a b
  rw [zeroEmbed_right, zeroEmbed_left]
  dsimp only [zeroBlock, Matrix.of_apply]
  congr 1 <;> (funext t; cases t <;> rfl)

theorem isometry_comp {D K L : Type*} [Fintype D] [Fintype K] [Fintype L]
    [DecidableEq D] [DecidableEq K] [DecidableEq L]
    (A : Matrix D K ℂ) (B : Matrix K L ℂ) (hA : IsIsometry A) (hB : IsIsometry B) :
    IsIsometry (A * B) := by
  unfold IsIsometry at *
  rw [Matrix.conjTranspose_mul]
  calc _ = Bᴴ * (Aᴴ * A) * B := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hA, Matrix.mul_one, hB]

open scoped ComplexOrder in
theorem isometries_eq_of_cross {D K : Type*} [Fintype D] [Fintype K]
    [DecidableEq D] [DecidableEq K] (S G : Matrix D K ℂ)
    (hS : IsIsometry S) (hG : IsIsometry G) (hcross : Gᴴ * S = 1) : S = G := by
  have hother : Sᴴ * G = 1 := by
    have h := congrArg Matrix.conjTranspose hcross
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_one] using h
  have hzero : (S - G)ᴴ * (S - G) = 0 := by
    rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      hS, hG, hcross, hother]
    simp
  exact sub_eq_zero.mp (Matrix.conjTranspose_mul_self_eq_zero.mp hzero)

/-- A unitary block of a unitary circuit already gives clean implementation;
there is no failure component left. This handles the lambda=1 boundary case. -/
theorem unitary_zeroBlock_clean (C : Circuit (X ⊕ W)) (V : Op X)
    (hV : Vᴴ * V = 1) (hb : zeroBlock C.unitary = V) : CleanImplements C V := by
  have hS : IsIsometry (C.unitary * zeroEmbed (X := X) (W := W)) :=
    isometry_comp _ _ (Circuit.unitary_isUnitary C) zeroEmbed_isometry
  have hG : IsIsometry (zeroEmbed (X := X) (W := W) * V) :=
    isometry_comp _ _ zeroEmbed_isometry hV
  have hcross : ((zeroEmbed (X := X) (W := W)) * V)ᴴ *
      (C.unitary * zeroEmbed (X := X) (W := W)) = 1 := by
    rw [Matrix.conjTranspose_mul]
    calc _ = Vᴴ * ((zeroEmbed (X := X) (W := W))ᴴ * C.unitary * zeroEmbed (X := X) (W := W)) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [zeroEmbed_block, hb, hV]
  have hAE := isometries_eq_of_cross _ _ hS hG hcross
  intro ψ
  have h := congrArg (fun M => M * column ψ) hAE
  simp only [Matrix.mul_assoc, zeroEmbed_column, column_apply] at h
  funext b
  exact congrFun (congrFun h b) ()
end Paper12
