import Paper13.Basic

/-!
# Singlet projector identities

On qubits `a ≠ b` the singlet projector is `q = (1 - SWAP_{ab}) • 2⁻¹`.
Paper eq. (14): `(A_a + A_b) q = q (A_a + A_b) = 0` for `A ∈ {X, Z}`.

`singletQ` is an abbreviation for `Basic.singletProj`.
-/

noncomputable section

namespace Paper13

open Matrix
open scoped BigOperators

/-! ## `swapBasis` / `swapAt` -/

lemma swapBasis_apply {n : ℕ} (a b : Fin n) (x : QubitBasis n) (w : Fin n) :
    swapBasis a b x w = if w = a then x b else if w = b then x a else x w := by
  simp only [swapBasis, Function.update]
  split_ifs <;> simp_all

lemma swapBasis_a {n : ℕ} (a b : Fin n) (x : QubitBasis n) (hab : a ≠ b) :
    swapBasis a b x a = x b := by
  rw [swapBasis_apply]; simp [hab]

lemma swapBasis_b {n : ℕ} (a b : Fin n) (x : QubitBasis n) (hab : a ≠ b) :
    swapBasis a b x b = x a := by
  rw [swapBasis_apply]; simp [Ne.symm hab]

lemma swapBasis_other {n : ℕ} (a b : Fin n) (x : QubitBasis n) (w : Fin n)
    (hwa : w ≠ a) (hwb : w ≠ b) : swapBasis a b x w = x w := by
  rw [swapBasis_apply]; simp [hwa, hwb]

lemma swapAt_mul_swapAt {n : ℕ} (a b : Fin n) : swapAt a b * swapAt a b = 1 := by
  apply Matrix.ext
  intro x y
  simp only [Matrix.mul_apply, swapAt, Matrix.one_apply]
  have hsum :
      (∑ z : QubitBasis n,
          (if x = swapBasis a b z then (1 : ℂ) else 0) *
            (if z = swapBasis a b y then (1 : ℂ) else 0)) =
        if x = swapBasis a b (swapBasis a b y) then (1 : ℂ) else 0 := by
    rw [Fintype.sum_eq_single (swapBasis a b y)]
    · have h1 : (if swapBasis a b y = swapBasis a b y then (1 : ℂ) else 0) = 1 := if_pos rfl
      rw [h1, mul_one]
    · intro z hz
      have h1 : (if z = swapBasis a b y then (1 : ℂ) else 0) = 0 := if_neg hz
      rw [h1, mul_zero]
  rw [hsum, swapBasis_involutive a b y]

lemma swapAt_conjTranspose {n : ℕ} (a b : Fin n) :
    conjTranspose (swapAt a b) = swapAt a b := by
  apply Matrix.ext
  intro x y
  show (star (if y = swapBasis a b x then (1 : ℂ) else 0))
      = (if x = swapBasis a b y then (1 : ℂ) else 0)
  by_cases h : x = swapBasis a b y
  · have h2 : y = swapBasis a b x := by
      have h' : swapBasis a b x = y := by
        rw [h]
        exact swapBasis_involutive a b y
      exact h'.symm
    rw [if_pos h, if_pos h2]
    simp
  · have h2 : ¬ (y = swapBasis a b x) := by
      intro heq
      apply h
      have h' : swapBasis a b y = x := by
        rw [heq]
        exact swapBasis_involutive a b x
      exact h'.symm
    rw [if_neg h, if_neg h2]
    simp

lemma swapAt_self {n : ℕ} (a : Fin n) : swapAt a a = 1 := by
  apply Matrix.ext
  intro x y
  simp only [swapAt, swapBasis_self, Matrix.one_apply]

/-- Correct singlet projector `(1 - SWAP_{ab}) • 2⁻¹`. -/
abbrev singletQ {n : ℕ} (a b : Fin n) : Op n := singletProj a b

lemma singletQ_eq {n : ℕ} (a b : Fin n) :
    singletQ a b = (2 : ℂ)⁻¹ • (1 - swapAt a b) := rfl

/-! ## Pauli bits -/

lemma pauliX_eq (i j : Fin 2) : pauliX i j = if i = j then 0 else 1 := by
  fin_cases i <;> fin_cases j <;> simp [pauliX]

lemma pauliZ_eq (i j : Fin 2) : pauliZ i j = if i ≠ j then 0 else if i = 0 then 1 else -1 := by
  fin_cases i <;> fin_cases j <;> simp [pauliZ]

lemma ite_ne_zero_eq {α : Type} [Zero α] (i j : Fin 2) (v : α) :
    (if i ≠ j then (0:α) else v) = (if i = j then v else 0) := by
  by_cases h : i = j <;> simp [h]

lemma bitsX (A B C D : Fin 2) :
    (if B = C then (if A = D then (0:ℂ) else 1) else 0)
      + (if A = D then (if B = C then (0:ℂ) else 1) else 0)
    = (if B = D then (if A = C then (0:ℂ) else 1) else 0)
      + (if A = C then (if B = D then (0:ℂ) else 1) else 0) := by
  have h : (if B = C then (if A = D then (0:ℤ) else 1) else 0)
      + (if A = D then (if B = C then (0:ℤ) else 1) else 0)
    = (if B = D then (if A = C then (0:ℤ) else 1) else 0)
      + (if A = C then (if B = D then (0:ℤ) else 1) else 0) := by
    fin_cases A <;> fin_cases B <;> fin_cases C <;> fin_cases D <;> decide
  exact_mod_cast h

lemma bitsZ (A B C D : Fin 2) :
    (if B = C then (if A = D then (if A = 0 then (1:ℂ) else -1) else 0) else 0)
      + (if A = D then (if B = C then (if B = 0 then (1:ℂ) else -1) else 0) else 0)
    = (if B = D then (if A = C then (if A = 0 then (1:ℂ) else -1) else 0) else 0)
      + (if A = C then (if B = D then (if B = 0 then (1:ℂ) else -1) else 0) else 0) := by
  have h : (if B = C then (if A = D then (if A = 0 then (1:ℤ) else -1) else 0) else 0)
      + (if A = D then (if B = C then (if B = 0 then (1:ℤ) else -1) else 0) else 0)
    = (if B = D then (if A = C then (if A = 0 then (1:ℤ) else -1) else 0) else 0)
      + (if A = C then (if B = D then (if B = 0 then (1:ℤ) else -1) else 0) else 0) := by
    fin_cases A <;> fin_cases B <;> fin_cases C <;> fin_cases D <;> decide
  exact_mod_cast h

/-! ## Collective vs `swapAt` -/

lemma cond_embed_a_swap {n : ℕ} (a b : Fin n) (x y : QubitBasis n) (hab : a ≠ b) :
    (∀ w, w ≠ a → x w = swapBasis a b y w) ↔ (x b = y a ∧ ∀ w, w ≠ a → w ≠ b → x w = y w) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := h b (Ne.symm hab); rwa [swapBasis_b a b y hab] at this
    · intro w hwa hwb
      have := h w hwa; rwa [swapBasis_other a b y w hwa hwb] at this
  · intro h w hwa
    by_cases hwb : w = b
    · rw [hwb, swapBasis_b a b y hab]; exact h.1
    · rw [swapBasis_other a b y w hwa hwb]; exact h.2 w hwa hwb

lemma cond_embed_b_swap {n : ℕ} (a b : Fin n) (x y : QubitBasis n) (hab : a ≠ b) :
    (∀ w, w ≠ b → x w = swapBasis a b y w) ↔ (x a = y b ∧ ∀ w, w ≠ a → w ≠ b → x w = y w) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := h a hab; rwa [swapBasis_a a b y hab] at this
    · intro w hwa hwb
      have := h w hwb; rwa [swapBasis_other a b y w hwa hwb] at this
  · intro h w hwb
    by_cases hwa : w = a
    · rw [hwa, swapBasis_a a b y hab]; exact h.1
    · rw [swapBasis_other a b y w hwa hwb]; exact h.2 w hwa hwb

lemma cond_embed_a {n : ℕ} (a b : Fin n) (x y : QubitBasis n) (hab : a ≠ b) :
    (∀ w, w ≠ a → x w = y w) ↔ (x b = y b ∧ ∀ w, w ≠ a → w ≠ b → x w = y w) := by
  constructor
  · intro h; exact ⟨h b (Ne.symm hab), fun w hwa hwb => h w hwa⟩
  · intro h w hwa
    by_cases hwb : w = b
    · rw [hwb]; exact h.1
    · exact h.2 w hwa hwb

lemma cond_embed_b {n : ℕ} (a b : Fin n) (x y : QubitBasis n) (hab : a ≠ b) :
    (∀ w, w ≠ b → x w = y w) ↔ (x a = y a ∧ ∀ w, w ≠ a → w ≠ b → x w = y w) := by
  constructor
  · intro h; exact ⟨h a hab, fun w hwa hwb => h w hwb⟩
  · intro h w hwb
    by_cases hwa : w = a
    · rw [hwa]; exact h.1
    · exact h.2 w hwa hwb

lemma entryX_collective_swap {n : ℕ} (a b : Fin n) (x y : QubitBasis n) (hab : a ≠ b) :
    embed pauliX a x (swapBasis a b y) + embed pauliX b x (swapBasis a b y)
      = embed pauliX a x y + embed pauliX b x y := by
  have hA : swapBasis a b y a = y b := swapBasis_a a b y hab
  have hB : swapBasis a b y b = y a := swapBasis_b a b y hab
  have h1 := cond_embed_a_swap a b x y hab
  have h2 := cond_embed_b_swap a b x y hab
  have h3 := cond_embed_a a b x y hab
  have h4 := cond_embed_b a b x y hab
  simp only [embed, h1, h2, h3, h4, hA, hB]
  by_cases hoff : ∀ w, w ≠ a → w ≠ b → x w = y w
  · have hoffT : (∀ w : Fin n, w ≠ a → w ≠ b → x w = y w) = True :=
      propext ⟨fun _ => trivial, fun _ => hoff⟩
    simp only [hoffT, and_true]
    rw [pauliX_eq, pauliX_eq, pauliX_eq, pauliX_eq]
    exact bitsX (x a) (x b) (y a) (y b)
  · have n1 : ¬ (x b = y a ∧ ∀ w, w ≠ a → w ≠ b → x w = y w) := fun h => hoff h.2
    have n2 : ¬ (x a = y b ∧ ∀ w, w ≠ a → w ≠ b → x w = y w) := fun h => hoff h.2
    have n3 : ¬ (x b = y b ∧ ∀ w, w ≠ a → w ≠ b → x w = y w) := fun h => hoff h.2
    have n4 : ¬ (x a = y a ∧ ∀ w, w ≠ a → w ≠ b → x w = y w) := fun h => hoff h.2
    rw [if_neg n1, if_neg n2, if_neg n3, if_neg n4]

lemma entryZ_collective_swap {n : ℕ} (a b : Fin n) (x y : QubitBasis n) (hab : a ≠ b) :
    embed pauliZ a x (swapBasis a b y) + embed pauliZ b x (swapBasis a b y)
      = embed pauliZ a x y + embed pauliZ b x y := by
  have hA : swapBasis a b y a = y b := swapBasis_a a b y hab
  have hB : swapBasis a b y b = y a := swapBasis_b a b y hab
  have h1 := cond_embed_a_swap a b x y hab
  have h2 := cond_embed_b_swap a b x y hab
  have h3 := cond_embed_a a b x y hab
  have h4 := cond_embed_b a b x y hab
  simp only [embed, h1, h2, h3, h4, hA, hB]
  by_cases hoff : ∀ w, w ≠ a → w ≠ b → x w = y w
  · have hoffT : (∀ w : Fin n, w ≠ a → w ≠ b → x w = y w) = True :=
      propext ⟨fun _ => trivial, fun _ => hoff⟩
    simp only [hoffT, and_true]
    rw [pauliZ_eq, pauliZ_eq, pauliZ_eq, pauliZ_eq]
    rw [ite_ne_zero_eq, ite_ne_zero_eq, ite_ne_zero_eq, ite_ne_zero_eq]
    exact bitsZ (x a) (x b) (y a) (y b)
  · have n1 : ¬ (x b = y a ∧ ∀ w, w ≠ a → w ≠ b → x w = y w) := fun h => hoff h.2
    have n2 : ¬ (x a = y b ∧ ∀ w, w ≠ a → w ≠ b → x w = y w) := fun h => hoff h.2
    have n3 : ¬ (x b = y b ∧ ∀ w, w ≠ a → w ≠ b → x w = y w) := fun h => hoff h.2
    have n4 : ¬ (x a = y a ∧ ∀ w, w ≠ a → w ≠ b → x w = y w) := fun h => hoff h.2
    rw [if_neg n1, if_neg n2, if_neg n3, if_neg n4]

lemma collectiveX_mul_swapAt {n : ℕ} (a b : Fin n) :
    collective pauliX a b * swapAt a b = collective pauliX a b := by
  by_cases hab : a = b
  · subst hab; rw [swapAt_self, mul_one]
  · apply Matrix.ext
    intro x y
    simp only [Matrix.mul_apply, swapAt, collective]
    have hsum :
        (∑ z : QubitBasis n,
            (embed pauliX a + embed pauliX b) x z *
              (if z = swapBasis a b y then (1 : ℂ) else 0)) =
          (embed pauliX a + embed pauliX b) x (swapBasis a b y) := by
      rw [Fintype.sum_eq_single (swapBasis a b y)]
      · simp
      · intro z hz; simp [hz]
    rw [hsum]
    exact entryX_collective_swap a b x y hab

lemma collectiveZ_mul_swapAt {n : ℕ} (a b : Fin n) :
    collective pauliZ a b * swapAt a b = collective pauliZ a b := by
  by_cases hab : a = b
  · subst hab; rw [swapAt_self, mul_one]
  · apply Matrix.ext
    intro x y
    simp only [Matrix.mul_apply, swapAt, collective]
    have hsum :
        (∑ z : QubitBasis n,
            (embed pauliZ a + embed pauliZ b) x z *
              (if z = swapBasis a b y then (1 : ℂ) else 0)) =
          (embed pauliZ a + embed pauliZ b) x (swapBasis a b y) := by
      rw [Fintype.sum_eq_single (swapBasis a b y)]
      · simp
      · intro z hz; simp [hz]
    rw [hsum]
    exact entryZ_collective_swap a b x y hab

lemma embed_conjTranspose {n : ℕ} (A : Op1) (hA : conjTranspose A = A) (v : Fin n) :
    conjTranspose (embed A v) = embed A v := by
  apply Matrix.ext
  intro x y
  simp only [Matrix.conjTranspose_apply, embed]
  by_cases h : ∀ w, w ≠ v → x w = y w
  · have h' : ∀ w, w ≠ v → y w = x w := fun w hw => (h w hw).symm
    rw [if_pos h, if_pos h']
    have hxy : A (y v) (x v) = star (A (x v) (y v)) := by
      have e1 : (conjTranspose A) (y v) (x v) = star (A (x v) (y v)) := by
        simp [Matrix.conjTranspose_apply]
      rw [hA] at e1
      exact e1
    rw [hxy]
    simp
  · have h' : ¬ ∀ w, w ≠ v → y w = x w := by
      intro hh
      apply h
      intro w hw
      exact (hh w hw).symm
    rw [if_neg h, if_neg h']
    simp

lemma collectiveX_conjTranspose {n : ℕ} (a b : Fin n) :
    conjTranspose (collective pauliX a b) = collective pauliX a b := by
  simp [collective, conjTranspose_add, embed_conjTranspose, pauliX_conjTranspose]

lemma collectiveZ_conjTranspose {n : ℕ} (a b : Fin n) :
    conjTranspose (collective pauliZ a b) = collective pauliZ a b := by
  simp [collective, conjTranspose_add, embed_conjTranspose, pauliZ_conjTranspose]

lemma swapAt_mul_collectiveX {n : ℕ} (a b : Fin n) :
    swapAt a b * collective pauliX a b = collective pauliX a b := by
  have h1 : conjTranspose (swapAt a b * collective pauliX a b) = collective pauliX a b := by
    rw [conjTranspose_mul, swapAt_conjTranspose, collectiveX_conjTranspose,
      collectiveX_mul_swapAt]
  calc swapAt a b * collective pauliX a b
      = conjTranspose (conjTranspose (swapAt a b * collective pauliX a b)) := by
        rw [conjTranspose_conjTranspose]
    _ = conjTranspose (collective pauliX a b) := by rw [h1]
    _ = collective pauliX a b := collectiveX_conjTranspose a b

lemma swapAt_mul_collectiveZ {n : ℕ} (a b : Fin n) :
    swapAt a b * collective pauliZ a b = collective pauliZ a b := by
  have h1 : conjTranspose (swapAt a b * collective pauliZ a b) = collective pauliZ a b := by
    rw [conjTranspose_mul, swapAt_conjTranspose, collectiveZ_conjTranspose,
      collectiveZ_mul_swapAt]
  calc swapAt a b * collective pauliZ a b
      = conjTranspose (conjTranspose (swapAt a b * collective pauliZ a b)) := by
        rw [conjTranspose_conjTranspose]
    _ = conjTranspose (collective pauliZ a b) := by rw [h1]
    _ = collective pauliZ a b := collectiveZ_conjTranspose a b

lemma singletQ_collectiveX {n : ℕ} (a b : Fin n) :
    collective pauliX a b * singletQ a b = 0 ∧
    singletQ a b * collective pauliX a b = 0 := by
  rw [singletQ_eq]
  constructor
  · rw [mul_smul_comm, mul_sub, mul_one, collectiveX_mul_swapAt, sub_self, smul_zero]
  · rw [smul_mul_assoc, sub_mul, one_mul, swapAt_mul_collectiveX, sub_self, smul_zero]

lemma singletQ_collectiveZ {n : ℕ} (a b : Fin n) :
    collective pauliZ a b * singletQ a b = 0 ∧
    singletQ a b * collective pauliZ a b = 0 := by
  rw [singletQ_eq]
  constructor
  · rw [mul_smul_comm, mul_sub, mul_one, collectiveZ_mul_swapAt, sub_self, smul_zero]
  · rw [smul_mul_assoc, sub_mul, one_mul, swapAt_mul_collectiveZ, sub_self, smul_zero]

lemma singletQ_isOrth {n : ℕ} (a b : Fin n) : IsOrthProj (singletQ a b) := by
  rw [singletQ_eq]
  show IsHerm ((2:ℂ)⁻¹ • (1 - swapAt a b)) ∧ IsProj ((2:ℂ)⁻¹ • (1 - swapAt a b))
  rw [IsHerm, IsProj]
  constructor
  · rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_one, swapAt_conjTranspose]
    simp
  · rw [smul_mul_smul]
    have hmid : (1 - swapAt a b) * (1 - swapAt a b) = (2 : ℂ) • (1 - swapAt a b) := by
      have h : (1 - swapAt a b) * (1 - swapAt a b)
          = 1 - swapAt a b - swapAt a b + swapAt a b * swapAt a b := by
        simp only [sub_mul, mul_sub, mul_one, one_mul]
        abel
      rw [h, swapAt_mul_swapAt, two_smul]
      abel
    rw [hmid, smul_smul]
    field_simp

/-! ## Disjoint supports -/

lemma swapBasis_comm {n : ℕ} (a b c d : Fin n) (y : QubitBasis n)
    (hd : a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d) :
    swapBasis a b (swapBasis c d y) = swapBasis c d (swapBasis a b y) := by
  by_cases hab : a = b
  · subst hab
    rw [swapBasis_self, swapBasis_self]
  by_cases hcd : c = d
  · subst hcd
    rw [swapBasis_self, swapBasis_self]
  funext w
  by_cases hwa : w = a
  · rw [hwa]
    rw [swapBasis_a a b (swapBasis c d y) hab,
      swapBasis_other c d y b hd.2.2.1 hd.2.2.2,
      swapBasis_other c d (swapBasis a b y) a hd.1 hd.2.1,
      swapBasis_a a b y hab]
  · by_cases hwb : w = b
    · rw [hwb]
      rw [swapBasis_b a b (swapBasis c d y) hab,
        swapBasis_other c d y a hd.1 hd.2.1,
        swapBasis_other c d (swapBasis a b y) b hd.2.2.1 hd.2.2.2,
        swapBasis_b a b y hab]
    · by_cases hwc : w = c
      · rw [hwc]
        rw [swapBasis_other a b (swapBasis c d y) c (Ne.symm hd.1) (Ne.symm hd.2.2.1),
          swapBasis_a c d y hcd,
          swapBasis_a c d (swapBasis a b y) hcd,
          swapBasis_other a b y d (Ne.symm hd.2.1) (Ne.symm hd.2.2.2)]
      · by_cases hwd : w = d
        · rw [hwd]
          rw [swapBasis_other a b (swapBasis c d y) d (Ne.symm hd.2.1) (Ne.symm hd.2.2.2),
            swapBasis_b c d y hcd,
            swapBasis_b c d (swapBasis a b y) hcd,
            swapBasis_other a b y c (Ne.symm hd.1) (Ne.symm hd.2.2.1)]
        · rw [swapBasis_other a b _ w hwa hwb,
            swapBasis_other c d y w hwc hwd,
            swapBasis_other c d _ w hwc hwd,
            swapBasis_other a b y w hwa hwb]

lemma swapAt_mul_swapAt_comm_ite {n : ℕ} (a b c d : Fin n) (x y : QubitBasis n) :
    (∑ z : QubitBasis n,
        (if x = swapBasis a b z then (1 : ℂ) else 0) *
          (if z = swapBasis c d y then (1 : ℂ) else 0)) =
      if x = swapBasis a b (swapBasis c d y) then (1 : ℂ) else 0 := by
  rw [Fintype.sum_eq_single (swapBasis c d y)]
  · have h1 : (if swapBasis c d y = swapBasis c d y then (1 : ℂ) else 0) = 1 := if_pos rfl
    rw [h1, mul_one]
  · intro z hz
    have h1 : (if z = swapBasis c d y then (1 : ℂ) else 0) = 0 := if_neg hz
    rw [h1, mul_zero]

lemma swapAt_comm_swapAt {n : ℕ} (a b c d : Fin n)
    (hd : a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d) :
    swapAt a b * swapAt c d = swapAt c d * swapAt a b := by
  apply Matrix.ext
  intro x y
  simp only [Matrix.mul_apply, swapAt]
  rw [swapAt_mul_swapAt_comm_ite a b c d x y,
    swapAt_mul_swapAt_comm_ite c d a b x y,
    swapBasis_comm a b c d y hd]

lemma singletQ_comm_singletQ {n : ℕ} (a b c d : Fin n)
    (hd : a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d) :
    singletQ a b * singletQ c d = singletQ c d * singletQ a b := by
  rw [singletQ_eq, singletQ_eq, smul_mul_smul, smul_mul_smul]
  have h1 : swapAt a b * swapAt c d = swapAt c d * swapAt a b :=
    swapAt_comm_swapAt a b c d hd
  have h : (1 - swapAt a b) * (1 - swapAt c d)
      = (1 - swapAt c d) * (1 - swapAt a b) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one]
    rw [h1]
    abel
  rw [h]

lemma swapAt_comm_embed {n : ℕ} (A : Op1) (a b v : Fin n)
    (hva : v ≠ a) (hvb : v ≠ b) :
    swapAt a b * embed A v = embed A v * swapAt a b := by
  by_cases hab : a = b
  · subst hab; rw [swapAt_self, one_mul, mul_one]
  · apply Matrix.ext
    intro x y
    simp only [Matrix.mul_apply, swapAt, embed]
    have hl :
        (∑ z : QubitBasis n,
            (if x = swapBasis a b z then (1 : ℂ) else 0) *
              (if ∀ w, w ≠ v → z w = y w then A (z v) (y v) else 0)) =
          (if ∀ w, w ≠ v → swapBasis a b x w = y w
            then A (swapBasis a b x v) (y v) else 0) := by
      rw [Fintype.sum_eq_single (swapBasis a b x)]
      · have h1 : (if x = swapBasis a b (swapBasis a b x) then (1:ℂ) else 0) = 1 :=
          if_pos (swapBasis_involutive a b x).symm
        rw [h1, one_mul]
      · intro z hz
        have hne : ¬ x = swapBasis a b z := by
          intro heq
          apply hz
          have : swapBasis a b x = swapBasis a b (swapBasis a b z) := by rw [heq]
          have : swapBasis a b x = z := by
            rwa [swapBasis_involutive] at this
          exact this.symm
        simp [hne]
    have hr :
        (∑ z : QubitBasis n,
            (if ∀ w, w ≠ v → x w = z w then A (x v) (z v) else 0) *
              (if z = swapBasis a b y then (1 : ℂ) else 0)) =
          (if ∀ w, w ≠ v → x w = swapBasis a b y w
            then A (x v) (swapBasis a b y v) else 0) := by
      rw [Fintype.sum_eq_single (swapBasis a b y)]
      · simp
      · intro z hz; simp [hz]
    rw [hl, hr]
    have hval : swapBasis a b x v = x v := swapBasis_other a b x v hva hvb
    have hval2 : swapBasis a b y v = y v := swapBasis_other a b y v hva hvb
    have hcond : (∀ w, w ≠ v → swapBasis a b x w = y w) ↔
        (∀ w, w ≠ v → x w = swapBasis a b y w) := by
      constructor
      · intro h w hw
        rw [swapBasis_apply a b y w]
        by_cases hwa : w = a
        · rw [hwa]
          have hb := h b (Ne.symm hvb)
          rw [swapBasis_apply a b x b, if_neg (Ne.symm hab), if_pos rfl] at hb
          rw [if_pos rfl]
          exact hb
        · by_cases hwb : w = b
          · rw [hwb]
            have ha := h a (Ne.symm hva)
            rw [swapBasis_apply a b x a, if_pos rfl] at ha
            rw [if_neg (Ne.symm hab), if_pos rfl]
            exact ha
          · rw [if_neg hwa, if_neg hwb]
            have hoff := h w hw
            rw [swapBasis_apply a b x w, if_neg hwa, if_neg hwb] at hoff
            exact hoff
      · intro h w hw
        rw [swapBasis_apply a b x w]
        by_cases hwa : w = a
        · rw [hwa]
          have hb := h b (Ne.symm hvb)
          rw [swapBasis_apply a b y b, if_neg (Ne.symm hab), if_pos rfl] at hb
          rw [if_pos rfl]
          exact hb
        · by_cases hwb : w = b
          · rw [hwb]
            have ha := h a (Ne.symm hva)
            rw [swapBasis_apply a b y a, if_pos rfl] at ha
            rw [if_neg (Ne.symm hab), if_pos rfl]
            exact ha
          · rw [if_neg hwa, if_neg hwb]
            have hoff := h w hw
            rw [swapBasis_apply a b y w, if_neg hwa, if_neg hwb] at hoff
            exact hoff
    have hcond' : (∀ w, w ≠ v → swapBasis a b x w = y w)
        = (∀ w, w ≠ v → x w = swapBasis a b y w) := propext hcond
    simp only [hcond', hval, hval2]

lemma singletQ_comm_embed {n : ℕ} (A : Op1) (a b v : Fin n)
    (hva : v ≠ a) (hvb : v ≠ b) :
    singletQ a b * embed A v = embed A v * singletQ a b := by
  rw [singletQ_eq, smul_mul_assoc, mul_smul_comm]
  congr 1
  rw [sub_mul, mul_sub, one_mul, mul_one, swapAt_comm_embed A a b v hva hvb]

end Paper13
