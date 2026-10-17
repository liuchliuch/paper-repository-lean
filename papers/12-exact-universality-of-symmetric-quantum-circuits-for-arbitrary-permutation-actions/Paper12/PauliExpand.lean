import Paper12.Qubit

/-!
# Pauli expansion and orbit-constant coefficients (Lemma 2.3)

Orthogonality of the phase-free Hermitian Pauli basis gives
`U = ∑_P α_P P` with `α_P = 2^{-n} Tr(P U)`.  Equivariance forces the
coefficients to be constant on `Γ`-orbits, and unitarity gives
`∑_P |α_P|² = 1`.
-/

noncomputable section

namespace Paper12

open Matrix Complex

/-- Absolute value of a complex number, as the Euclidean norm (the paper's `|z|`). -/
noncomputable def Complex.abs (z : ℂ) : ℝ := ‖z‖

@[simp] theorem Complex.abs_nonneg (z : ℂ) : 0 ≤ Complex.abs z := norm_nonneg z

theorem Complex.abs_mul (z w : ℂ) : Complex.abs (z * w) = Complex.abs z * Complex.abs w :=
  norm_mul z w

@[simp] theorem Complex.abs_one : Complex.abs (1 : ℂ) = 1 := norm_one

@[simp] theorem Complex.abs_zero : Complex.abs (0 : ℂ) = 0 := norm_zero

@[simp] theorem Complex.abs_natCast (n : ℕ) : Complex.abs (n : ℂ) = n := by
  simp [Complex.abs]

theorem Complex.abs_two : Complex.abs (2 : ℂ) = 2 := Complex.abs_natCast 2

theorem Complex.abs_ofReal (x : ℝ) : Complex.abs (x : ℂ) = |x| := by
  have hnn : 0 ≤ ‖(x : ℂ)‖ := norm_nonneg _
  have hsq : ‖(x : ℂ)‖ ^ 2 = x * x := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
  calc ‖(x : ℂ)‖ = Real.sqrt (‖(x : ℂ)‖ ^ 2) := (Real.sqrt_sq hnn).symm
    _ = Real.sqrt (x * x) := by rw [hsq]
    _ = Real.sqrt (x ^ 2) := by rw [sq]
    _ = |x| := Real.sqrt_sq_eq_abs x

theorem Complex.abs_sq (z : ℂ) : Complex.abs z ^ 2 = Complex.normSq z :=
  (Complex.normSq_eq_norm_sq z).symm

theorem Complex.abs_pow (z : ℂ) (n : ℕ) : Complex.abs (z ^ n) = Complex.abs z ^ n :=
  norm_pow z n

theorem Complex.abs_zpow (z : ℂ) (n : ℤ) : Complex.abs (z ^ n) = Complex.abs z ^ n :=
  norm_zpow z n

theorem Complex.abs_star (z : ℂ) : Complex.abs (starRingEnd ℂ z) = Complex.abs z := norm_star z

variable {X : Type*} [Fintype X]

local instance : DecidableEq X := Classical.decEq _

/-- Pauli coefficient `α_P = 2^{-n} Tr(P U)`. -/
def pauliCoeff (U : Op X) (w : PWord X) : ℂ :=
  (2 : ℂ) ^ (-Fintype.card X : ℤ) * Matrix.trace (pop X w * U)

/-- The support of a coefficient function. -/
def coeffSupport (α : Coeffs X) : Finset (PWord X) :=
  (Finset.univ : Finset (PWord X)).filter (fun w => α w ≠ 0)

/-- Number of nonzero Pauli coefficients `M = |J|`. -/
def coeffCard (α : Coeffs X) : ℕ := (coeffSupport α).card

/-- The `ℓ¹` mass `λ = ∑_{P ∈ J} |α_P|`. -/
def coeffMass (α : Coeffs X) : ℝ :=
  ∑ w ∈ coeffSupport α, Complex.abs (α w)

/-- Expansion of `U` in the Pauli basis. -/
def pauliExpand (U : Op X) : Op X :=
  ∑ w : PWord X, pauliCoeff U w • pop X w

/-! ### Finite sums over function spaces -/

theorem sum_fn_prod {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (h : α → β → ℂ) : ∑ f : α → β, ∏ x, h x (f x) = ∏ x, ∑ y, h x y :=
  (Fintype.prod_sum h).symm

theorem sum_fn2_prod {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (g : α → β → β → ℂ) :
    ∑ (b : α → β), ∑ (c : α → β), ∏ x, g x (b x) (c x) = ∏ x, ∑ i : β, ∑ j : β, g x i j := by
  have h1 : ∀ b : α → β, ∑ c : α → β, ∏ x, g x (b x) (c x) = ∏ x, ∑ j, g x (b x) j := by
    intro b
    exact (Fintype.prod_sum (fun x j => g x (b x) j)).symm
  simp_rw [h1]
  exact (Fintype.prod_sum (fun x i => ∑ j, g x i j)).symm

/-! ### One-qubit Pauli orthogonality -/

lemma sum_psym (f : PSym → ℂ) : ∑ s, f s = f .I + f .X + f .Y + f .Z := by
  have h : (Finset.univ : Finset PSym) = {.I, .X, .Y, .Z} := by
    ext s; cases s <;> simp
  rw [h, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  · ring
  all_goals decide

theorem sum_pmat_mul_entry (i j c d : Fin 2) :
    ∑ s : PSym, pmat s i j * pmat s c d = if i = d ∧ j = c then (2 : ℂ) else 0 := by
  rw [sum_psym]
  fin_cases i <;> fin_cases j <;> fin_cases c <;> fin_cases d
    <;> simp [pmat, Complex.I_mul_I]
    <;> norm_num

theorem trace_pmat_mul_pmat : ∀ a b : PSym,
    Matrix.trace (pmat a * pmat b) = if a = b then (2 : ℂ) else 0
  | .I, .I => by simp [pmat]
  | .I, .X => by
      rw [if_neg (by decide)]
      show Matrix.trace ((1 : Matrix (Fin 2) (Fin 2) ℂ) * pmat .X) = 0
      rw [Matrix.one_mul, Matrix.trace_fin_two]; simp [pmat]
  | .I, .Y => by
      rw [if_neg (by decide)]
      show Matrix.trace ((1 : Matrix (Fin 2) (Fin 2) ℂ) * pmat .Y) = 0
      rw [Matrix.one_mul, Matrix.trace_fin_two]; simp [pmat]
  | .I, .Z => by
      rw [if_neg (by decide)]
      show Matrix.trace ((1 : Matrix (Fin 2) (Fin 2) ℂ) * pmat .Z) = 0
      rw [Matrix.one_mul, Matrix.trace_fin_two]; simp [pmat]
  | .X, .I => by
      rw [if_neg (by decide)]
      show Matrix.trace (pmat .X * (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 0
      rw [Matrix.mul_one, Matrix.trace_fin_two]; simp [pmat]
  | .X, .X => by
      rw [if_pos rfl]
      show Matrix.trace ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![0, 1; 1, 0]) = 2
      rw [Matrix.mul_fin_two, Matrix.trace_fin_two]; norm_num
  | .X, .Y => by
      rw [if_neg (by decide)]
      show Matrix.trace ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![0, -I; I, 0]) = 0
      rw [Matrix.mul_fin_two, Matrix.trace_fin_two]; norm_num [Complex.I_mul_I]
  | .X, .Z => by
      rw [if_neg (by decide)]
      show Matrix.trace ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![1, 0; 0, -1]) = 0
      rw [Matrix.mul_fin_two, Matrix.trace_fin_two]; norm_num
  | .Y, .I => by
      rw [if_neg (by decide)]
      show Matrix.trace (pmat .Y * (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 0
      rw [Matrix.mul_one, Matrix.trace_fin_two]; simp [pmat]
  | .Y, .X => by
      rw [if_neg (by decide)]
      show Matrix.trace ((!![0, -I; I, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![0, 1; 1, 0]) = 0
      rw [Matrix.mul_fin_two, Matrix.trace_fin_two]; norm_num [Complex.I_mul_I]
  | .Y, .Y => by
      rw [if_pos rfl]
      show Matrix.trace ((!![0, -I; I, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![0, -I; I, 0]) = 2
      rw [Matrix.mul_fin_two, Matrix.trace_fin_two]; norm_num [Complex.I_mul_I]
  | .Y, .Z => by
      rw [if_neg (by decide)]
      show Matrix.trace ((!![0, -I; I, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![1, 0; 0, -1]) = 0
      rw [Matrix.mul_fin_two, Matrix.trace_fin_two]; norm_num [Complex.I_mul_I]
  | .Z, .I => by
      rw [if_neg (by decide)]
      show Matrix.trace (pmat .Z * (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 0
      rw [Matrix.mul_one, Matrix.trace_fin_two]; simp [pmat]
  | .Z, .X => by
      rw [if_neg (by decide)]
      show Matrix.trace ((!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) * !![0, 1; 1, 0]) = 0
      rw [Matrix.mul_fin_two, Matrix.trace_fin_two]; norm_num
  | .Z, .Y => by
      rw [if_neg (by decide)]
      show Matrix.trace ((!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) * !![0, -I; I, 0]) = 0
      rw [Matrix.mul_fin_two, Matrix.trace_fin_two]; norm_num [Complex.I_mul_I]
  | .Z, .Z => by
      rw [if_pos rfl]
      show Matrix.trace ((!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) * !![1, 0; 0, -1]) = 2
      rw [Matrix.mul_fin_two, Matrix.trace_fin_two]; norm_num

/-! ### Pauli word identities -/

theorem pop_hermitian (w : PWord X) : (pop X w)ᴴ = pop X w := by
  ext i j
  rw [Matrix.conjTranspose_apply, pop_apply, pop_apply]
  have h : ∀ x : X, starRingEnd ℂ (pmat (w x) (j x) (i x)) = pmat (w x) (i x) (j x) := by
    intro x
    have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M (i x) (j x))
      (pmat_hermitian (w x))
    simpa [Matrix.conjTranspose_apply] using hh
  show starRingEnd ℂ (∏ x, pmat (w x) (j x) (i x)) = ∏ x, pmat (w x) (i x) (j x)
  rw [map_prod]
  exact Finset.prod_congr rfl (fun x _ => h x)

theorem trace_pop_mul_pop (v w : PWord X) :
    Matrix.trace (pop X v * pop X w) = if v = w then (2 : ℂ) ^ Fintype.card X else 0 := by
  have htrace : Matrix.trace (pop X v * pop X w)
      = ∑ b : Basis X, ∑ c : Basis X, ∏ x, pmat (v x) (b x) (c x) * pmat (w x) (c x) (b x) := by
    rw [Matrix.trace]
    simp only [Matrix.diag_apply, Matrix.mul_apply, pop_apply]
    congr 1
    funext b
    rw [Finset.sum_congr rfl]
    intro c _
    rw [Finset.prod_mul_distrib]
  have hfn : (∑ b : Basis X, ∑ c : Basis X, ∏ x, pmat (v x) (b x) (c x) * pmat (w x) (c x) (b x))
      = ∏ x : X, ∑ i : Fin 2, ∑ j : Fin 2, pmat (v x) i j * pmat (w x) j i :=
    sum_fn2_prod (fun (x : X) (i j : Fin 2) => pmat (v x) i j * pmat (w x) j i)
  rw [htrace, hfn]
  have hfac : ∀ x : X, (∑ i : Fin 2, ∑ j : Fin 2, pmat (v x) i j * pmat (w x) j i)
      = Matrix.trace (pmat (v x) * pmat (w x)) := by
    intro x
    rw [Matrix.trace_fin_two, Matrix.mul_apply, Matrix.mul_apply]
    simp only [Fin.sum_univ_two]
  have he : (fun x : X => ∑ i : Fin 2, ∑ j : Fin 2, pmat (v x) i j * pmat (w x) j i)
      = fun x : X => if v x = w x then (2 : ℂ) else 0 := by
    funext x
    rw [hfac x, trace_pmat_mul_pmat]
  rw [he]
  by_cases h : v = w
  · subst h
    rw [if_pos rfl]
    have h2 : (∏ x : X, (if v x = v x then (2 : ℂ) else 0)) = (2 : ℂ) ^ Fintype.card X := by
      have he : (fun x : X => if v x = v x then (2 : ℂ) else 0) = fun _ => (2 : ℂ) := by
        funext x
        exact if_pos rfl
      rw [he, Finset.prod_const, Finset.card_univ]
    rw [h2]
  · obtain ⟨x, hx⟩ := Function.ne_iff.mp h
    rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ x) (if_neg hx)

theorem sum_pop_entry (i j c d : Basis X) :
    ∑ w : PWord X, pop X w i j * pop X w c d
      = if i = d ∧ j = c then (2 : ℂ) ^ Fintype.card X else 0 := by
  have h : ∀ w : PWord X, pop X w i j * pop X w c d
      = ∏ x, pmat (w x) (i x) (j x) * pmat (w x) (c x) (d x) := by
    intro w
    rw [pop_apply, pop_apply, Finset.prod_mul_distrib]
  simp_rw [h]
  have hfn : (∑ w : PWord X, ∏ x, pmat (w x) (i x) (j x) * pmat (w x) (c x) (d x))
      = ∏ x : X, ∑ s : PSym, pmat s (i x) (j x) * pmat s (c x) (d x) :=
    sum_fn_prod (fun x s => pmat s (i x) (j x) * pmat s (c x) (d x))
  rw [hfn]
  have h2 : ∀ x : X, (∑ s : PSym, pmat s (i x) (j x) * pmat s (c x) (d x))
      = if i x = d x ∧ j x = c x then (2 : ℂ) else 0 := fun x =>
    sum_pmat_mul_entry (i x) (j x) (c x) (d x)
  simp_rw [h2]
  by_cases hij : i = d ∧ j = c
  · obtain ⟨hi, hj⟩ := hij
    subst hi
    subst hj
    rw [if_pos ⟨rfl, rfl⟩]
    simp
  · rw [if_neg hij]
    by_cases h1 : i = d
    · have hne : j ≠ c := fun hh => hij ⟨h1, hh⟩
      obtain ⟨x, hx⟩ := Function.ne_iff.mp hne
      refine Finset.prod_eq_zero (Finset.mem_univ x) ?_
      exact if_neg (fun ⟨_, h3⟩ => hx h3)
    · obtain ⟨x, hx⟩ := Function.ne_iff.mp h1
      refine Finset.prod_eq_zero (Finset.mem_univ x) ?_
      exact if_neg (fun ⟨h3, _⟩ => hx h3)

theorem R_conj_apply (γ : X ≃ X) (A : Op X) (i j : Basis X) :
    (R γ * A * (R γ)ᴴ) i j = A (i ∘ γ) (j ∘ γ) := by
  simp only [Matrix.mul_apply]
  have hR : ∀ a b : Basis X, R γ a b = if permBasis γ b = a then (1 : ℂ) else 0 := fun _ _ => rfl
  have hRad : ∀ a b : Basis X, (R γ)ᴴ a b = if permBasis γ a = b then (1 : ℂ) else 0 :=
    R_adj_apply γ
  simp only [hR, hRad]
  have hpe : ∀ a b : Basis X, permBasis γ a = b ↔ a = b ∘ γ := by
    intro a b
    constructor
    · intro h
      funext y
      have := congrFun h (γ y)
      simpa [permBasis, Function.comp] using this
    · intro h
      funext x
      subst h
      simp [permBasis, Function.comp]
  rw [Finset.sum_eq_single (j ∘ γ)]
  · rw [if_pos ((hpe _ _).2 rfl), mul_one]
    rw [Finset.sum_eq_single (i ∘ γ)]
    · rw [if_pos ((hpe _ _).2 rfl), one_mul]
    · intro k _ hk
      rw [if_neg]
      · simp
      · exact fun hh => hk ((hpe _ _).1 hh)
    · intro hk
      exact absurd (Finset.mem_univ (i ∘ γ)) hk
  · intro k _ hk
    rw [if_neg]
    · simp
    · exact fun hh => hk ((hpe _ _).1 hh)
  · intro hk
    exact absurd (Finset.mem_univ (j ∘ γ)) hk

theorem R_pop_conj (γ : X ≃ X) (w : PWord X) :
    pop X (actWord γ w) = R γ * pop X w * (R γ)ᴴ := by
  ext i j
  rw [R_conj_apply]
  simp only [pop_apply, actWord_apply]
  have hprod : (∏ x, pmat (w (γ.symm x)) (i x) (j x))
      = ∏ x, pmat (w x) (i (γ x)) (j (γ x)) := by
    have key := Equiv.prod_comp γ.symm
      (fun y : X => pmat (w y) (i (γ y)) (j (γ y)))
    have heq : ∀ x : X, pmat (w (γ.symm x)) (i x) (j x)
        = pmat (w (γ.symm x)) (i (γ (γ.symm x))) (j (γ (γ.symm x))) := fun x => by
      simp only [Equiv.apply_symm_apply]
    have hrew : (∏ x : X, pmat (w (γ.symm x)) (i x) (j x))
        = ∏ x : X, pmat (w (γ.symm x)) (i (γ (γ.symm x))) (j (γ (γ.symm x))) :=
      Finset.prod_congr rfl (fun x _ => heq x)
    rw [hrew]
    exact key
  exact hprod

/-- Coefficient of an orbit-equal function is constant along the action. -/
theorem coeff_orbit {γ : X ≃ X} {U : Op X} (h : U * R γ = R γ * U) (w : PWord X) :
    pauliCoeff U (actWord γ w) = pauliCoeff U w := by
  have hpop := R_pop_conj γ w
  have hcomm : R γ * U = U * R γ := h.symm
  have hRd : (R γ)ᴴ * U = U * (R γ)ᴴ := by
    have h1 : U = R γ * U * (R γ)ᴴ := by
      have h2 : R γ * U * (R γ)ᴴ = U := by
        calc R γ * U * (R γ)ᴴ = U * R γ * (R γ)ᴴ := by rw [hcomm]
          _ = U * (R γ * (R γ)ᴴ) := by ac_rfl
          _ = U * 1 := congrArg (fun z => U * z) (R_mul_adj γ)
          _ = U := Matrix.mul_one _
      exact h2.symm
    calc (R γ)ᴴ * U = (R γ)ᴴ * (R γ * U * (R γ)ᴴ) := by rw [← h1]
      _ = ((R γ)ᴴ * R γ) * U * (R γ)ᴴ := by ac_rfl
      _ = U * (R γ)ᴴ := by rw [R_unitary, Matrix.one_mul]
  have htrace : Matrix.trace (pop X (actWord γ w) * U) = Matrix.trace (pop X w * U) := by
    rw [hpop]
    have e1 : R γ * pop X w * (R γ)ᴴ * U = R γ * pop X w * ((R γ)ᴴ * U) := by ac_rfl
    rw [e1, hRd]
    have e2 : R γ * pop X w * (U * (R γ)ᴴ) = R γ * (pop X w * U) * (R γ)ᴴ := by ac_rfl
    rw [e2]
    have e3 : Matrix.trace (R γ * (pop X w * U) * (R γ)ᴴ)
        = Matrix.trace ((R γ)ᴴ * R γ * (pop X w * U)) := Matrix.trace_mul_cycle _ _ _
    rw [e3]; rw [R_unitary, Matrix.one_mul]
  unfold pauliCoeff
  rw [htrace]

/-! ### Parseval identity -/

theorem unitary_mul_adj {n : Type*} [Fintype n] [DecidableEq n] (U : Matrix n n ℂ)
    (hU : Uᴴ * U = 1) : U * Uᴴ = 1 := Matrix.mul_eq_one_comm.mp hU

/-- Reconstruction: `∑_P Tr(P U) P = 2^n U`. -/
theorem pauli_reconstruct (U : Op X) (i j : Basis X) :
    ∑ w : PWord X, Matrix.trace (pop X w * U) * pop X w i j
      = (2 : ℂ) ^ Fintype.card X * U i j := by
  have htr : ∀ w : PWord X, Matrix.trace (pop X w * U)
      = ∑ c : Basis X, ∑ d : Basis X, pop X w c d * U d c := by
    intro w
    rw [Matrix.trace]
    simp only [Matrix.diag_apply, Matrix.mul_apply]
  simp_rw [htr, Finset.sum_mul]
  have key : ∀ (w : PWord X) (c d : Basis X),
      pop X w c d * U d c * pop X w i j = U d c * (pop X w c d * pop X w i j) := by
    intros; ring
  simp_rw [key]
  have hswap : (∑ w : PWord X, ∑ c : Basis X, ∑ d : Basis X,
      U d c * (pop X w c d * pop X w i j))
      = (∑ c : Basis X, ∑ d : Basis X, U d c * (∑ w : PWord X, pop X w c d * pop X w i j)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro c _
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro d _
    rw [← Finset.mul_sum]
  rw [hswap]
  simp_rw [sum_pop_entry]
  rw [Finset.sum_eq_single j]
  · rw [Finset.sum_eq_single i]
    · rw [if_pos ⟨rfl, rfl⟩, mul_comm]
    · intro d _ hd
      rw [if_neg (fun h => hd h.2), mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  · intro c _ hc
    rw [Finset.sum_eq_zero]
    intro d _
    rw [if_neg (fun h => hc h.1), mul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem pauli_reconstruct_op (U : Op X) :
    ∑ w : PWord X, Matrix.trace (pop X w * U) • pop X w
      = ((2 : ℂ) ^ Fintype.card X) • U := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  exact pauli_reconstruct U i j

/-- Equation (4), with the actual trace-defined Pauli coefficients. -/
theorem pauliExpand_eq (U : Op X) : pauliExpand U = U := by
  unfold pauliExpand pauliCoeff
  simp_rw [MulAction.mul_smul]
  rw [← Finset.smul_sum, pauli_reconstruct_op, smul_smul]
  rw [_root_.zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0)), one_smul]

theorem selector_support_orbit {γ : X ≃ X} {U : Op X}
    (h : U * R γ = R γ * U) (w : PWord X) :
    actWord γ w ∈ coeffSupport (pauliCoeff U) ↔ w ∈ coeffSupport (pauliCoeff U) := by
  simp only [coeffSupport, Finset.mem_filter, Finset.mem_univ, true_and, coeff_orbit h]

theorem sum_trace_mul_conj (U : Op X) (hU : Uᴴ * U = 1) :
    ∑ w : PWord X, (Matrix.trace (pop X w * U))
        * starRingEnd ℂ (Matrix.trace (pop X w * U))
      = (4 : ℂ) ^ Fintype.card X := by
  have hconj : ∀ w : PWord X,
      starRingEnd ℂ (Matrix.trace (pop X w * U)) = Matrix.trace (Uᴴ * pop X w) := by
    intro w
    show star (Matrix.trace (pop X w * U)) = Matrix.trace (Uᴴ * pop X w)
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, pop_hermitian]
  simp_rw [hconj]
  have hlin : (∑ w : PWord X, (Matrix.trace (pop X w * U)) * Matrix.trace (Uᴴ * pop X w))
      = Matrix.trace (Uᴴ * (∑ w : PWord X, Matrix.trace (pop X w * U) • pop X w)) := by
    rw [Matrix.mul_sum (Finset.univ) (fun w : PWord X => Matrix.trace (pop X w * U) • pop X w) Uᴴ]
    rw [Matrix.trace_sum]
    congr 1
    funext w
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  rw [hlin, pauli_reconstruct_op]
  have hsmul : Uᴴ * (((2 : ℂ) ^ Fintype.card X) • U)
      = ((2 : ℂ) ^ Fintype.card X) • (Uᴴ * U) := by
    rw [Matrix.mul_smul]
  rw [hsmul, hU, Matrix.trace_smul, Matrix.trace_one]
  have hcard : Fintype.card (Basis X) = 2 ^ Fintype.card X := by
    rw [Fintype.card_fun, Fintype.card_fin]
  rw [hcard]
  push_cast
  rw [smul_eq_mul, ← mul_pow]
  norm_num

theorem coeffMass_eq_sum (α : Coeffs X) :
    coeffMass α = ∑ w : PWord X, Complex.abs (α w) := by
  unfold coeffMass coeffSupport
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro w _
  split_ifs with h
  · rfl
  · simp_all

/-- Unitarity implies `∑ |α_P|² = 1`. -/
theorem coeff_l2 (U : Op X) (hU : Uᴴ * U = 1) :
    ∑ w : PWord X, Complex.abs (pauliCoeff U w) ^ 2 = 1 := by
  have hp : ∀ w : PWord X,
      pauliCoeff U w = (2 : ℂ) ^ (-Fintype.card X : ℤ) * Matrix.trace (pop X w * U) :=
    fun _ => rfl
  have habs : ∀ w : PWord X,
      Complex.abs (pauliCoeff U w) ^ 2
        = ((2 : ℝ) ^ (-Fintype.card X : ℤ)) ^ 2
          * Complex.abs (Matrix.trace (pop X w * U)) ^ 2 := by
    intro w
    rw [hp, Complex.abs_mul, Complex.abs_zpow, Complex.abs_two, mul_pow]
  simp_rw [habs]
  rw [← Finset.mul_sum]
  have hsq : ∀ w : PWord X,
      Complex.abs (Matrix.trace (pop X w * U)) ^ 2
        = Complex.normSq (Matrix.trace (pop X w * U)) := fun w => Complex.abs_sq _
  simp_rw [hsq]
  have hnsq : ∀ w : PWord X,
      Complex.normSq (Matrix.trace (pop X w * U))
        = (Matrix.trace (pop X w * U)
            * starRingEnd ℂ (Matrix.trace (pop X w * U))).re := by
    intro w
    have := Complex.mul_conj (Matrix.trace (pop X w * U))
    rw [this, Complex.ofReal_re]
  simp_rw [hnsq]
  rw [← Complex.re_sum]
  have hsum := sum_trace_mul_conj U hU
  rw [hsum]
  have hreal : ((4 : ℂ) ^ Fintype.card X).re = (4 : ℝ) ^ Fintype.card X := by
    norm_cast
  rw [hreal, _root_.zpow_neg, zpow_natCast, inv_pow]
  have hfour : (4 : ℝ) ^ Fintype.card X = ((2 : ℝ) ^ Fintype.card X) ^ 2 := by
    rw [← pow_mul, mul_comm (Fintype.card X) 2, pow_mul]
    norm_num
  rw [hfour, inv_mul_cancel₀ (by positivity)]

/-- `ℓ¹` mass bounds: `1 ≤ λ ≤ √M`. -/
theorem coeff_mass_bounds (U : Op X) (hU : Uᴴ * U = 1) :
    1 ≤ coeffMass (pauliCoeff U) ∧
      coeffMass (pauliCoeff U) ≤ Real.sqrt (coeffCard (pauliCoeff U)) := by
  have hl2 := coeff_l2 U hU
  have hmass := coeffMass_eq_sum (pauliCoeff U)
  have hnn : ∀ w : PWord X, 0 ≤ Complex.abs (pauliCoeff U w) := fun w =>
    Complex.abs_nonneg _
  have hlow : 1 ≤ coeffMass (pauliCoeff U) := by
    have h1 : ∑ w : PWord X, Complex.abs (pauliCoeff U w) ^ 2
        ≤ (coeffMass (pauliCoeff U)) ^ 2 := by
      rw [hmass]
      exact Finset.sum_sq_le_sq_sum_of_nonneg (fun w _ => hnn w)
    rw [hl2] at h1
    have hmass_nonneg : 0 ≤ coeffMass (pauliCoeff U) := by
      rw [hmass]
      exact Finset.sum_nonneg (fun w _ => hnn w)
    nlinarith
  have hup : coeffMass (pauliCoeff U) ≤ Real.sqrt (coeffCard (pauliCoeff U)) := by
    have h1 : (coeffMass (pauliCoeff U)) ^ 2
        ≤ (coeffCard (pauliCoeff U) : ℝ) * 1 := by
      have h2 := sq_sum_le_card_mul_sum_sq
        (s := coeffSupport (pauliCoeff U)) (f := fun w => Complex.abs (pauliCoeff U w))
      -- (∑_{supp} |α|)^2 ≤ |supp| * ∑_{supp} |α|^2
      have h3 : (∑ w ∈ coeffSupport (pauliCoeff U), Complex.abs (pauliCoeff U w) ^ 2)
          = ∑ w : PWord X, Complex.abs (pauliCoeff U w) ^ 2 := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro w _ hn
        simp only [coeffSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hn
        simp [not_not.mp hn]
      rw [h3, hl2] at h2
      push_cast at h2
      simpa using h2
    have hmass_nonneg : 0 ≤ coeffMass (pauliCoeff U) := by
      rw [hmass]
      exact Finset.sum_nonneg (fun w _ => hnn w)
    have hM : 0 ≤ (coeffCard (pauliCoeff U) : ℝ) := by positivity
    exact (Real.le_sqrt hmass_nonneg hM).mpr (by simpa using h1)
  exact ⟨hlow, hup⟩

/-- Selector amplitude `d_P = √(|α_P| / λ)`. -/
def selectorAmp (α : Coeffs X) (w : PWord X) : ℝ :=
  Real.sqrt (Complex.abs (α w) / coeffMass α)

/-- Phase `ω_P = α_P / |α_P|` on the support. -/
def selectorPhase (α : Coeffs X) (w : PWord X) : ℂ :=
  if α w = 0 then 1 else (α w) / Complex.abs (α w)

/-- Sum of squared selector amplitudes is `1`. -/
theorem selector_amp_sq (α : Coeffs X)
    (h : 0 < coeffMass α) :
    ∑ w ∈ coeffSupport α, (selectorAmp α w) ^ 2 = 1 := by
  have hnn : ∀ w, 0 ≤ Complex.abs (α w) / coeffMass α := fun w =>
    div_nonneg (Complex.abs_nonneg _) (le_of_lt h)
  have h2 : ∀ w ∈ coeffSupport α, (selectorAmp α w) ^ 2 = Complex.abs (α w) / coeffMass α := by
    intro w _
    unfold selectorAmp
    exact Real.sq_sqrt (hnn w)
  conv_lhs => rw [Finset.sum_congr rfl (fun w hw => h2 w hw)]
  rw [← Finset.sum_div]
  have : (∑ w ∈ coeffSupport α, Complex.abs (α w)) = coeffMass α := rfl
  rw [this, div_self (ne_of_gt h)]

end Paper12
