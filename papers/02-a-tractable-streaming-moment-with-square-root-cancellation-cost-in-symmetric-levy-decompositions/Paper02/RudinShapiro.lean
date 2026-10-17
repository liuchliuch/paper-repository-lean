import Paper02.Basic

/-!
# Rudin–Shapiro coefficient words and transition counts

Coefficient lists of `P_m`/`Q_m`, lengths, heads, and
`T_m + U_m = 2^m - 1` (Lemma 2.4).
-/

noncomputable section

namespace Paper02.RS

open Paper02

/-- Joint recursion `(coeffs P_m, coeffs Q_m)`. -/
def coeffsPQ : ℕ → List ℝ × List ℝ
  | 0 => ([1], [1])
  | m + 1 =>
    let p := (coeffsPQ m).1
    let q := (coeffsPQ m).2
    (p ++ q, p ++ q.map (fun x => -x))

def coeffsP (m : ℕ) : List ℝ := (coeffsPQ m).1
def coeffsQ (m : ℕ) : List ℝ := (coeffsPQ m).2

lemma coeffsP_succ (m : ℕ) : coeffsP (m + 1) = coeffsP m ++ coeffsQ m := rfl
lemma coeffsQ_succ (m : ℕ) :
    coeffsQ (m + 1) = coeffsP m ++ (coeffsQ m).map (fun x => -x) := rfl

lemma coeffsP_length_and_Q : ∀ m, (coeffsP m).length = 2 ^ m ∧ (coeffsQ m).length = 2 ^ m
  | 0 => by
    show (coeffsPQ 0).1.length = 1 ∧ (coeffsPQ 0).2.length = 1
    exact ⟨rfl, rfl⟩
  | m + 1 => by
    rcases coeffsP_length_and_Q m with ⟨hp, hq⟩
    constructor
    · rw [coeffsP_succ, List.length_append, hp, hq, pow_succ]; ring
    · rw [coeffsQ_succ, List.length_append, List.length_map, hp, hq, pow_succ]; ring

lemma coeffsP_length (m : ℕ) : (coeffsP m).length = 2 ^ m :=
  (coeffsP_length_and_Q m).1

lemma coeffsQ_length (m : ℕ) : (coeffsQ m).length = 2 ^ m :=
  (coeffsP_length_and_Q m).2

lemma coeffsP_one : coeffsP 1 = [1, 1] := rfl
lemma coeffsQ_one : coeffsQ 1 = [1, -1] := rfl

lemma coeffsP_head : ∀ m, (coeffsP m).headD 0 = 1
  | 0 => rfl
  | m + 1 => by
    show ((coeffsP m ++ coeffsQ m)).headD 0 = 1
    cases h : coeffsP m with
    | nil =>
      have := congr_arg List.length h
      rw [coeffsP_length] at this
      simp at this
    | cons a as =>
      have ha : a = 1 := by
        have := coeffsP_head m
        rw [h] at this
        exact this
      show (a :: as ++ coeffsQ m).headD 0 = 1
      rw [ha]
      rfl

lemma coeffsQ_head : ∀ m, (coeffsQ m).headD 0 = 1
  | 0 => rfl
  | m + 1 => by
    show ((coeffsP m ++ (coeffsQ m).map (fun x => -x))).headD 0 = 1
    cases h : coeffsP m with
    | nil =>
      have := congr_arg List.length h
      rw [coeffsP_length] at this
      simp at this
    | cons a as =>
      have ha : a = 1 := by
        have := coeffsP_head m
        rw [h] at this
        exact this
      show (a :: as ++ List.map (fun x => -x) (coeffsQ m)).headD 0 = 1
      rw [ha]
      rfl

/-! ## Transition counts -/

def transitions : List ℝ → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => (if a * b < 0 then 1 else 0) + transitions (b :: rest)

lemma transitions_cons_cons (a b : ℝ) (rest : List ℝ) :
    transitions (a :: b :: rest)
      = (if a * b < 0 then 1 else 0) + transitions (b :: rest) := rfl

lemma transitions_neg : ∀ (u : List ℝ),
    transitions (u.map (fun x => -x)) = transitions u
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by
    have h : (-a) * (-b) = a * b := by ring
    show (if (-a) * (-b) < 0 then 1 else 0)
        + transitions ((b :: rest).map (fun x => -x))
        = (if a * b < 0 then 1 else 0) + transitions (b :: rest)
    rw [h, transitions_neg]

def joinTrans (u v : List ℝ) : ℕ :=
  if u = [] ∨ v = [] then 0
  else if (u.getLastD 0) * (v.headD 0) < 0 then 1 else 0

lemma List.getLastD_eq_default {α : Type} : ∀ (v : List α) (a b : α),
    v ≠ [] → v.getLastD a = v.getLastD b
  | [], _, _, h => absurd rfl h
  | [_], _, _, _ => rfl
  | x :: y :: ys, a, b, _ => by
    have h1 : (x :: y :: ys).getLastD a = (y :: ys).getLastD y := List.getLastD_cons
    have h2 : (x :: y :: ys).getLastD b = (y :: ys).getLastD y := List.getLastD_cons
    rw [h1, h2]

lemma List.getLastD_append_of_ne_nil {α : Type} : ∀ (u v : List α) (d : α),
    v ≠ [] → (u ++ v).getLastD d = v.getLastD d
  | [], v, d, _ => rfl
  | a :: u, v, d, hv => by
    show ((a :: u) ++ v).getLastD d = v.getLastD d
    rw [List.cons_append]
    show (a :: (u ++ v)).getLastD d = _
    rw [List.getLastD_cons]
    have ih := List.getLastD_append_of_ne_nil u v a hv
    rw [ih]
    exact List.getLastD_eq_default v a d hv

lemma List.getLastD_mem {α : Type} : ∀ (u : List α) (d : α), u ≠ [] → u.getLastD d ∈ u
  | [], _, h => absurd rfl h
  | [_], d, _ => by simp
  | a :: b :: bs, d, _ => by
    have h : (a :: b :: bs).getLastD d = (b :: bs).getLastD b := List.getLastD_cons
    rw [h]
    exact List.mem_cons_of_mem _ (List.getLastD_mem (b :: bs) b (List.cons_ne_nil _ _))

lemma coeffs_mem_of_PQ : ∀ m x,
    (x ∈ coeffsP m → x = 1 ∨ x = -1) ∧ (x ∈ coeffsQ m → x = 1 ∨ x = -1)
  | 0, x => by
    constructor
    · intro h
      have : coeffsP 0 = [1] := rfl
      rw [this] at h
      exact Or.inl (by simpa using h)
    · intro h
      have : coeffsQ 0 = [1] := rfl
      rw [this] at h
      exact Or.inl (by simpa using h)
  | m + 1, x => by
    rcases coeffs_mem_of_PQ m x with ⟨hp, hq⟩
    constructor
    · intro h
      rw [coeffsP_succ, List.mem_append] at h
      rcases h with h | h
      · exact hp h
      · exact hq h
    · intro h
      rw [coeffsQ_succ, List.mem_append] at h
      rcases h with h | h
      · exact hp h
      · rw [List.mem_map] at h
        obtain ⟨y, hy, he⟩ := h
        have hxy : x = -y := he.symm
        have hy' : y = 1 ∨ y = -1 := (coeffs_mem_of_PQ m y).2 hy
        rcases hy' with hy' | hy'
        · rw [hxy, hy']; exact Or.inr (by norm_num)
        · rw [hxy, hy']; exact Or.inl (by norm_num)

lemma coeffsP_mem (m : ℕ) {x : ℝ} (hx : x ∈ coeffsP m) : x = 1 ∨ x = -1 :=
  (coeffs_mem_of_PQ m x).1 hx

lemma coeffsP_last_ne_zero (m : ℕ) : (coeffsP m).getLastD 0 ≠ 0 := by
  have hne : coeffsP m ≠ [] := by
    intro h
    have := congr_arg List.length h
    rw [coeffsP_length] at this
    simp at this
  have hin := List.getLastD_mem (coeffsP m) 0 hne
  rcases coeffsP_mem m hin with h | h
  · rw [h]; norm_num
  · rw [h]; norm_num

lemma joinTrans_sum_one (u v : List ℝ) (hu : u ≠ []) (hv : v ≠ [])
    (hne : (u.getLastD 0) * (v.headD 0) ≠ 0) :
    joinTrans u v + joinTrans u (v.map (fun x => -x)) = 1 := by
  have hneM : (v.map (fun x => -x)) ≠ [] := by
    intro h
    have h0 : (v.map (fun x => -x)).length = 0 := by rw [h]; rfl
    rw [List.length_map] at h0
    exact absurd (List.length_pos_of_ne_nil hv) (by omega)
  simp only [joinTrans, hu, hv, hneM, if_false, or_false]
  have hhead : (v.map (fun x => -x)).headD 0 = - v.headD 0 := by
    cases v with
    | nil => exact absurd rfl hv
    | cons a as => simp
  rw [hhead]
  set j := u.getLastD 0
  set w := v.headD 0
  have hne0 : j * w ≠ 0 := hne
  by_cases hj : j * w < 0
  · have h1 : (if j * w < 0 then (1 : ℕ) else 0) = 1 := by simp [hj]
    have h2 : (if j * (-w) < 0 then (1 : ℕ) else 0) = 0 := by
      have : j * (-w) = - (j * w) := by ring
      rw [this]
      have hpos : ¬ (-(j * w) < 0) := by linarith
      simp [hpos]
    rw [h1, h2]
  · have hpos : 0 < j * w := lt_of_le_of_ne (le_of_not_gt hj) (Ne.symm hne0)
    have h1 : (if j * w < 0 then (1 : ℕ) else 0) = 0 := by simp [hj]
    have h2 : (if j * (-w) < 0 then (1 : ℕ) else 0) = 1 := by
      have : j * (-w) = - (j * w) := by ring
      rw [this]
      have hlt : - (j * w) < 0 := by linarith
      simp [hlt]
    rw [h1, h2]

lemma transitions_append : ∀ (u v : List ℝ),
    transitions (u ++ v) = transitions u + transitions v + joinTrans u v
  | [], v => by
    show transitions v = 0 + transitions v + joinTrans [] v
    simp [joinTrans]
  | [a], v => by
    cases v with
    | nil => rfl
    | cons b v' =>
      show transitions (a :: b :: v')
          = 0 + transitions (b :: v') + joinTrans [a] (b :: v')
      rw [transitions_cons_cons]
      have hjoin : joinTrans [a] (b :: v') = if a * b < 0 then 1 else 0 := by
        have hne1 : ([a] : List ℝ) ≠ [] := List.cons_ne_nil _ _
        have hne2 : (b :: v') ≠ [] := List.cons_ne_nil _ _
        simp only [joinTrans, hne1, hne2, if_false, or_false]
        rfl
      rw [hjoin]
      by_cases h : a * b < 0
      · simp [h, Nat.add_comm]
      · simp [h]
  | a :: b :: u', v => by
    have ih := transitions_append (b :: u') v
    have hne1 : (a :: b :: u') ≠ [] := List.cons_ne_nil _ _
    have hne3 : (b :: u') ≠ [] := List.cons_ne_nil _ _
    have hjoinEq : joinTrans (a :: b :: u') v = joinTrans (b :: u') v := by
      cases v with
      | nil => simp [joinTrans]
      | cons c v' =>
        have hne2 : (c :: v') ≠ [] := List.cons_ne_nil _ _
        simp only [joinTrans, hne1, hne3, hne2, if_false, or_false]
        have hlast : ((a :: b :: u').getLastD 0) = ((b :: u').getLastD 0) :=
          List.getLastD_cons
        rw [hlast]
    have hLHS : transitions ((a :: b :: u') ++ v)
        = (if a * b < 0 then 1 else 0)
            + (transitions (b :: u') + transitions v + joinTrans (b :: u') v) := by
      have hcat : (a :: b :: u') ++ v = a :: b :: (u' ++ v) := rfl
      rw [hcat, transitions_cons_cons]
      have hcast : transitions (b :: (u' ++ v)) = transitions ((b :: u') ++ v) := rfl
      rw [hcast, ih]
    have hRHS : transitions (a :: b :: u') + transitions v + joinTrans (a :: b :: u') v
        = (if a * b < 0 then 1 else 0)
            + transitions (b :: u') + transitions v + joinTrans (b :: u') v := by
      rw [transitions_cons_cons, hjoinEq]
    rw [hLHS, hRHS]
    omega

def T (m : ℕ) : ℕ := transitions (coeffsP m)
def U (m : ℕ) : ℕ := transitions (coeffsQ m)

lemma T_zero : T 0 = 0 := rfl
lemma U_zero : U 0 = 0 := rfl

lemma T_one : T 1 = 0 := by
  show transitions (coeffsP 1) = 0
  rw [coeffsP_one]
  show transitions [1, 1] = 0
  rw [transitions_cons_cons]
  show (if (1:ℝ) * 1 < 0 then 1 else 0) + transitions [1] = 0
  rw [show transitions ([1] : List ℝ) = 0 from rfl]
  norm_num

lemma U_one : U 1 = 1 := by
  show transitions (coeffsQ 1) = 1
  rw [coeffsQ_one]
  show transitions [1, -1] = 1
  rw [transitions_cons_cons]
  show (if (1:ℝ) * (-1) < 0 then 1 else 0) + transitions [-1] = 1
  rw [show transitions ([-1] : List ℝ) = 0 from rfl]
  norm_num

lemma two_mul_pred_add_one (n : ℕ) (hn : 1 ≤ n) : 2 * (n - 1) + 1 = 2 * n - 1 := by
  omega

lemma two_pow_succ_pred (m : ℕ) : 2 * (2 ^ m - 1) + 1 = 2 ^ (m + 1) - 1 := by
  have hp : 1 ≤ (2 : ℕ) ^ m := Nat.one_le_two_pow
  rw [pow_succ']
  exact two_mul_pred_add_one _ (by omega)

/-- Lemma 2.4: `T_m + U_m = 2^m - 1`. -/
lemma T_add_U (m : ℕ) : T m + U m = 2 ^ m - 1 := by
  induction m with
  | zero => simp [T_zero, U_zero]
  | succ m ih =>
    have hP : T (m + 1) = transitions (coeffsP m ++ coeffsQ m) := by
      unfold T
      rw [coeffsP_succ]
    have hQ : U (m + 1) = transitions (coeffsP m ++ (coeffsQ m).map (fun x => -x)) := by
      unfold U
      rw [coeffsQ_succ]
    have hneP : coeffsP m ≠ [] := by
      intro h
      have := congr_arg List.length h
      rw [coeffsP_length] at this
      simp at this
    have hneQ : coeffsQ m ≠ [] := by
      intro h
      have := congr_arg List.length h
      rw [coeffsQ_length] at this
      simp at this
    have hne0 : (coeffsP m).getLastD 0 * (coeffsQ m).headD 0 ≠ 0 := by
      have h1 : (coeffsQ m).headD 0 = 1 := coeffsQ_head m
      have h2 : (coeffsP m).getLastD 0 ≠ 0 := coeffsP_last_ne_zero m
      rw [h1]
      intro h
      exact h2 (by nlinarith)
    have key : joinTrans (coeffsP m) (coeffsQ m)
        + joinTrans (coeffsP m) ((coeffsQ m).map (fun x => -x)) = 1 :=
      joinTrans_sum_one _ _ hneP hneQ hne0
    have hstep : T (m + 1) + U (m + 1) = 2 * (T m + U m) + 1 := by
      rw [hP, hQ, transitions_append, transitions_append, transitions_neg]
      have hj := key
      have htp : transitions (coeffsP m) = T m := rfl
      have htq : transitions (coeffsQ m) = U m := rfl
      omega
    rw [hstep, ih]
    exact two_pow_succ_pred m

end Paper02.RS
