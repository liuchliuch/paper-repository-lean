import Paper08.RationalProgram

/-!
# Binary long division and Euclidean reduction

The algorithms below compute their results by binary long division and the
Euclidean recurrence. Costs count linear passes over the current binary
words, with six passes budgeted per division bit and per Euclidean step.
They are independent of the native implementation of Lean's `/`, `%`, or gcd.
-/

namespace Paper08.SchoolbookArithmetic

lemma size_double {a : ℕ} (ha : 0 < a) : (2 * a).size = a.size + 1 := by
  have h := Nat.size_bit (b := false) (n := a) (by simp [Nat.bit]; omega)
  simpa [Nat.bit, Nat.mul_comm] using h

lemma size_half_succ_le {a : ℕ} (ha : 0 < a) : (a / 2).size + 1 ≤ a.size := by
  by_cases hh : a / 2 = 0
  · have hm := Nat.mod_lt a (by decide : 0 < 2)
    have he := Nat.mod_add_div a 2
    have heq : a = 1 := by omega
    subst a
    simp
  · have hhalf : 2 * (a / 2) ≤ a := Nat.mul_div_le a 2
    have hs := Nat.size_le_size hhalf
    rw [size_double (by omega : 0 < a / 2)] at hs
    exact hs

structure Division where
  quotient : ℕ
  remainder : ℕ
  bitCost : ℕ

/-- The standard binary digit-at-a-time long division algorithm. -/
def longDivide (a b : ℕ) : Division :=
  if hb : b = 0 then ⟨0, a, 0⟩ else
  if ha : a = 0 then ⟨0, 0, 0⟩ else
    let previous := longDivide (a / 2) b
    let r := 2 * previous.remainder + a % 2
    if b ≤ r then
      ⟨2 * previous.quotient + 1, r - b, previous.bitCost + 6 * (a.size + b.size + 1)⟩
    else
      ⟨2 * previous.quotient, r, previous.bitCost + 6 * (a.size + b.size + 1)⟩
termination_by a
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

/-- The binary algorithm computes the ordinary quotient and remainder. -/
theorem longDivide_spec (a b : ℕ) (hb : 0 < b) :
    (longDivide a b).quotient = a / b ∧ (longDivide a b).remainder = a % b := by
  induction a using Nat.strongRecOn with
  | ind a ih =>
    rw [longDivide, dif_neg (by omega)]
    by_cases ha : a = 0
    · subst a
      simp
    rw [dif_neg ha]
    have hi := ih (a / 2) (Nat.div_lt_self (by omega) (by decide))
    have hrem : (longDivide (a / 2) b).remainder < b := by rw [hi.2]; exact Nat.mod_lt _ hb
    have he : (longDivide (a / 2) b).remainder + b * (longDivide (a / 2) b).quotient = a / 2 := by
      rw [hi.1, hi.2]
      exact Nat.mod_add_div _ _
    have hbit : a % 2 < 2 := Nat.mod_lt _ (by decide)
    have hsplit := Nat.mod_add_div a 2
    dsimp only
    split_ifs with h
    · have hr : 2 * (longDivide (a / 2) b).remainder + a % 2 - b < b := by omega
      have heq : 2 * (longDivide (a / 2) b).remainder + a % 2 - b +
          b * (2 * (longDivide (a / 2) b).quotient + 1) = a := by
        have hs := Nat.sub_add_cancel h
        nlinarith
      have hu := (Nat.div_mod_unique hb).mpr ⟨heq, hr⟩
      exact ⟨hu.1.symm, hu.2.symm⟩
    · have hr : 2 * (longDivide (a / 2) b).remainder + a % 2 < b := by omega
      have heq : 2 * (longDivide (a / 2) b).remainder + a % 2 +
          b * (2 * (longDivide (a / 2) b).quotient) = a := by nlinarith
      have hu := (Nat.div_mod_unique hb).mpr ⟨heq, hr⟩
      exact ⟨hu.1.symm, hu.2.symm⟩

/-- Long division costs a quadratic number of binary-word bit passes. -/
theorem longDivide_cost_le (a b : ℕ) :
    (longDivide a b).bitCost ≤ 6 * a.size * (a.size + b.size + 1) := by
  induction a using Nat.strongRecOn with
  | ind a ih =>
    rw [longDivide]
    split_ifs with hb ha h
    · simp
    · simp
    all_goals
      have ha' : 0 < a := by omega
      have hi := ih (a / 2) (Nat.div_lt_self ha' (by decide))
      have hs := size_half_succ_le ha'
      have hh : (a / 2).size ≤ a.size := by omega
      have hm := Nat.mul_le_mul_left (6 * (a / 2).size)
        (Nat.add_le_add_right (Nat.add_le_add_right hh b.size) 1)
      have hp := Nat.mul_le_mul_right (a.size + b.size + 1)
        (Nat.mul_le_mul_left 6 hs)
      dsimp only
      split_ifs <;> dsimp only <;> nlinarith

/-- Number of actual Euclidean remainder steps. -/
def euclidSteps (a b : ℕ) : ℕ :=
  if hb : b = 0 then 0 else 1 + euclidSteps b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (by omega)

lemma euclidSteps_eq {a b : ℕ} (hb : 0 < b) :
    euclidSteps a b = 1 + euclidSteps b (a % b) := by
  rw [euclidSteps, dif_neg (by omega)]

/-- A positive value halved at a two-step Euclidean stage loses a binary digit. -/
lemma size_drop_of_double_le {r b : ℕ} (hr : 0 < r) (h : 2 * r ≤ b) :
    r.size + 1 ≤ b.size := by
  have hh := Nat.size_le_size h
  rwa [size_double hr] at hh

/-- Euclid's algorithm takes at most twice the second argument's bit length
plus one remainder step. The proof uses the two-step remainder-halving bound. -/
theorem euclidSteps_le (a b : ℕ) : euclidSteps a b ≤ 2 * b.size + 1 := by
  induction b using Nat.strongRecOn generalizing a with
  | ind b ih =>
    by_cases hb : b = 0
    · subst b
      simp [euclidSteps]
    have hbp : 0 < b := by omega
    rw [euclidSteps_eq hbp]
    let r := a % b
    have hrb : r < b := Nat.mod_lt a hbp
    by_cases hr : r = 0
    · simp only [r, hr] at *
      simp [euclidSteps, hr]
    have hrp : 0 < r := by omega
    by_cases hhalf : 2 * r ≤ b
    · have hd := size_drop_of_double_le hrp hhalf
      have hi := ih r hrb b
      change 1 + euclidSteps b r ≤ _
      omega
    · have hrem : b % r = b - r := by
        rw [Nat.mod_eq_sub_mod (by omega : r ≤ b), Nat.mod_eq_of_lt (by omega : b - r < r)]
      have hsmall : 2 * (b % r) ≤ b := by rw [hrem]; omega
      have hremb : b % r < b := (Nat.mod_lt b hrp).trans hrb
      rw [show a % b = r from rfl, euclidSteps_eq hrp]
      by_cases hz : b % r = 0
      · rw [hz, euclidSteps]
        simp
        have hs : 1 ≤ b.size := Nat.size_pos.mpr hbp
        omega
      · have hd := size_drop_of_double_le (by omega : 0 < b % r) hsmall
        have hi := ih (b % r) hremb r
        omega

/-- The actual Euclidean cost, using the proved long-division implementation
for each remainder and charging a linear binary-word pass for loop overhead. -/
def gcdWithCost (a b : ℕ) : ℕ × ℕ :=
  if hb : b = 0 then (a, 0) else
    let previous := gcdWithCost b (a % b)
    (previous.1, previous.2 + (longDivide a b).bitCost + 6 * (a.size + b.size + 1))
termination_by b
decreasing_by exact Nat.mod_lt _ (by omega)


/-- Euclidean reduction computes the ordinary greatest common divisor. -/
theorem gcdWithCost_value (a b : ℕ) : (gcdWithCost a b).1 = Nat.gcd a b := by
  induction b using Nat.strongRecOn generalizing a with
  | ind b ih =>
    by_cases hb : b = 0
    · subst b
      simp [gcdWithCost]
    rw [gcdWithCost, dif_neg hb]
    dsimp only
    rw [ih (a % b) (Nat.mod_lt _ (by omega)) b]
    rw [Nat.gcd_comm a b, Nat.gcd_rec b a, Nat.gcd_comm]

/-- Cost of every Euclidean step is polynomial in a fixed initial operand
length, and the number of steps is controlled by `euclidSteps_le`. -/
theorem gcdWithCost_cost_le (a b B : ℕ) (ha : a.size ≤ B) (hb : b.size ≤ B) :
    (gcdWithCost a b).2 ≤ euclidSteps a b * (6 * (B + 1) * (2 * B + 1)) := by
  induction b using Nat.strongRecOn generalizing a with
  | ind b ih =>
    by_cases hb0 : b = 0
    · subst b
      simp [gcdWithCost, euclidSteps]
    have hbp : 0 < b := by omega
    have hrem : (a % b).size ≤ B := (Nat.size_le_size (Nat.le_of_lt (Nat.mod_lt a hbp))).trans hb
    have hi := ih (a % b) (Nat.mod_lt a hbp) b hb hrem
    have hdiv := longDivide_cost_le a b
    have hstep : (longDivide a b).bitCost + 6 * (a.size + b.size + 1) ≤
        6 * (B + 1) * (2 * B + 1) := by
      have hbase : a.size + b.size + 1 ≤ 2 * B + 1 := by omega
      have hm := Nat.mul_le_mul (Nat.mul_le_mul_left 6 (Nat.add_le_add_right ha 1)) hbase
      nlinarith
    rw [gcdWithCost, dif_neg hb0, euclidSteps_eq hbp]
    dsimp only
    nlinarith

/-- Explicit cubic bit-pass bound for the actual Euclidean reduction. -/
theorem gcdWithCost_cubic (a b B : ℕ) (ha : a.size ≤ B) (hb : b.size ≤ B) :
    (gcdWithCost a b).2 ≤ 36 * (B + 1) ^ 3 := by
  have hc := gcdWithCost_cost_le a b B ha hb
  have hs : euclidSteps a b ≤ 2 * B + 1 := (euclidSteps_le a b).trans (by omega)
  have hm := Nat.mul_le_mul_right (6 * (B + 1) * (2 * B + 1)) hs
  have hp : (2 * B + 1) * (6 * (B + 1) * (2 * B + 1)) ≤ 36 * (B + 1) ^ 3 := by nlinarith
  exact hc.trans (hm.trans hp)


lemma signed_exact_div {a : ℤ} {g : ℕ} (hg : 0 < g) (hga : g ∣ a.natAbs) :
    a / (g : ℤ) = a.sign * ((a.natAbs / g : ℕ) : ℤ) := by
  apply Int.ediv_eq_of_eq_mul_right (by exact_mod_cast hg.ne')
  symm
  calc
    (g : ℤ) * (a.sign * ((a.natAbs / g : ℕ) : ℤ)) =
        a.sign * ((g * (a.natAbs / g) : ℕ) : ℤ) := by push_cast; ring
    _ = a.sign * (a.natAbs : ℤ) := by rw [Nat.mul_div_cancel' hga]
    _ = a := Int.sign_mul_natAbs a

structure Normalized where
  numerator : ℤ
  denominator : ℕ
  bitCost : ℕ

/-- Fraction reduction using the actual Euclidean and long-division programs.
The zero-denominator convention agrees with the rational field convention. -/
def normalize (a b : ℤ) : Normalized :=
  if b = 0 then ⟨0, 1, 0⟩ else
    let g := gcdWithCost a.natAbs b.natAbs
    let n := longDivide a.natAbs g.1
    let d := longDivide b.natAbs g.1
    ⟨b.sign * a.sign * (n.quotient : ℤ), d.quotient,
      g.2 + n.bitCost + d.bitCost + 8 * (a.natAbs.size + b.natAbs.size + 1)⟩

/-- The normalization implementation computes precisely the canonical
numerator and denominator of the rational value, rather than accepting them
as a correctness certificate. -/
theorem normalize_spec (a b : ℤ) :
    (normalize a b).numerator = (Rat.divInt a b).num ∧
      (normalize a b).denominator = (Rat.divInt a b).den := by
  by_cases hb : b = 0
  · subst b
    simp [normalize]
  have hbp : 0 < b.natAbs := Int.natAbs_pos.mpr hb
  let g := Nat.gcd a.natAbs b.natAbs
  have hgp : 0 < g := Nat.gcd_pos_of_pos_right _ hbp
  have hgnum := (longDivide_spec a.natAbs g hgp).1
  have hgden := (longDivide_spec b.natAbs g hgp).1
  have habs : (b.sign * a).natAbs = a.natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hb, Nat.one_mul]
  have hga : g ∣ (b.sign * a).natAbs := by rw [habs]; exact Nat.gcd_dvd_left _ _
  have hdiv := signed_exact_div hgp hga
  rw [habs, Int.sign_mul] at hdiv
  simp only [Int.sign_sign] at hdiv
  rw [normalize, if_neg hb]
  simp only [gcdWithCost_value]
  change b.sign * a.sign * ((longDivide a.natAbs g).quotient : ℤ) = (Rat.divInt a b).num ∧
    (longDivide b.natAbs g).quotient = (Rat.divInt a b).den
  rw [hgnum, hgden, Rat.num_mk, Rat.den_mk, if_neg hb, Int.gcd_def]
  constructor
  · simpa only [mul_assoc] using hdiv.symm
  · rfl

/-- Canonical rational normalization costs polynomially many binary passes.
The cost bound is derived from the implemented divisions and gcd steps. -/
theorem normalize_cost_le (a b : ℤ) (B : ℕ)
    (ha : a.natAbs.size ≤ B) (hb : b.natAbs.size ≤ B) :
    (normalize a b).bitCost ≤ 100 * (B + 1) ^ 3 := by
  by_cases hb0 : b = 0
  · simp [normalize, hb0]
  have hbp : 0 < b.natAbs := Int.natAbs_pos.mpr hb0
  let g := Nat.gcd a.natAbs b.natAbs
  have hgle : g ≤ b.natAbs := Nat.gcd_le_right _ hbp
  have hgs : g.size ≤ B := (Nat.size_le_size hgle).trans hb
  have hc := gcdWithCost_cubic a.natAbs b.natAbs B ha hb
  have hn := longDivide_cost_le a.natAbs g
  have hd := longDivide_cost_le b.natAbs g
  have hn' : (longDivide a.natAbs g).bitCost ≤ 6 * B * (2 * B + 1) := by
    apply hn.trans
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 6 ha) (by omega)
  have hd' : (longDivide b.natAbs g).bitCost ≤ 6 * B * (2 * B + 1) := by
    apply hd.trans
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 6 hb) (by omega)
  rw [normalize, if_neg hb0]
  dsimp only
  rw [gcdWithCost_value]
  change (gcdWithCost a.natAbs b.natAbs).2 + (longDivide a.natAbs g).bitCost +
    (longDivide b.natAbs g).bitCost + 8 * (a.natAbs.size + b.natAbs.size + 1) ≤ _
  nlinarith


/-- Binary shift-and-add multiplication. Its charged linear pass is the
ordinary schoolbook addition of the shifted partial product and `b`. -/
def binaryMultiply (a b : ℕ) : ℕ × ℕ :=
  if ha : a = 0 then (0, 0) else
    let previous := binaryMultiply (a / 2) b
    (2 * previous.1 + (a % 2) * b, previous.2 + 6 * (a.size + b.size + 1))
termination_by a
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

theorem binaryMultiply_value (a b : ℕ) : (binaryMultiply a b).1 = a * b := by
  induction a using Nat.strongRecOn with
  | ind a ih =>
    rw [binaryMultiply]
    split_ifs with ha
    · simp [ha]
    · dsimp only
      rw [ih (a / 2) (Nat.div_lt_self (by omega) (by decide))]
      have he := Nat.mod_add_div a 2
      nlinarith

theorem binaryMultiply_cost_le (a b : ℕ) :
    (binaryMultiply a b).2 ≤ 6 * a.size * (a.size + b.size + 1) := by
  induction a using Nat.strongRecOn with
  | ind a ih =>
    rw [binaryMultiply]
    split_ifs with ha
    · simp
    · have ha' : 0 < a := by omega
      have hi := ih (a / 2) (Nat.div_lt_self ha' (by decide))
      have hs := size_half_succ_le ha'
      have hh : (a / 2).size ≤ a.size := by omega
      have hm := Nat.mul_le_mul_left (6 * (a / 2).size)
        (Nat.add_le_add_right (Nat.add_le_add_right hh b.size) 1)
      have hp := Nat.mul_le_mul_right (a.size + b.size + 1) (Nat.mul_le_mul_left 6 hs)
      dsimp only
      nlinarith

lemma nat_size_le_of_le_pow {a K : ℕ} (ha : a ≤ 2 ^ K) : a.size ≤ K + 1 := by
  apply Nat.size_le.mpr
  rw [pow_succ]
  have hp : 0 < (2 : ℕ) ^ K := by positivity
  omega

lemma int_mul_size_le (a b : ℤ) :
    (a * b).natAbs.size ≤ a.natAbs.size + b.natAbs.size + 1 := by
  have h := Nat.mul_le_mul (Nat.lt_size_self a.natAbs).le (Nat.lt_size_self b.natAbs).le
  rw [← pow_add, ← Int.natAbs_mul] at h
  exact nat_size_le_of_le_pow h

lemma int_add_size_le (a b : ℤ) :
    (a + b).natAbs.size ≤ max a.natAbs.size b.natAbs.size + 2 := by
  let B := max a.natAbs.size b.natAbs.size
  have ha : a.natAbs ≤ 2 ^ B := (Nat.lt_size_self _).le.trans
    (Nat.pow_le_pow_right (by decide : 0 < 2) (le_max_left _ _))
  have hb : b.natAbs ≤ 2 ^ B := (Nat.lt_size_self _).le.trans
    (Nat.pow_le_pow_right (by decide : 0 < 2) (le_max_right _ _))
  have habs := Int.natAbs_add_le a b
  have h : (a + b).natAbs ≤ 2 ^ (B + 1) := by rw [pow_succ]; omega
  exact nat_size_le_of_le_pow h

lemma int_sub_size_le (a b : ℤ) :
    (a - b).natAbs.size ≤ max a.natAbs.size b.natAbs.size + 2 := by
  simpa only [sub_eq_add_neg, Int.natAbs_neg] using int_add_size_le a (-b)

open RationalProgram BitComplexity

/-- Raw integer numerators and denominators used by every binary operation.
Comparison selects an already represented rational, and may reuse the cross
products used by the arithmetic operations. -/
def rawParts : RationalProgram.Op → ℚ → ℚ → ℤ × ℤ
  | .add, x, y => (x.num * (y.den : ℤ) + y.num * (x.den : ℤ), (x.den : ℤ) * (y.den : ℤ))
  | .sub, x, y => (x.num * (y.den : ℤ) - y.num * (x.den : ℤ), (x.den : ℤ) * (y.den : ℤ))
  | .mul, x, y => (x.num * y.num, (x.den : ℤ) * (y.den : ℤ))
  | .div, x, y => (x.num * (y.den : ℤ), (x.den : ℤ) * y.num)
  | .min, x, y => if x ≤ y then (x.num, (x.den : ℤ)) else (y.num, (y.den : ℤ))
  | .max, x, y => if x ≤ y then (y.num, (y.den : ℤ)) else (x.num, (x.den : ℤ))

/-- The raw-pair arithmetic agrees with the abstract rational operator. -/
theorem rawParts_value (o : RationalProgram.Op) (x y : ℚ) :
    Rat.divInt (rawParts o x y).1 (rawParts o x y).2 = o.eval x y := by
  cases o
  · change Rat.divInt (x.num * (y.den : ℤ) + y.num * (x.den : ℤ))
      ((x.den : ℤ) * (y.den : ℤ)) = x + y
    symm
    rw [Rat.add_def, Rat.normalize_eq_mkRat, Rat.mkRat_eq_divInt]
    norm_cast
  · change Rat.divInt (x.num * (y.den : ℤ) - y.num * (x.den : ℤ))
      ((x.den : ℤ) * (y.den : ℤ)) = x - y
    symm
    rw [sub_eq_add_neg, Rat.add_def, Rat.normalize_eq_mkRat, Rat.mkRat_eq_divInt]
    simp only [Rat.neg_num, Rat.neg_den]
    congr 1 <;> push_cast <;> ring
  · change Rat.divInt (x.num * y.num) ((x.den : ℤ) * (y.den : ℤ)) = x * y
    symm
    rw [Rat.mul_eq_mkRat, Rat.mkRat_eq_divInt]
    norm_cast
  · exact (Rat.div_def' x y).symm
  · rcases le_total x y with h | h
    · simp only [rawParts, if_pos h, Op.eval, min_eq_left h, Rat.num_divInt_den]
    · by_cases he : x ≤ y
      · have heq : x = y := le_antisymm he h
        subst y
        simp [rawParts, Op.eval]
      · simp only [rawParts, if_neg he, Op.eval, min_eq_right h, Rat.num_divInt_den]
  · rcases le_total x y with h | h
    · simp only [rawParts, if_pos h, Op.eval, max_eq_right h, Rat.num_divInt_den]
    · by_cases he : x ≤ y
      · have heq : x = y := le_antisymm he h
        subst y
        simp [rawParts, Op.eval]
      · simp only [rawParts, if_neg he, Op.eval, max_eq_left h, Rat.num_divInt_den]

/-- Signed multiplication uses the validated shift/add multiplication of
absolute values; sign changes require only a linear word pass. -/
def signedMultiply (a b : ℤ) : ℤ :=
  a.sign * b.sign * ((binaryMultiply a.natAbs b.natAbs).1 : ℤ)

@[simp] theorem signedMultiply_value (a b : ℤ) : signedMultiply a b = a * b := by
  rw [signedMultiply, binaryMultiply_value, Nat.cast_mul]
  calc
    a.sign * b.sign * ((a.natAbs : ℤ) * (b.natAbs : ℤ)) =
        (a.sign * (a.natAbs : ℤ)) * (b.sign * (b.natAbs : ℤ)) := by ring
    _ = a * b := by rw [Int.sign_mul_natAbs, Int.sign_mul_natAbs]

/-- Actual raw-pair construction: every cross product is returned by the
shift/add algorithm. Comparisons use those same integer cross products. -/
def implementedRawParts (o : RationalProgram.Op) (x y : ℚ) : ℤ × ℤ :=
  let xy := signedMultiply x.num (y.den : ℤ)
  let yx := signedMultiply y.num (x.den : ℤ)
  let nn := signedMultiply x.num y.num
  let dd := signedMultiply (x.den : ℤ) (y.den : ℤ)
  match o with
  | .add => (xy + yx, dd)
  | .sub => (xy - yx, dd)
  | .mul => (nn, dd)
  | .div => (xy, yx)
  | .min => if xy ≤ yx then (x.num, (x.den : ℤ)) else (y.num, (y.den : ℤ))
  | .max => if xy ≤ yx then (y.num, (y.den : ℤ)) else (x.num, (x.den : ℤ))

@[simp] theorem implementedRawParts_eq (o : RationalProgram.Op) (x y : ℚ) :
    implementedRawParts o x y = rawParts o x y := by
  cases o <;> simp [implementedRawParts, rawParts, Rat.le_iff, mul_comm]

/-- Canonical-pair implementation of an individual rational operation. -/
def kernel (o : RationalProgram.Op) (x y : ℚ) : Normalized :=
  normalize (implementedRawParts o x y).1 (implementedRawParts o x y).2

/-- The implemented kernel returns exactly the canonical components of the
specified operator. -/
theorem kernel_spec (o : RationalProgram.Op) (x y : ℚ) :
    (kernel o x y).numerator = (o.eval x y).num ∧
      (kernel o x y).denominator = (o.eval x y).den := by
  have h := normalize_spec (rawParts o x y).1 (rawParts o x y).2
  simpa only [kernel, implementedRawParts_eq, rawParts_value] using h

/-- Explicit raw multiplication and linear-pass work, in addition to actual
normalization. The four possible products can be formed once and reused. -/
def kernelCost (o : RationalProgram.Op) (x y : ℚ) : ℕ :=
  (kernel o x y).bitCost +
    (binaryMultiply x.num.natAbs y.den).2 +
    (binaryMultiply y.num.natAbs x.den).2 +
    (binaryMultiply x.num.natAbs y.num.natAbs).2 +
    (binaryMultiply x.den y.den).2 +
    40 * (rationalBits x + rationalBits y + 1)

lemma components_size_le_bits (x : ℚ) :
    x.num.natAbs.size ≤ rationalBits x ∧ x.den.size ≤ rationalBits x := by
  unfold rationalBits
  omega

/-- Every raw integer supplied to normalization has length linear in the
actual input encodings. -/
theorem rawParts_size_le (o : RationalProgram.Op) (x y : ℚ) :
    (rawParts o x y).1.natAbs.size ≤ rationalBits x + rationalBits y + 3 ∧
      (rawParts o x y).2.natAbs.size ≤ rationalBits x + rationalBits y + 3 := by
  have hx := components_size_le_bits x
  have hy := components_size_le_bits y
  have hxy := int_mul_size_le x.num (y.den : ℤ)
  have hyx := int_mul_size_le y.num (x.den : ℤ)
  have hnn := int_mul_size_le x.num y.num
  have hdd := int_mul_size_le (x.den : ℤ) (y.den : ℤ)
  have hdn := int_mul_size_le (x.den : ℤ) y.num
  simp only [Int.natAbs_natCast] at hxy hyx hdd hdn
  cases o
  · have hh := int_add_size_le (x.num * (y.den : ℤ)) (y.num * (x.den : ℤ))
    dsimp only [rawParts]
    omega
  · have hh := int_sub_size_le (x.num * (y.den : ℤ)) (y.num * (x.den : ℤ))
    dsimp only [rawParts]
    omega
  · dsimp only [rawParts]
    omega
  · dsimp only [rawParts]
    omega
  · dsimp only [rawParts]
    split_ifs <;> simp only [Int.natAbs_natCast] <;> omega
  · dsimp only [rawParts]
    split_ifs <;> simp only [Int.natAbs_natCast] <;> omega

/-- The actual schoolbook/Euclidean operation pipeline is bounded by a fixed
multiple of the operand-sensitive cubic charge in the expression model. -/
theorem kernelCost_le (o : RationalProgram.Op) (x y : ℚ) :
    kernelCost o x y ≤ 10000 * (rationalBits x + rationalBits y + 1) ^ 3 := by
  let K := rationalBits x + rationalBits y + 1
  have hK : 1 ≤ K := by dsimp [K]; omega
  have hx := components_size_le_bits x
  have hy := components_size_le_bits y
  have hr := rawParts_size_le o x y
  have hn := normalize_cost_le (rawParts o x y).1 (rawParts o x y).2
    (rationalBits x + rationalBits y + 3) hr.1 hr.2
  have hxy := binaryMultiply_cost_le x.num.natAbs y.den
  have hyx := binaryMultiply_cost_le y.num.natAbs x.den
  have hnn := binaryMultiply_cost_le x.num.natAbs y.num.natAbs
  have hdd := binaryMultiply_cost_le x.den y.den
  have hbound : ∀ a b : ℕ, a.size ≤ K → b.size ≤ K →
      (binaryMultiply a b).2 ≤ 6 * K * (2 * K + 1) := by
    intro a b ha hb
    apply (binaryMultiply_cost_le a b).trans
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 6 ha) (by omega)
  have hp₁ := hbound x.num.natAbs y.den (by dsimp [K]; omega) (by dsimp [K]; omega)
  have hp₂ := hbound y.num.natAbs x.den (by dsimp [K]; omega) (by dsimp [K]; omega)
  have hp₃ := hbound x.num.natAbs y.num.natAbs (by dsimp [K]; omega) (by dsimp [K]; omega)
  have hp₄ := hbound x.den y.den (by dsimp [K]; omega) (by dsimp [K]; omega)
  change (kernel o x y).bitCost + _ + _ + _ + _ + 40 * K ≤ 10000 * K ^ 3
  change (normalize (rawParts o x y).1 (rawParts o x y).2).bitCost ≤ 100 * (K + 3) ^ 3 at hn
  have hn' : (kernel o x y).bitCost ≤ 100 * (K + 3) ^ 3 := by
    simpa only [kernel, implementedRawParts_eq] using hn
  nlinarith


/-- Signed floor division implemented using the quotient and remainder from
binary long division. A negative nonintegral quotient is rounded downward. -/
def floorKernel (x : ℚ) : ℤ × ℕ :=
  let d := longDivide x.num.natAbs x.den
  let cost := d.bitCost + 8 * (x.num.natAbs.size + x.den.size + 1)
  if x.num < 0 then
    if d.remainder = 0 then (-((d.quotient : ℕ) : ℤ), cost)
    else (-((d.quotient : ℕ) : ℤ) - 1, cost)
  else (((d.quotient : ℕ) : ℤ), cost)

/-- Correctness of the implemented rational-floor kernel. -/
theorem floorKernel_value (x : ℚ) : (floorKernel x).1 = ⌊x⌋ := by
  have hs := longDivide_spec x.num.natAbs x.den x.den_pos
  have hd : (0 : ℤ) < x.den := by exact_mod_cast x.den_pos
  have hrem : (longDivide x.num.natAbs x.den).remainder < x.den := by
    rw [hs.2]
    exact Nat.mod_lt _ x.den_pos
  have he : ((longDivide x.num.natAbs x.den).remainder : ℤ) +
      (x.den : ℤ) * ((longDivide x.num.natAbs x.den).quotient : ℤ) = (x.num.natAbs : ℤ) := by
    rw [hs.1, hs.2]
    exact_mod_cast Nat.mod_add_div x.num.natAbs x.den
  have hr0 : (0 : ℤ) ≤ (longDivide x.num.natAbs x.den).remainder := by positivity
  have hrlt : ((longDivide x.num.natAbs x.den).remainder : ℤ) < x.den := by exact_mod_cast hrem
  rw [Rat.floor_def']
  unfold floorKernel
  dsimp only
  split_ifs with hn hz
  · have habs : (x.num.natAbs : ℤ) = -x.num := by rw [Int.natCast_natAbs, abs_of_neg hn]
    have heq : (0 : ℤ) + (x.den : ℤ) * (-((longDivide x.num.natAbs x.den).quotient : ℤ)) = x.num := by
      rw [hz, habs] at he
      norm_num at he
      nlinarith
    exact ((Int.ediv_emod_unique hd).mpr ⟨heq, by simp, hd⟩).1.symm
  · have habs : (x.num.natAbs : ℤ) = -x.num := by rw [Int.natCast_natAbs, abs_of_neg hn]
    have hrpos : (0 : ℤ) < (longDivide x.num.natAbs x.den).remainder := by exact_mod_cast (by omega : 0 < (longDivide x.num.natAbs x.den).remainder)
    have heq : ((x.den : ℤ) - (longDivide x.num.natAbs x.den).remainder) +
        (x.den : ℤ) * (-((longDivide x.num.natAbs x.den).quotient : ℤ) - 1) = x.num := by nlinarith
    exact ((Int.ediv_emod_unique hd).mpr ⟨heq, by omega, by omega⟩).1.symm
  · have habs : (x.num.natAbs : ℤ) = x.num := by rw [Int.natCast_natAbs, abs_of_nonneg (by omega)]
    have heq : ((longDivide x.num.natAbs x.den).remainder : ℤ) +
        (x.den : ℤ) * ((longDivide x.num.natAbs x.den).quotient : ℤ) = x.num := by omega
    exact ((Int.ediv_emod_unique hd).mpr ⟨heq, hr0, hrlt⟩).1.symm

theorem floorKernel_cost_le (x : ℚ) :
    (floorKernel x).2 ≤ 10000 * (rationalBits x + 1) ^ 3 := by
  have hs := components_size_le_bits x
  have hd := longDivide_cost_le x.num.natAbs x.den
  have hsum : x.num.natAbs.size + x.den.size + 1 ≤ 2 * rationalBits x + 1 := by omega
  have hm := Nat.mul_le_mul (Nat.mul_le_mul_left 6 hs.1) hsum
  unfold floorKernel
  dsimp only
  split_ifs <;> dsimp only <;> nlinarith

/-- Full schoolbook/Euclidean execution cost of an arithmetic expression.
Each node is charged the cost of the actual validated kernel implementation. -/
def exprBitCost : RationalProgram.Expr → ℕ
  | .atom _ => 0
  | .node o x y => exprBitCost x + exprBitCost y + kernelCost o x.eval y.eval
  | .floor x => exprBitCost x + (floorKernel x.eval).2

/-- Construct a rational directly from the canonical fields returned by the
implemented kernel. The proof fields are erased; no second normalization or
abstract rational operation is executed. -/
def kernelValue (o : RationalProgram.Op) (x y : ℚ) : ℚ :=
  Rat.mk' (kernel o x y).numerator (kernel o x y).denominator
    (by rw [(kernel_spec o x y).2]; exact (o.eval x y).den_nz)
    (by rw [(kernel_spec o x y).1, (kernel_spec o x y).2]; exact (o.eval x y).reduced)

@[simp] theorem kernelValue_eq (o : RationalProgram.Op) (x y : ℚ) :
    kernelValue o x y = o.eval x y := by
  apply Rat.ext
  · exact (kernel_spec o x y).1
  · exact (kernel_spec o x y).2

/-- Execute the entire expression using the implemented exact kernels.
Intermediate values are generated recursively from the original leaves. -/
def execute : RationalProgram.Expr → ℚ × ℕ
  | .atom q => (q, 0)
  | .node o x y =>
    let a := execute x
    let b := execute y
    (kernelValue o a.1 b.1, a.2 + b.2 + kernelCost o a.1 b.1)
  | .floor x =>
    let a := execute x
    let b := floorKernel a.1
    ((b.1 : ℚ), a.2 + b.2)

/-- Actual execution returns the specified value and the traced kernel cost. -/
theorem execute_spec (e : RationalProgram.Expr) :
    (execute e).1 = e.eval ∧ (execute e).2 = exprBitCost e := by
  induction e with
  | atom q => simp [execute, Expr.eval, exprBitCost]
  | node o x y hx hy =>
    simp only [execute, Expr.eval, exprBitCost, hx.1, hx.2, hy.1, hy.2, kernelValue_eq]
    trivial
  | floor x hx =>
    simp only [execute, Expr.eval, exprBitCost, hx.1, hx.2, floorKernel_value]
    trivial

/-- The original expression charge dominates the implemented arithmetic
pipeline by a single universal factor. -/
theorem exprBitCost_le (e : RationalProgram.Expr) : exprBitCost e ≤ 10000 * e.work := by
  induction e with
  | atom q => simp [exprBitCost, Expr.work]
  | node o x y hx hy =>
    have h := kernelCost_le o x.eval y.eval
    dsimp only [exprBitCost, Expr.work]
    nlinarith
  | floor x hx =>
    have h := floorKernel_cost_le x.eval
    dsimp only [exprBitCost, Expr.work]
    nlinarith

/-- An unconditional polynomial upper bound for the implemented exact
arithmetic pipeline, in the actual expression size and input bit length. -/
theorem exprBitCost_polynomial (e : RationalProgram.Expr) :
    exprBitCost e ≤ 10000 * e.operations *
      (4 * ((e.inputHeight + 2) * (e.operations + 1)) + 3) ^ 3 := by
  apply (exprBitCost_le e).trans
  have h := Nat.mul_le_mul_left 10000 (Expr.work_le e)
  simpa only [Nat.mul_assoc] using h

/-- Polynomial bit-pass time of the actual recursively evaluated program. -/
theorem execute_cost_polynomial (e : RationalProgram.Expr) :
    (execute e).2 ≤ 10000 * e.operations *
      (4 * ((e.inputHeight + 2) * (e.operations + 1)) + 3) ^ 3 := by
  rw [(execute_spec e).2]
  exact exprBitCost_polynomial e

end Paper08.SchoolbookArithmetic
