import Paper08.ProgramPolynomial
import Paper08.LowDegreeDiscreteCost
import Paper08.FPTASDiscreteCost

/-!
# Polynomial absorption of the main discrete source trace

The bound quantifies uniformly over all inputs with fixed model parameters.
Its numerical exponents therefore cannot depend on an oracle polynomial.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 4000
namespace Paper08.FPTASDiscretePolynomial

/-- Numerical inputs satisfying the occurrence and precision restrictions. -/
structure Input (fixed : Parameters.Fixed) (c : ℕ) where
  n : ℕ
  m : ℕ
  L : ℕ
  ε : ℚ
  hn : 1 ≤ n
  hm : 1 ≤ m
  hmn : m ≤ c*n
  hε : 0 < ε
  hεu : ε ≤ 1/2
  hbits : BitComplexity.rationalBits ε ≤ L

def ratio {fixed : Parameters.Fixed} {c : ℕ} (i : Input fixed c) : ℚ := (i.n : ℚ)/i.ε

def order {fixed : Parameters.Fixed} {c : ℕ} (i : Input fixed c) : ℕ :=
  Parameters.truncationOrder fixed i.m i.ε

def level {fixed : Parameters.Fixed} {c : ℕ} (i : Input fixed c) : ℕ :=
  Parameters.level fixed i.m i.ε

lemma ratio_ge_one {fixed : Parameters.Fixed} {c : ℕ} (i : Input fixed c) : 1 ≤ ratio i := by
  apply (le_div_iff₀ i.hε).mpr
  have hn : (1 : ℚ) ≤ i.n := Nat.cast_le.mpr i.hn
  linarith [i.hεu]

lemma length_ge_one {fixed : Parameters.Fixed} {c : ℕ} (i : Input fixed c) : (1 : ℚ) ≤ i.L+1 := by
  have := (Nat.cast_nonneg i.L : (0 : ℚ) ≤ i.L)
  linarith

/-- A uniform polynomial bound, with all constants outside the input quantifier. -/
def Bounded {fixed : Parameters.Fixed} {c : ℕ} (f : Input fixed c → ℕ) : Prop :=
  ∃ B D C : ℕ, ∀ i, (f i : ℚ) ≤ (B : ℚ)*((i.L : ℚ)+1)^D*(ratio i)^C

lemma bounded_const {fixed : Parameters.Fixed} {c : ℕ} (k : ℕ) :
    Bounded (fun _ : Input fixed c => k) := by
  exact ⟨k, 0, 0, fun _ => by simp⟩

lemma bounded_mono {fixed : Parameters.Fixed} {c : ℕ} {f g : Input fixed c → ℕ}
    (hg : Bounded g) (hfg : ∀ i, f i ≤ g i) : Bounded f := by
  obtain ⟨B,D,C,h⟩ := hg
  exact ⟨B,D,C,fun i => (Nat.cast_le.mpr (hfg i)).trans (h i)⟩

lemma bounded_add {fixed : Parameters.Fixed} {c : ℕ} {f g : Input fixed c → ℕ}
    (hf : Bounded f) (hg : Bounded g) : Bounded (fun i => f i+g i) := by
  obtain ⟨B,D,C,h⟩ := hf
  obtain ⟨B',D',C',h'⟩ := hg
  refine ⟨B+B',max D D',max C C',?_⟩
  intro i
  have h₁ : (f i : ℚ) ≤ (B : ℚ)*((i.L : ℚ)+1)^(max D D')*(ratio i)^(max C C') := by
    apply (h i).trans
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (length_ge_one i) (le_max_left _ _)) (Nat.cast_nonneg B))
      (pow_le_pow_right₀ (ratio_ge_one i) (le_max_left _ _))
      (pow_nonneg (by linarith [ratio_ge_one i]) _) (by positivity)
  have h₂ : (g i : ℚ) ≤ (B' : ℚ)*((i.L : ℚ)+1)^(max D D')*(ratio i)^(max C C') := by
    apply (h' i).trans
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (length_ge_one i) (le_max_right _ _)) (Nat.cast_nonneg B'))
      (pow_le_pow_right₀ (ratio_ge_one i) (le_max_right _ _))
      (pow_nonneg (by linarith [ratio_ge_one i]) _) (by positivity)
  push_cast
  nlinarith

lemma bounded_mul {fixed : Parameters.Fixed} {c : ℕ} {f g : Input fixed c → ℕ}
    (hf : Bounded f) (hg : Bounded g) : Bounded (fun i => f i*g i) := by
  obtain ⟨B,D,C,h⟩ := hf
  obtain ⟨B',D',C',h'⟩ := hg
  refine ⟨B*B',D+D',C+C',?_⟩
  intro i
  have hr : 0 ≤ ratio i := by linarith [ratio_ge_one i]
  have hh := mul_le_mul (h i) (h' i) (Nat.cast_nonneg (g i)) (by positivity)
  convert hh using 1 <;> push_cast <;> simp only [pow_add] <;> ring

lemma bounded_pow {fixed : Parameters.Fixed} {c : ℕ} {f : Input fixed c → ℕ}
    (hf : Bounded f) (k : ℕ) : Bounded (fun i => f i^k) := by
  obtain ⟨B,D,C,h⟩ := hf
  refine ⟨B^k,D*k,C*k,?_⟩
  intro i
  have hh := pow_le_pow_left₀ (Nat.cast_nonneg (f i)) (h i) k
  convert hh using 1 <;> simp only [Nat.cast_pow, mul_pow, ← pow_mul]

lemma bounded_n (fixed : Parameters.Fixed) (c : ℕ) : Bounded (fun i : Input fixed c => i.n) := by
  refine ⟨1,0,1,?_⟩
  intro i
  simp only [Nat.cast_one,pow_zero,pow_one,mul_one,one_mul]
  apply (le_div_iff₀ i.hε).mpr
  nlinarith [mul_le_mul_of_nonneg_left (show i.ε ≤ 1 by linarith [i.hεu]) (Nat.cast_nonneg i.n : (0 : ℚ) ≤ i.n)]

lemma bounded_m (fixed : Parameters.Fixed) (c : ℕ) : Bounded (fun i : Input fixed c => i.m) := by
  apply bounded_mono (bounded_mul (bounded_const c) (bounded_n fixed c))
  exact fun i => i.hmn

lemma bounded_bits (fixed : Parameters.Fixed) (c : ℕ) :
    Bounded (fun i : Input fixed c => BitComplexity.rationalBits i.ε) := by
  refine ⟨1,1,0,?_⟩
  intro i
  simp only [Nat.cast_one,pow_one,pow_zero,mul_one,one_mul]
  have hi : (BitComplexity.rationalBits i.ε : ℚ) ≤ i.L := Nat.cast_le.mpr i.hbits
  linarith

lemma bounded_two_order (fixed : Parameters.Fixed) (c : ℕ) :
    Bounded (fun i : Input fixed c => 2^order i) := by
  refine ⟨1,0,ProgramPolynomial.orderExponent fixed c,?_⟩
  intro i
  simpa only [Nat.cast_pow,Nat.cast_ofNat,pow_zero,Nat.cast_one,mul_one,one_mul] using
    ProgramPolynomial.two_pow_order_variables fixed i.hn i.hmn i.hε i.hεu

lemma bounded_order (fixed : Parameters.Fixed) (c : ℕ) : Bounded (fun i : Input fixed c => order i) :=
  bounded_mono (bounded_two_order fixed c) (fun i => (order i).lt_two_pow_self.le)

lemma bounded_level (fixed : Parameters.Fixed) (c : ℕ) : Bounded (fun i : Input fixed c => level i) :=
  bounded_mono (bounded_mul (bounded_const (FPTASCost.levelSlope fixed)) (bounded_order fixed c))
    (fun i => FPTASCost.level_le_slope fixed i.hm i.hε)

lemma bounded_base_order (fixed : Parameters.Fixed) (c base : ℕ) :
    Bounded (fun i : Input fixed c => base^order i) := by
  refine ⟨1,0,ProgramPolynomial.orderExponent fixed c*base.size,?_⟩
  intro i
  simpa only [Nat.cast_pow,pow_zero,Nat.cast_one,mul_one,one_mul] using
    ProgramPolynomial.fixed_base_order_le fixed base i.hn i.hmn i.hε i.hεu

lemma bounded_two_level_add_order (fixed : Parameters.Fixed) (c : ℕ) :
    Bounded (fun i : Input fixed c => 2^(level i+order i)) := by
  apply bounded_mono (bounded_pow (bounded_two_order fixed c) (FPTASCost.levelSlope fixed+1))
  intro i
  rw [← pow_mul]
  apply Nat.pow_le_pow_right (by decide : 0 < 2)
  have hi := FPTASCost.level_le_slope fixed i.hm i.hε
  dsimp only [level,order]
  nlinarith

lemma bounded_two_mul_level (fixed : Parameters.Fixed) (c r : ℕ) :
    Bounded (fun i : Input fixed c => 2^(r*level i)) := by
  apply bounded_mono (bounded_pow (bounded_two_order fixed c) (r*FPTASCost.levelSlope fixed))
  intro i
  rw [← pow_mul]
  apply Nat.pow_le_pow_right (by decide : 0 < 2)
  have hi := FPTASCost.level_le_slope fixed i.hm i.hε
  dsimp only [level,order]
  nlinarith


/-- Polynomial closure for numeric control formulas, applied after their
actual finite-source bounds have been derived. -/
syntax "bound_arith" : tactic
open Lean Elab Tactic Meta in
elab_rules : tactic
| `(tactic| bound_arith) => do
  let t ← instantiateMVars (← getMainTarget)
  let t := t.consumeMData
  unless t.isAppOf ``Bounded do throwError "Expected a polynomial bound, got {t}"
  let f ← whnf t.getAppArgs.back!
  let (head, lhs, rhs) ← lambdaTelescope f fun xs body => do
    let body := body.consumeMData
    let args := body.getAppArgs
    if args.size < 2 then return (body.getAppFn.constName?, none, none)
    let a ← mkLambdaFVars xs args[args.size-2]!
    let b ← mkLambdaFVars xs args.back!
    return (body.getAppFn.constName?, some a, some b)
  match head with
  | some ``HAdd.hAdd | some ``Nat.add =>
      let some a := lhs | throwError "Missing left summand"
      let some b := rhs | throwError "Missing right summand"
      let a ← PrettyPrinter.delab a
      let b ← PrettyPrinter.delab b
      evalTactic (← `(tactic| apply bounded_add (f := $a) (g := $b) <;> bound_arith))
  | some ``HMul.hMul | some ``Nat.mul =>
      let some a := lhs | throwError "Missing left factor"
      let some b := rhs | throwError "Missing right factor"
      let a ← PrettyPrinter.delab a
      let b ← PrettyPrinter.delab b
      evalTactic (← `(tactic| apply bounded_mul (f := $a) (g := $b) <;> bound_arith))
  | some ``HPow.hPow | some ``Nat.pow =>
      try evalTactic (← `(tactic| assumption))
      catch _ =>
        let some a := lhs | throwError "Missing power base"
        let some b := rhs | throwError "Missing exponent"
        let a ← PrettyPrinter.delab a
        let k ← lambdaTelescope b fun _ body => PrettyPrinter.delab body
        evalTactic (← `(tactic| apply bounded_pow (f := $a) (k := $k) <;> bound_arith))
  | _ => evalTactic (← `(tactic| first | assumption | exact bounded_const _))


/-- At inputs at least one, the complete integer ceil/clog control envelope
has a universal degree-seven bound in its two numeric budgets. -/
lemma expression_control_envelope {H P : ℕ} {u : ℚ} (hu : 1 ≤ u)
    (hH : (H : ℚ) ≤ u) (hP : (P : ℚ) ≤ u) :
    (LowDegreeDiscreteCost.expressionControlBound H P : ℚ) ≤ 25000*u^7 := by
  have hu0 : 0 ≤ u := by linarith
  let F : ℚ → ℚ → ℚ := fun v w =>
    w*(4*((v+2)*(w+1))+3)^3+(2*(v*(w+1)+2*w)+2)^3+
      (2*(v*(w+1)+2*w)+2)*((2*(2*(v*(w+1)+2*w)+1)+2)^2+1)+
      (2*(v*(w+1)+2*w)+2)
  calc
    _ = F H P := by
      dsimp only [F]
      unfold LowDegreeDiscreteCost.expressionControlBound LowDegreeDiscreteCost.precisionControlBound
      push_cast
      ring
    _ ≤ F u u := by
      dsimp only [F]
      gcongr

    _ ≤ _ := by
      dsimp only [F]
      have h0 : 1 ≤ u^7 := one_le_pow₀ hu
      have h1 : u ≤ u^7 := by simpa using pow_le_pow_right₀ hu (by decide : 1 ≤ 7)
      have h2 := pow_le_pow_right₀ hu (by decide : 2 ≤ 7)
      have h3 := pow_le_pow_right₀ hu (by decide : 3 ≤ 7)
      have h4 := pow_le_pow_right₀ hu (by decide : 4 ≤ 7)
      have h5 := pow_le_pow_right₀ hu (by decide : 5 ≤ 7)
      have h6 := pow_le_pow_right₀ hu (by decide : 6 ≤ 7)
      nlinarith


lemma selection_formula_envelope {H h : ℕ} {u : ℚ} (hu : 1 ≤ u)
    (hH : (H : ℚ) ≤ 6*u^2) (hh : (h : ℚ) ≤ u) :
    ((2*LowDegreeDiscreteCost.expressionControlBound (H+20) (h+8)+4*H+3 : ℕ) : ℚ) ≤
      (50000*26^7+27 : ℕ)*u^14 := by
  have hu0 : 0 ≤ u := by linarith
  have h1 : 1 ≤ u^2 := one_le_pow₀ hu
  have hu2 : u ≤ u^2 := by simpa using pow_le_pow_right₀ hu (by decide : 1 ≤ 2)
  have hctrl := expression_control_envelope (u := 26*u^2) (by nlinarith)
    (H := H+20) (P := h+8) (by push_cast; nlinarith) (by push_cast; nlinarith)
  have hp : (26*u^2)^7 = 26^7*u^14 := by rw [mul_pow, ← pow_mul]
  rw [hp] at hctrl
  have hu14 : u^2 ≤ u^14 := pow_le_pow_right₀ hu (by decide : 2 ≤ 14)
  have h14 : 1 ≤ u^14 := one_le_pow₀ hu
  push_cast at hctrl ⊢
  nlinarith


lemma monomial_mono {x y : ℚ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    {B B' d c D C : ℕ} (hB : B ≤ B') (hd : d ≤ D) (hc : c ≤ C) :
    (B : ℚ)*y^d*x^c ≤ (B' : ℚ)*y^D*x^C := by
  exact mul_le_mul
    (mul_le_mul (Nat.cast_le.mpr hB) (pow_le_pow_right₀ hy hd)
      (pow_nonneg (by linarith) _) (Nat.cast_nonneg _))
    (pow_le_pow_right₀ hx hc) (pow_nonneg (by linarith) _)
    (by positivity)

lemma log_nodes_le_run_nodes {n m : ℕ} (fixed : Parameters.Fixed)
    (scopes : Fin m → Finset (Fin n)) (query : PrimitiveMomentsQ.Queries scopes)
    (r c : ℕ) (ε : ℚ) :
    FPTASProgram.logNodes m r c (Parameters.truncationOrder fixed m ε)
      (Parameters.precision fixed m ε) (Parameters.level fixed m ε) ≤
      FPTASProgram.runNodeBound fixed scopes query r c ε := by
  unfold FPTASProgram.runNodeBound
  dsimp only
  generalize FPTASProgram.logNodes m r c _ _ _ = g
  generalize Algorithm.exponentialScale _ = h
  generalize Algorithm.exponentialDegree _ = N
  have hp : 1 ≤ 2^h := one_le_pow₀ (by decide : 1 ≤ (2 : ℕ))
  have hn : 1 ≤ N+1 := by omega
  have hfirst : g+h+3 ≤ (N+1)*(g+h+3) := Nat.le_mul_of_pos_left _ (by omega)
  have hsecond : (N+1)*(g+h+3)+2 ≤ (N+1)*((N+1)*(g+h+3)+2) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hf : g ≤ (N+1)*((N+1)*(g+h+3)+2)+1 := by omega
  have hnon : 0 ≤ (N+1)*((N+1)*(g+h+3)+2)+1 := Nat.zero_le _
  nlinarith

lemma scale_le_run_nodes {n m : ℕ} (fixed : Parameters.Fixed)
    (scopes : Fin m → Finset (Fin n)) (query : PrimitiveMomentsQ.Queries scopes)
    (r c : ℕ) (ε : ℚ) :
    Algorithm.exponentialScale (FPTASProgram.logProgram scopes query r c
      (Parameters.truncationOrder fixed m ε) fixed.C (Parameters.primitiveTolerance fixed m ε)).eval ≤
      FPTASProgram.runNodeBound fixed scopes query r c ε := by
  unfold FPTASProgram.runNodeBound
  dsimp only
  generalize FPTASProgram.logNodes m r c _ _ _ = g
  generalize Algorithm.exponentialScale _ = h
  generalize Algorithm.exponentialDegree _ = N
  have hp : h ≤ 2^h := h.lt_two_pow_self.le
  have hf : 1 ≤ (N+1)*((N+1)*(g+h+3)+2)+1 := by omega
  nlinarith [Nat.zero_le (2^h)]


lemma bounded_expression_control {fixed : Parameters.Fixed} {c : ℕ}
    {H P : Input fixed c → ℕ} (hH : Bounded H) (hP : Bounded P) :
    Bounded (fun i => LowDegreeDiscreteCost.expressionControlBound (H i) (P i)) := by
  unfold LowDegreeDiscreteCost.expressionControlBound LowDegreeDiscreteCost.precisionControlBound
  bound_arith


/-- Universal absorption for the complete control expression after the real
numeric budgets have each been bounded by the common envelope. -/
lemma complete_formula_envelope {base I M bits h nodes : ℕ} {u : ℚ} (hu : 1 ≤ u)
    (hbase : (base : ℚ) ≤ u) (hI : (I : ℚ) ≤ u) (hM : (M : ℚ) ≤ u)
    (hbits : (bits : ℚ) ≤ u) (hh : (h : ℚ) ≤ u) (hnodes : (nodes : ℚ) ≤ u) :
    ((base+20000*(2*LowDegreeDiscreteCost.expressionControlBound
      (I*(M+1)+2*M+bits+1+20) (h+8)+4*(I*(M+1)+2*M+bits+1)+3)+nodes+1 : ℕ) : ℚ) ≤
      (20000*(50000*26^7+27)+3 : ℕ)*u^14 := by
  have hu0 : 0 ≤ u := by linarith
  have h1 : 1 ≤ u^2 := one_le_pow₀ hu
  have hu2 : u ≤ u^2 := by simpa using pow_le_pow_right₀ hu (by decide : 1 ≤ 2)
  have hprod : (I : ℚ)*((M : ℚ)+1) ≤ u*(u+1) :=
    mul_le_mul hI (by linarith) (by positivity) hu0
  have hH : ((I*(M+1)+2*M+bits+1 : ℕ) : ℚ) ≤ 6*u^2 := by
    push_cast
    nlinarith
  have he := selection_formula_envelope hu hH hh
  have hu14 : u ≤ u^14 := by simpa using pow_le_pow_right₀ hu (by decide : 1 ≤ 14)
  have h14 : 1 ≤ u^14 := one_le_pow₀ hu
  push_cast at he ⊢
  nlinarith


lemma bounded_base_level_add_order (fixed : Parameters.Fixed) (c base : ℕ) (hb : 1 ≤ base) :
    Bounded (fun i : Input fixed c => base^(level i+order i)) := by
  apply bounded_mono (bounded_pow (bounded_base_order fixed c base) (FPTASCost.levelSlope fixed+1))
  intro i
  rw [← pow_mul]
  apply Nat.pow_le_pow_right (by omega : 0 < base)
  have hi := FPTASCost.level_le_slope fixed i.hm i.hε
  dsimp only [level,order]
  nlinarith


lemma bounded_base_level (fixed : Parameters.Fixed) (c base : ℕ) (hb : 1 ≤ base) :
    Bounded (fun i : Input fixed c => base^level i) := by
  apply bounded_mono (bounded_pow (bounded_base_order fixed c base) (FPTASCost.levelSlope fixed))
  intro i
  rw [← pow_mul]
  apply Nat.pow_le_pow_right (by omega : 0 < base)
  simpa only [Nat.mul_comm] using FPTASCost.level_le_slope fixed i.hm i.hε

attribute [irreducible] Bounded

lemma bounded_parameter_height (fixed : Parameters.Fixed) (c : ℕ) :
    Bounded (fun i : Input fixed c => FPTASDiscreteCost.parameterHeight fixed i.m (order i) (level i) i.ε) := by
  have hm := bounded_m fixed c
  have hs := bounded_order fixed c
  have hJ := bounded_level fixed c
  have hbits := bounded_bits fixed c
  unfold FPTASDiscreteCost.parameterHeight
  bound_arith

lemma bounded_parameter (fixed : Parameters.Fixed) (c : ℕ) :
    Bounded (fun i : Input fixed c => FPTASDiscreteCost.parameterBound fixed i.m i.ε) := by
  have hm := bounded_m fixed c
  have hs := bounded_order fixed c
  have hJ := bounded_level fixed c
  have hH := bounded_parameter_height fixed c
  have hP : Bounded (fun i : Input fixed c => 12*order i+40) := by bound_arith
  have hctrl := bounded_expression_control hH hP
  unfold FPTASDiscreteCost.parameterBound
  dsimp only
  change Bounded (fun i : Input fixed c =>
    5*LowDegreeDiscreteCost.expressionControlBound
      (FPTASDiscreteCost.parameterHeight fixed i.m (order i) (level i) i.ε) (12*order i+40)+
      order i+i.m+level i+4)
  bound_arith

lemma bounded_point (fixed : Parameters.Fixed) (r c : ℕ) :
    Bounded (fun i : Input fixed c => FPTASDiscreteCost.pointBound i.n r (level i)) := by
  have hn := bounded_n fixed c
  have hJ := bounded_level fixed c
  unfold FPTASDiscreteCost.pointBound
  bound_arith

lemma bounded_cell (fixed : Parameters.Fixed) (r c : ℕ) :
    Bounded (fun i : Input fixed c => FPTASDiscreteCost.cellBound i.n r (order i) (level i)) := by
  have hs := bounded_order fixed c
  have hp := bounded_point fixed r c
  unfold FPTASDiscreteCost.cellBound
  bound_arith

lemma bounded_rule_source (fixed : Parameters.Fixed) (c : ℕ) :
    Bounded (fun i : Input fixed c => AntidiagonalCost.boundedBound (order i) (level i)) := by
  have hs := bounded_order fixed c
  have hJ := bounded_level fixed c
  have h2s := bounded_two_order fixed c
  have h2J := bounded_base_level fixed c 2 (by decide)
  have h4s := bounded_base_order fixed c 4
  have h4J := bounded_base_level fixed c 4 (by decide)
  unfold AntidiagonalCost.boundedBound AntidiagonalCost.bound AntidiagonalCost.nodeBound
  dsimp only
  simp only [pow_add,pow_one]
  bound_arith

lemma bounded_exponent_source (fixed : Parameters.Fixed) (c : ℕ) :
    Bounded (fun i : Input fixed c => AntidiagonalCost.exponentBound i.m (order i)) := by
  have hs := bounded_order fixed c
  have hm := bounded_m fixed c
  have h2s := bounded_two_order fixed c
  have h4s := bounded_base_order fixed c 4
  unfold AntidiagonalCost.exponentBound AntidiagonalCost.bound AntidiagonalCost.nodeBound
  simp only [pow_add,pow_one]
  bound_arith

lemma bounded_rule (fixed : Parameters.Fixed) (r c : ℕ) :
    Bounded (fun i : Input fixed c => FPTASDiscreteCost.ruleBound i.n r (order i) (level i)) := by
  have hn := bounded_n fixed c
  have hs := bounded_order fixed c
  have hJ := bounded_level fixed c
  have h2s := bounded_two_order fixed c
  have h2J := bounded_base_level fixed c 2 (by decide)
  have h2rj := bounded_two_mul_level fixed c r
  have hcell := bounded_cell fixed r c
  have hsource := bounded_rule_source fixed c
  unfold FPTASDiscreteCost.ruleBound
  dsimp only
  simp only [pow_add]
  bound_arith

lemma bounded_sparse (fixed : Parameters.Fixed) (r c : ℕ) :
    Bounded (fun i : Input fixed c => FPTASDiscreteCost.sparseBound i.n i.m r (order i) (level i)) := by
  have hs := bounded_order fixed c
  have hm := bounded_m fixed c
  have hrule := bounded_rule fixed r c
  unfold FPTASDiscreteCost.sparseBound
  bound_arith

lemma bounded_moment (fixed : Parameters.Fixed) (r c : ℕ) :
    Bounded (fun i : Input fixed c => FPTASDiscreteCost.momentBound i.n i.m r (order i) (level i)) := by
  have hs := bounded_order fixed c
  have hm := bounded_m fixed c
  have h4s := bounded_base_order fixed c 4
  have hsparse := bounded_sparse fixed r c
  have hsource := bounded_exponent_source fixed c
  unfold FPTASDiscreteCost.momentBound
  bound_arith

lemma bounded_lookup (fixed : Parameters.Fixed) (c : ℕ) :
    Bounded (fun i : Input fixed c => FPTASDiscreteCost.lookupBound i.m) := by
  have hm := bounded_m fixed c
  unfold FPTASDiscreteCost.lookupBound
  bound_arith

lemma bounded_forest (fixed : Parameters.Fixed) (c : ℕ) :
    Bounded (fun i : Input fixed c => FPTASDiscreteCost.forestNodeBound i.m) := by
  have hm := bounded_m fixed c
  have hlookup := bounded_lookup fixed c
  unfold FPTASDiscreteCost.forestNodeBound
  bound_arith

lemma bounded_candidate (fixed : Parameters.Fixed) (c d : ℕ) :
    Bounded (fun i : Input fixed c => FPTASDiscreteCost.candidateBound i.m d (order i)) := by
  have hm := bounded_m fixed c
  have hs := bounded_order fixed c
  have h4d := bounded_base_order fixed c (4*d)
  have hforest := bounded_forest fixed c
  unfold FPTASDiscreteCost.candidateBound
  bound_arith

lemma bounded_support_size (fixed : Parameters.Fixed) (c d : ℕ) :
    Bounded (fun i : Input fixed c => FPTASDiscreteCost.supportSizeBound i.m d (order i)) := by
  have hm := bounded_m fixed c
  have hs := bounded_order fixed c
  have h2s := bounded_two_order fixed c
  have h4d := bounded_base_order fixed c (4*d)
  have hcandidate := bounded_candidate fixed c d
  unfold FPTASDiscreteCost.supportSizeBound
  simp only [pow_add,pow_one]
  bound_arith

lemma bounded_code_step (fixed : Parameters.Fixed) (c d : ℕ) :
    Bounded (fun i : Input fixed c => FPTASDiscreteCost.codeStepBound d (order i)) := by
  have hs := bounded_order fixed c
  have h4d := bounded_base_order fixed c (4*d)
  unfold FPTASDiscreteCost.codeStepBound
  simp only [pow_add,pow_one]
  bound_arith

lemma bounded_code_table (fixed : Parameters.Fixed) (c d : ℕ) :
    Bounded (fun i : Input fixed c => FPTASDiscreteCost.codeTableBound d (order i)) := by
  have hs := bounded_order fixed c
  have hstep := bounded_code_step fixed c d
  unfold FPTASDiscreteCost.codeTableBound
  bound_arith

lemma bounded_membership (fixed : Parameters.Fixed) (c : ℕ) :
    Bounded (fun i : Input fixed c => FPTASDiscreteCost.membershipKeyBound i.m) := by
  have hm := bounded_m fixed c
  unfold FPTASDiscreteCost.membershipKeyBound
  bound_arith

lemma bounded_support_prelude (fixed : Parameters.Fixed) (c d : ℕ) :
    Bounded (fun i : Input fixed c => FPTASDiscreteCost.supportPreludeBound i.m d (order i)) := by
  have hm := bounded_m fixed c
  have hs := bounded_order fixed c
  have h2s := bounded_two_order fixed c
  have h4d := bounded_base_order fixed c (4*d)
  have htable := bounded_code_table fixed c d
  have hsize := bounded_support_size fixed c d
  have hmembership := bounded_membership fixed c
  unfold FPTASDiscreteCost.supportPreludeBound
  simp only [pow_add,pow_one]
  bound_arith

lemma bounded_final_support (fixed : Parameters.Fixed) (c d : ℕ) :
    Bounded (fun i : Input fixed c => FPTASDiscreteCost.finalSupportBound i.m d (order i)) := by
  have hm := bounded_m fixed c
  have hs := bounded_order fixed c
  have h2s := bounded_two_order fixed c
  have h4d := bounded_base_order fixed c (4*d)
  unfold FPTASDiscreteCost.finalSupportBound
  simp only [pow_add,pow_one]
  bound_arith

lemma bounded_log (fixed : Parameters.Fixed) (r c : ℕ) :
    Bounded (fun i : Input fixed c => FPTASDiscreteCost.logBound i.n i.m r c (order i) (level i)) := by
  have hn := bounded_n fixed c
  have hm := bounded_m fixed c
  have hs := bounded_order fixed c
  have h2s := bounded_two_order fixed c
  have h8d := bounded_base_order fixed c (8*FPTASAlgorithm.degreeBound r c)
  have hprelude := bounded_support_prelude fixed c (FPTASAlgorithm.degreeBound r c)
  have hfinal := bounded_final_support fixed c (FPTASAlgorithm.degreeBound r c)
  have hmoment := bounded_moment fixed r c
  have hmembership := bounded_membership fixed c
  unfold FPTASDiscreteCost.logBound FPTASDiscreteCost.logBound.graphWorkBound
  dsimp only
  simp only [pow_add,pow_one]
  bound_arith

/-- These source and parameter-selection polynomials contain no oracle
coefficient or degree. All their exponents are therefore fixed model constants. -/
theorem base_polynomial (fixed : Parameters.Fixed) (r c : ℕ) :
    Bounded (fun i : Input fixed c => 20000*FPTASDiscreteCost.parameterBound fixed i.m i.ε+
      FPTASDiscreteCost.logBound i.n i.m r c (order i) (level i)) := by
  exact bounded_add (bounded_mul (bounded_const 20000) (bounded_parameter fixed c)) (bounded_log fixed r c)


lemma monomial_ge_one {K D C : ℕ} {x y : ℚ} (hK : 1 ≤ K) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    1 ≤ (K : ℚ)*y^D*x^C := by
  have hKq : (1 : ℚ) ≤ K := Nat.cast_le.mpr hK
  have hyp : 1 ≤ y^D := one_le_pow₀ hy
  have hxp : 1 ≤ x^C := one_le_pow₀ hx
  have hkyp : 1 ≤ (K : ℚ)*y^D := by
    simpa only [one_mul] using mul_le_mul hKq hyp (by norm_num : (0 : ℚ) ≤ 1) (Nat.cast_nonneg K)
  simpa only [one_mul] using mul_le_mul hkyp hxp (by norm_num : (0 : ℚ) ≤ 1)
    (mul_nonneg (Nat.cast_nonneg K) (pow_nonneg (by linarith) D))

lemma monomial_power (F K D C : ℕ) (x y : ℚ) :
    (F : ℚ)*((K : ℚ)*y^D*x^C)^14 = ((F*K^14 : ℕ) : ℚ)*y^(D*14)*x^(C*14) := by
  simp only [mul_pow, ← pow_mul, Nat.cast_mul, Nat.cast_pow]
  ring

/-- Uniform polynomial bound for the complete actual discrete executor.
The numerical exponent is chosen before the uniform oracle polynomial. -/
theorem exists_complete_polynomial (p : FPTAS.Params) (fixed : Parameters.Fixed)
    (hb : FPTASCorrectness.FixedBounds p fixed) :
    ∃ C : ℕ, ∀ A degree : ℕ, ∃ B D : ℕ, 0 < B ∧
      ∀ {n m L : ℕ} (E : FactorFamily n p.r m) (labels : Fin m → ℕ)
      (O : (e : Fin m) → EffectiveAccess.Oracle (E e).scope.card (E e).psi.toFun A degree (labels e))
      (_hlabels : ∀ e, labels e ≤ L)
      (_hc : FamilyBoundedOccurrence E p.c) (_hE : ∀ e, (E e).RangeOk p.q)
      (_hLip : ∀ e, (E e).LipOk p.K) (_hne : FPTASCorrectness.CommonNonvanishing p E)
      {ε : ℚ} (_hn : 1 ≤ n) (_hε : 0 < ε) (_hεu : ε ≤ 1/2)
      (_hbits : BitComplexity.rationalBits ε ≤ L),
      (FPTASDiscreteCost.completeDiscreteWork fixed (fun e => (E e).scope)
        (fun e => (O e).valueOracle.query) p.r p.c ε : ℚ) ≤
        (B : ℚ)*((L : ℚ)+1)^D*((n : ℚ)/ε)^C := by
  have hbasePoly := base_polynomial fixed p.r p.c
  unfold Bounded at hbasePoly
  obtain ⟨B₀,D₀,C₀,hbase⟩ := hbasePoly
  let C := max C₀ (max (ProgramPolynomial.arithmeticRatioDegree fixed p.r p.c) 1)
  refine ⟨C*14,?_⟩
  intro A degree
  let K := B₀+ProgramPolynomial.arithmeticCoeff fixed p.r p.c A degree+2
  let D := max D₀ (max (ProgramPolynomial.arithmeticEncodingDegree fixed p.r p.c degree) 1)
  let F := 20000*(50000*26^7+27)+3
  have hK : 1 ≤ K := (by decide : 1 ≤ 2).trans (Nat.le_add_left 2 _)
  have hF : 1 ≤ F := (by decide : 1 ≤ 3).trans (Nat.le_add_left 3 _)
  refine ⟨F*K^14,D*14,?_,?_⟩
  · exact Nat.mul_pos (by omega) (pow_pos (by omega : 0 < K) _)
  intro n m L E labels O hlabels hc hE hLip hne ε hn hε hεu hbits
  let x : ℚ := (n : ℚ)/ε
  let y : ℚ := (L : ℚ)+1
  let U : ℚ := K*y^D*x^C
  have hx : 1 ≤ x := by
    apply (le_div_iff₀ hε).mpr
    have hnq : (1 : ℚ) ≤ n := Nat.cast_le.mpr hn
    linarith
  have hy : 1 ≤ y := by dsimp only [y]; have := (Nat.cast_nonneg L : (0 : ℚ) ≤ L); linarith
  have hU : 1 ≤ U := monomial_ge_one hK hx hy
  have hfactor : (F : ℚ)*U^14 = ((F*K^14 : ℕ) : ℚ)*y^(D*14)*x^(C*14) :=
    monomial_power F K D C x y
  by_cases hm0 : m=0
  · simp only [FPTASDiscreteCost.completeDiscreteWork, if_pos hm0, Nat.cast_one]
    change (1 : ℚ) ≤ ((F*K^14 : ℕ) : ℚ)*y^(D*14)*x^(C*14)
    rw [← hfactor]
    have hp : 1 ≤ U^14 := one_le_pow₀ hU
    have hFq : (1 : ℚ) ≤ F := Nat.cast_le.mpr hF
    nlinarith
  have hm : 1 ≤ m := by omega
  let i : Input fixed p.c := ⟨n,m,L,ε,hn,hm,family_card_le_occurrence_mul_variables E hc,hε,hεu,hbits⟩
  have hbaseU : ((20000*FPTASDiscreteCost.parameterBound fixed m ε+
      FPTASDiscreteCost.logBound n m p.r p.c (Parameters.truncationOrder fixed m ε)
        (Parameters.level fixed m ε) : ℕ) : ℚ) ≤ U := by
    apply (hbase i).trans
    exact monomial_mono hx hy
      ((Nat.le_add_right B₀ _).trans (Nat.le_add_right _ 2))
      (le_max_left _ _) (le_max_left _ _)
  have hnum := ProgramPolynomial.model_numeric_bounds_polynomial p fixed hb E labels O hc hE hLip hne hm hn hε hεu hbits
  have hmono : (ProgramPolynomial.arithmeticCoeff fixed p.r p.c A degree : ℚ)*y^
      ProgramPolynomial.arithmeticEncodingDegree fixed p.r p.c degree*
      x^ProgramPolynomial.arithmeticRatioDegree fixed p.r p.c ≤ U := by
    exact monomial_mono hx hy
      ((Nat.le_add_left _ B₀).trans (Nat.le_add_right _ 2))
      ((le_max_left _ _).trans (le_max_right _ _)) ((le_max_left _ _).trans (le_max_right _ _))
  have hnodes : (FPTASProgram.runNodeBound fixed (fun e => (E e).scope)
      (fun e => (O e).valueOracle.query) p.r p.c ε : ℚ) ≤ U := hnum.1.trans hmono
  have hinput : (FPTASProgram.runInputBound fixed (fun e => (E e).scope)
      (fun e => (O e).valueOracle.query) p.r p.c A degree L ε : ℚ) ≤ U := hnum.2.trans hmono
  let s := Parameters.truncationOrder fixed m ε
  let J := Parameters.level fixed m ε
  let P := Parameters.precision fixed m ε
  let M := FPTASProgram.logNodes m p.r p.c s P J
  let I := PrimitiveInputHeight.inputBound A degree L p.r J P s
  let T := FPTASDiscreteCost.cachedLogApprox (fun e => (E e).scope) (fun e => (O e).valueOracle.query)
    p.r p.c s fixed.C (Parameters.primitiveTolerance fixed m ε)
  have hM : (M : ℚ) ≤ U := (Nat.cast_le.mpr (log_nodes_le_run_nodes fixed
    (fun e => (E e).scope) (fun e => (O e).valueOracle.query) p.r p.c ε)).trans hnodes
  have hI : (I : ℚ) ≤ U := by
    apply (Nat.cast_le.mpr (show I ≤ FPTASProgram.runInputBound fixed (fun e => (E e).scope)
      (fun e => (O e).valueOracle.query) p.r p.c A degree L ε from ?_)).trans hinput
    unfold FPTASProgram.runInputBound
    change I ≤ I+_+3
    omega
  have hcached : T = (FPTASProgram.logProgram (fun e => (E e).scope)
      (fun e => (O e).valueOracle.query) p.r p.c s fixed.C (Parameters.primitiveTolerance fixed m ε)).eval := by
    simp only [T,FPTASDiscreteCost.cachedLogApprox_eq,FPTASProgram.logProgram_eval]
  have hh : (Algorithm.exponentialScale T : ℚ) ≤ U := by
    rw [hcached]
    exact (Nat.cast_le.mpr (scale_le_run_nodes fixed (fun e => (E e).scope)
      (fun e => (O e).valueOracle.query) p.r p.c ε)).trans hnodes
  have hyU : y ≤ U := by
    have h := monomial_mono hx hy (B := 1) (B' := K) (d := 1) (c := 0) (D := D) (C := C) hK
      ((le_max_right _ _).trans (le_max_right _ _)) (Nat.zero_le C)
    simpa only [Nat.cast_one,one_mul,pow_one,pow_zero,mul_one] using h
  have hbitsU : (BitComplexity.rationalBits ε : ℚ) ≤ U :=
    (Nat.cast_le.mpr hbits).trans (by dsimp only [y] at hyU; linarith)
  have hcomplete : (FPTASDiscreteCost.completeDiscreteBound fixed (fun e => (E e).scope)
      (fun e => (O e).valueOracle.query) p.r p.c A degree L ε : ℚ) ≤ (F : ℚ)*U^14 := by
    have h := complete_formula_envelope hU hbaseU hI hM hbitsU hh hnodes
    unfold FPTASDiscreteCost.completeDiscreteBound FPTASDiscreteCost.expSelectionBound
      FPTASDiscreteCost.logHeightBound
    dsimp only
    exact h
  calc
    _ ≤ (FPTASDiscreteCost.completeDiscreteBound fixed (fun e => (E e).scope)
        (fun e => (O e).valueOracle.query) p.r p.c A degree L ε : ℚ) := Nat.cast_le.mpr
      (FPTASDiscreteCost.completeDiscreteWork_le fixed (fun e => (E e).scope) (fun e => (E e).card_le)
        (fun e => (E e).psi.toFun) labels O hlabels ε)
    _ ≤ (F : ℚ)*U^14 := hcomplete
    _ = _ := hfactor

end Paper08.FPTASDiscretePolynomial
