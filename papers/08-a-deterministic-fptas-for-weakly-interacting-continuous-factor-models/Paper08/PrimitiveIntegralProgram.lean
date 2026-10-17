import Paper08.PrimitiveExpressions

/-! # Arithmetic expressions for the actual sparse quadrature and moments -/
open scoped BigOperators
namespace Paper08.PrimitiveIntegralProgram
open RationalProgram PrimitiveProgram PrimitiveExpressions CellGrid RationalQuadrature
open PrimitiveMomentsQ

abbrev LocalQueries {n t : ℕ} (scopes : Fin t → Finset (Fin n)) :=
  (i : Fin t) → (Fin (scopes i).card → ℚ) → ℕ → ℚ

def stepExpr {n t : ℕ} (scopes : Fin t → Finset (Fin n)) (query : LocalQueries scopes)
    (α : Fin t → ℕ) (P : ℕ) (ν : Fin t → ℕ) (z : Grid (commonLevels scopes ν))
    (i : Fin t) (l : ℕ) : Expr :=
  primitiveSampleExpr P (α i) (query i (queryPoint l (localIndex scopes ν z i l)) P)

def incrementExpr {n t : ℕ} (scopes : Fin t → Finset (Fin n)) (query : LocalQueries scopes)
    (α : Fin t → ℕ) (P : ℕ) (ν : Fin t → ℕ) (z : Grid (commonLevels scopes ν)) (i : Fin t) : Expr :=
  match ν i with
  | 0 => stepExpr scopes query α P ν z i 0
  | l+1 => .node .sub (stepExpr scopes query α P ν z i (l+1)) (stepExpr scopes query α P ν z i l)

def weightExpr {n : ℕ} (m : Fin n → ℕ) : Expr := .node .div (.atom 1) (twoPower (∑ v, m v))

def ruleExpr {n t : ℕ} (scopes : Fin t → Finset (Fin n)) (query : LocalQueries scopes)
    (α : Fin t → ℕ) (P J : ℕ) : Expr :=
  letI := tupleOrder t
  sumSet (TupleCount.boundedTuples t J) fun ν =>
    letI := gridOrder (commonLevels scopes ν)
    sumSet Finset.univ fun z : Grid (commonLevels scopes ν) =>
      .node .mul (weightExpr (commonLevels scopes ν))
        (productSet Finset.univ (incrementExpr scopes query α P ν z))

def primitiveExpr {n t : ℕ} (scopes : Fin t → Finset (Fin n)) (query : LocalQueries scopes)
    (α : Fin t → ℕ) (s C : ℕ) (τ : ℚ) : Expr :=
  let J := Oracle.totalLevelChoice s C τ
  let P := Oracle.samplePrecision s (Oracle.primitiveSampleTol s J C τ)
  ruleExpr scopes query α P J

@[simp] theorem stepExpr_eval {n t : ℕ} (scopes : Fin t → Finset (Fin n)) (query : LocalQueries scopes)
    (α : Fin t → ℕ) (P : ℕ) (ν : Fin t → ℕ) (z : Grid (commonLevels scopes ν)) (i : Fin t) (l : ℕ) :
    (stepExpr scopes query α P ν z i l).eval = stepQ scopes (primitiveTable scopes query α P) ν z i l :=
  primitiveSampleExpr_eval _ _ _

@[simp] theorem incrementExpr_eval {n t : ℕ} (scopes : Fin t → Finset (Fin n)) (query : LocalQueries scopes)
    (α : Fin t → ℕ) (P : ℕ) (ν : Fin t → ℕ) (z : Grid (commonLevels scopes ν)) (i : Fin t) :
    (incrementExpr scopes query α P ν z i).eval =
      incrementQ scopes (primitiveTable scopes query α P) ν z i := by
  simp only [incrementExpr, incrementQ]
  split <;> simp_all [Expr.eval, Op.eval]

@[simp] theorem weightExpr_eval {n : ℕ} (m : Fin n → ℕ) : (weightExpr m).eval = weightQ m := by
  simp [weightExpr, Expr.eval, Op.eval, weightQ]

@[simp] theorem ruleExpr_eval {n t : ℕ} (scopes : Fin t → Finset (Fin n)) (query : LocalQueries scopes)
    (α : Fin t → ℕ) (P J : ℕ) :
    (ruleExpr scopes query α P J).eval = ruleQ scopes (primitiveTable scopes query α P) J := by
  simp only [ruleExpr, sumSet_eval, Expr.eval, Op.eval, weightExpr_eval,
    productSet_eval, incrementExpr_eval, ruleQ]
@[simp] theorem primitiveExpr_eval {n t : ℕ} (scopes : Fin t → Finset (Fin n)) (query : LocalQueries scopes)
    (α : Fin t → ℕ) (s C : ℕ) (τ : ℚ) :
    (primitiveExpr scopes query α s C τ).eval = primitiveRuleQ scopes query α s C τ :=
  ruleExpr_eval _ _ _ _ _

/-- The exact factorial weight is constructed, rather than inserted as a computed leaf. -/
def factorialWeightExpr {m : ℕ} (d : Fin m →₀ ℕ) : Expr :=
  productSet d.support fun e => RationalRecurrenceProgram.factorial (d e)

@[simp] theorem factorialWeightExpr_eval {m : ℕ} (d : Fin m →₀ ℕ) :
    (factorialWeightExpr d).eval = (factorialWeight d : ℚ) := by
  simp [factorialWeightExpr, RationalRecurrenceProgram.eval_factorial, factorialWeight, Finsupp.prod]

def sparseExpr {n m : ℕ} (scopes : Fin m → Finset (Fin n)) (query : Queries scopes)
    (d : Fin m →₀ ℕ) (s C : ℕ) (τ : ℚ) : Expr :=
  primitiveExpr (fun i : Fin d.support.card => scopes (d.support.orderEmbOfFin rfl i))
    (fun i => query (d.support.orderEmbOfFin rfl i))
    (fun i => d (d.support.orderEmbOfFin rfl i)) s C τ

@[simp] theorem sparseExpr_eval {n m : ℕ} (scopes : Fin m → Finset (Fin n)) (query : Queries scopes)
    (d : Fin m →₀ ℕ) (s C : ℕ) (τ : ℚ) :
    (sparseExpr scopes query d s C τ).eval = primitiveQ scopes query d s C τ :=
  primitiveExpr_eval _ _ _ _ _ _

def momentExpr {n m : ℕ} (scopes : Fin m → Finset (Fin n)) (query : Queries scopes)
    (B : Finset (Fin m)) (j s C : ℕ) (τ : ℚ) : Expr :=
  if j = 0 then .atom 1 else
    letI := exponentOrder m
    sumSet (Finset.finsuppAntidiag B j) fun d =>
      .node .div (sparseExpr scopes query d s C τ) (factorialWeightExpr d)

@[simp] theorem momentExpr_eval {n m : ℕ} (scopes : Fin m → Finset (Fin n)) (query : Queries scopes)
    (B : Finset (Fin m)) (j s C : ℕ) (τ : ℚ) :
    (momentExpr scopes query B j s C τ).eval = momentQ scopes query B j s C τ := by
  by_cases hj : j = 0 <;> simp [momentExpr, momentQ, hj, Expr.eval, Op.eval]

/-- A polynomial per-sample arithmetic-node bound. -/
def sampleNodes (s P : ℕ) : ℕ := 40*(s+1)*(P+3)^2

lemma stepExpr_operations {n t : ℕ} (scopes : Fin t → Finset (Fin n)) (query : LocalQueries scopes)
    (α : Fin t → ℕ) (P s : ℕ) (hα : ∀ i, α i ≤ s)
    (ν : Fin t → ℕ) (z : Grid (commonLevels scopes ν)) (i : Fin t) (l : ℕ) :
    (stepExpr scopes query α P ν z i l).operations ≤ sampleNodes s P := by
  exact (primitiveSampleExpr_operations P (α i) _).trans (by dsimp [sampleNodes]; gcongr; exact hα i)

lemma incrementExpr_operations {n t : ℕ} (scopes : Fin t → Finset (Fin n)) (query : LocalQueries scopes)
    (α : Fin t → ℕ) (P s : ℕ) (hα : ∀ i, α i ≤ s)
    (ν : Fin t → ℕ) (z : Grid (commonLevels scopes ν)) (i : Fin t) :
    (incrementExpr scopes query α P ν z i).operations ≤ 2*sampleNodes s P+1 := by
  unfold incrementExpr
  split
  · exact (stepExpr_operations scopes query α P s hα ν z i _).trans (by omega)
  · simp only [Expr.operations]
    have h₁ := stepExpr_operations scopes query α P s hα ν z i (ν i)
    have h₂ := stepExpr_operations scopes query α P s hα ν z i (ν i-1)
    rename_i l hl
    have h₁ := stepExpr_operations scopes query α P s hα ν z i (l+1)
    have h₂ := stepExpr_operations scopes query α P s hα ν z i l
    omega

@[simp] theorem weightExpr_operations {n : ℕ} (m : Fin n → ℕ) :
    (weightExpr m).operations = (∑ v, m v)+1 := by simp [weightExpr, Expr.operations]


/-- Actual arithmetic-node envelope, exponential only in total level and order. -/
def primitiveNodes (r s P J : ℕ) : ℕ :=
  2^((r+1)*J+s) * (r*J+2*s*(sampleNodes s P+1)+4)

theorem ruleExpr_operations {n t r s : ℕ} (scopes : Fin t → Finset (Fin n))
    (hscopes : ∀ i, (scopes i).card ≤ r) (query : LocalQueries scopes)
    (α : Fin t → ℕ) (hα : ∀ i, α i ≤ s) (ht : t ≤ s) (P J : ℕ) :
    (ruleExpr scopes query α P J).operations ≤ primitiveNodes r s P J := by
  letI := tupleOrder t
  let U := r*J+2*s*(sampleNodes s P+1)+3
  have hinner : ∀ ν ∈ TupleCount.boundedTuples t J,
      (letI := gridOrder (commonLevels scopes ν)
       sumSet Finset.univ fun z : Grid (commonLevels scopes ν) =>
        Expr.node .mul (weightExpr (commonLevels scopes ν))
          (productSet Finset.univ (incrementExpr scopes query α P ν z))).operations ≤
            2^(r*J)*U := by
    intro ν hν
    letI := gridOrder (commonLevels scopes ν)
    have hsum : (∑ v, commonLevels scopes ν v) ≤ r*J :=
      (sum_commonLevels_le scopes hscopes ν).trans
        (Nat.mul_le_mul_left r (TupleCount.mem_boundedTuples.mp hν))
    have hprod (z : Grid (commonLevels scopes ν)) :=
      productSet_operations_le Finset.univ (incrementExpr scopes query α P ν z)
        (N := 2*sampleNodes s P+1) (fun i _ => incrementExpr_operations scopes query α P s hα ν z i)
    simp only [Finset.card_univ, Fintype.card_fin] at hprod
    have hh := sumSet_operations_le (Finset.univ : Finset (Grid (commonLevels scopes ν)))
      (fun z => Expr.node .mul (weightExpr (commonLevels scopes ν))
        (productSet Finset.univ (incrementExpr scopes query α P ν z))) (N := U-1) (by
          intro z _
          have hp := hprod z
          simp only [Expr.operations, weightExpr_operations]
          dsimp [U]
          nlinarith)
    have hcard := common_grid_card_le scopes hscopes ν (TupleCount.mem_boundedTuples.mp hν)
    have hU : 1 ≤ U := by dsimp [U]; omega
    simp only [Finset.card_univ, Nat.sub_add_cancel hU] at hh
    exact hh.trans (Nat.mul_le_mul_right U hcard)
  have ho := sumSet_operations_le (TupleCount.boundedTuples t J) _ hinner
  change (sumSet (TupleCount.boundedTuples t J) _).operations ≤ _
  apply ho.trans
  rw [TupleCount.card_boundedTuples]
  have hbin : (J+t).choose t ≤ 2^(J+s) :=
    (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hpow : 1 ≤ 2^(r*J) := one_le_pow₀ (by decide)
  have hh : 2^(r*J)*U+1 ≤ 2^(r*J)*(U+1) := by nlinarith
  have hh' := Nat.mul_le_mul hbin hh
  apply hh'.trans_eq
  dsimp [primitiveNodes, U]
  rw [← Nat.mul_assoc, ← pow_add]
  congr 2 <;> ring

lemma support_card_le_degree {m : ℕ} (d : Fin m →₀ ℕ) : d.support.card ≤ d.degree := by
  calc
    d.support.card = ∑ _i ∈ d.support, 1 := by simp
    _ ≤ ∑ i ∈ d.support, d i := Finset.sum_le_sum fun i hi =>
      Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
    _ = d.degree := rfl

theorem sparseExpr_operations {n m r s C : ℕ} (scopes : Fin m → Finset (Fin n))
    (hscopes : ∀ e, (scopes e).card ≤ r) (query : Queries scopes)
    (d : Fin m →₀ ℕ) (hd : d.degree ≤ s) (τ : ℚ) :
    let J := Oracle.totalLevelChoice s C τ
    let P := Oracle.samplePrecision s (Oracle.primitiveSampleTol s J C τ)
    (sparseExpr scopes query d s C τ).operations ≤ primitiveNodes r s P J := by
  dsimp only [sparseExpr, primitiveExpr]
  apply ruleExpr_operations _ (fun i => hscopes _) _ _ _
    ((support_card_le_degree d).trans hd)
  intro i
  have hi : d (d.support.orderEmbOfFin rfl i) ≤ d.degree :=
    Finset.single_le_sum (fun e _ => Nat.zero_le (d e)) (d.support.orderEmbOfFin_mem rfl i)
  exact hi.trans hd

@[simp] theorem factorialWeightExpr_operations {m : ℕ} (d : Fin m →₀ ℕ) :
    (factorialWeightExpr d).operations = d.degree+d.support.card := by
  simp only [factorialWeightExpr, productSet_operations, RationalRecurrenceProgram.operations_factorial]
  rfl

/-- The complete B-local moment expression has polynomial per-term overhead
and at most 4^s genuine sparse exponent vectors. -/
theorem momentExpr_operations {n m r s C j : ℕ} (scopes : Fin m → Finset (Fin n))
    (hscopes : ∀ e, (scopes e).card ≤ r) (query : Queries scopes)
    (B : Finset (Fin m)) (hB : B.card ≤ s) (hj : j ≤ s) (τ : ℚ) :
    let J := Oracle.totalLevelChoice s C τ
    let P := Oracle.samplePrecision s (Oracle.primitiveSampleTol s J C τ)
    (momentExpr scopes query B j s C τ).operations ≤
      4^s*(primitiveNodes r s P J+2*s+2) := by
  dsimp only
  by_cases hj0 : j = 0
  · simp [momentExpr, hj0, Expr.operations]
  letI := exponentOrder m
  unfold momentExpr
  rw [if_neg hj0]
  have hh := sumSet_operations_le (Finset.finsuppAntidiag B j)
    (fun d => Expr.node .div (sparseExpr scopes query d s C τ) (factorialWeightExpr d))
    (N := primitiveNodes r s
      (Oracle.samplePrecision s (Oracle.primitiveSampleTol s (Oracle.totalLevelChoice s C τ) C τ))
      (Oracle.totalLevelChoice s C τ)+2*s+1) (by
        intro d hd
        have hdeg : d.degree ≤ s := by
          have hh := (Finset.mem_finsuppAntidiag'.mp hd).1
          change d.degree = j at hh
          omega
        have hp := sparseExpr_operations (C := C) scopes hscopes query d hdeg τ
        have hc := (support_card_le_degree d).trans hdeg
        simp only [Expr.operations, factorialWeightExpr_operations]
        dsimp only at hp
        omega)
  exact hh.trans (Nat.mul_le_mul_right _ (TupleCount.card_finsuppAntidiag_le B hB hj))

end Paper08.PrimitiveIntegralProgram
