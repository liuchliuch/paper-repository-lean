import Paper18.Category.FiniteCohomologyKillingBasic
import Paper18.Category.FiniteCohomologyKillingExtension

/-! # The explicit primitive on the actual universal twisted extension -/
noncomputable section
universe u v w
namespace Paper18.Category.FiniteCohomologyKilling
open Classical
variable {G : Type u} [Group G] {R : Type v} [CommRing R]
  {M : Type w} [CommGroup M] [Module R (Additive M)]
  (ω : FourCocycle G M)

/-- Evaluate the last two cocycle variables on the actual universal module. -/
def cocyclePairLinear (g h : G) : UniversalModule G R →ₗ[R] Additive M :=
  Finsupp.linearCombination R (fun p : NondegeneratePair G => -Additive.ofMul
    (ω.val g h p.1.1 p.1.2))

lemma cocyclePairLinear_pair (g h k l : G) :
    cocyclePairLinear (R := R) ω g h (universalPair G R k l) =
      -Additive.ofMul (ω.val g h k l) := by
  by_cases hk : k = 1
  · subst k
    simp only [universalPair_one_left, map_zero, FourCocycle.one₃, ofMul_one, neg_zero]
  · by_cases hl : l = 1
    · subst l
      simp only [universalPair_one_right, map_zero, FourCocycle.one₄, ofMul_one, neg_zero]
    · rw [universalPair_of_ne G R k l hk hl]
      change Finsupp.linearCombination R _
        (Finsupp.single (⟨(k, l), hk, hl⟩ : NondegeneratePair G) 1) = _
      simp only [Finsupp.linearCombination_single, one_smul]

/-- The fourth cocycle equation is exactly the linear relation needed by
the explicit primitive; every term is an actual module map. -/
lemma cocyclePairLinear_relation (g h k : G) (a : UniversalModule G R) :
    cocyclePairLinear ω h k a - cocyclePairLinear ω (g * h) k a +
      cocyclePairLinear ω g (h * k) a =
        cocyclePairLinear ω g h (universalActionLinear G R k a) := by
  suffices hh : cocyclePairLinear ω h k - cocyclePairLinear ω (g * h) k +
      cocyclePairLinear ω g (h * k) =
      (cocyclePairLinear ω g h).comp (universalActionLinear G R k) by
    exact LinearMap.congr_fun hh a
  apply Finsupp.lhom_ext
  intro p r
  have hs : (Finsupp.single p r : UniversalModule G R) =
      r • universalPair G R p.1.1 p.1.2 := by
    rw [universalPair_of_ne G R _ _ p.2.1 p.2.2]
    change Finsupp.single p r = r • Finsupp.single p (1 : R)
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hs]
  change cocyclePairLinear ω h k (r • universalPair G R p.1.1 p.1.2) -
      cocyclePairLinear ω (g * h) k (r • universalPair G R p.1.1 p.1.2) +
      cocyclePairLinear ω g (h * k) (r • universalPair G R p.1.1 p.1.2) =
    cocyclePairLinear ω g h (universalActionLinear G R k (r • universalPair G R p.1.1 p.1.2))
  simp only [map_smul, ← smul_sub, ← smul_add]
  congr 1
  rw [universalActionLinear_pair]
  simp only [map_add, map_sub, cocyclePairLinear_pair]
  have hc := congrArg Additive.ofMul (ω.cocycle g h k p.1.1 p.1.2)
  simp only [ofMul_mul] at hc
  have hh := congrArg (fun z : Additive M => z - Additive.ofMul (ω.val h k p.1.1 p.1.2) -
    Additive.ofMul (ω.val g (h * k) p.1.1 p.1.2) -
    Additive.ofMul (ω.val g h (k * p.1.1) p.1.2) -
    Additive.ofMul (ω.val g h k p.1.1)) hc
  abel_nf at hh ⊢
  exact hh.symm

/-- The actual additive primitive on the actual group extension. -/
def extensionPrimitiveAdd (x y z : UniversalExtension G R) : Additive M :=
  cocyclePairLinear ω x.quotient y.quotient z.kernel

/-- The actual coboundary calculation on the twisted product group. -/
lemma extensionPrimitiveAdd_spec (x y z w : UniversalExtension G R) :
    extensionPrimitiveAdd ω y z w - extensionPrimitiveAdd ω (x * y) z w +
      extensionPrimitiveAdd ω x (y * z) w - extensionPrimitiveAdd ω x y (z * w) +
      extensionPrimitiveAdd ω x y z =
        Additive.ofMul (ω.val x.quotient y.quotient z.quotient w.quotient) := by
  dsimp only [extensionPrimitiveAdd]
  simp only [UniversalExtension.mul_quotient, UniversalExtension.mul_kernel, map_add]
  calc
    _ = (cocyclePairLinear ω y.quotient z.quotient w.kernel -
        cocyclePairLinear ω (x.quotient * y.quotient) z.quotient w.kernel +
        cocyclePairLinear ω x.quotient (y.quotient * z.quotient) w.kernel) -
        cocyclePairLinear ω x.quotient y.quotient
          (universalActionLinear G R z.quotient w.kernel) -
        cocyclePairLinear ω x.quotient y.quotient
          (universalPair G R z.quotient w.quotient) := by abel
    _ = _ := by
      rw [cocyclePairLinear_relation, cocyclePairLinear_pair]
      abel

lemma cocyclePairLinear_one_left (h : G) : cocyclePairLinear (R := R) ω 1 h = 0 := by
  apply Finsupp.lhom_ext
  intro p r
  simp only [cocyclePairLinear, Finsupp.linearCombination_single,
    FourCocycle.one₁, ofMul_one, neg_zero, smul_zero, LinearMap.zero_apply]

lemma cocyclePairLinear_one_right (g : G) : cocyclePairLinear (R := R) ω g 1 = 0 := by
  apply Finsupp.lhom_ext
  intro p r
  simp only [cocyclePairLinear, Finsupp.linearCombination_single,
    FourCocycle.one₂, ofMul_one, neg_zero, smul_zero, LinearMap.zero_apply]

/-- An actual normalized multiplicative third cochain on the actual extension. -/
def extensionPrimitive : ThreeCochain (UniversalExtension G R) M where
  val x y z := Additive.toMul (extensionPrimitiveAdd ω x y z)
  one₁ y z := by
    apply Additive.ofMul.injective
    change cocyclePairLinear ω 1 y.quotient z.kernel = 0
    rw [cocyclePairLinear_one_left, LinearMap.zero_apply]
  one₂ x z := by
    apply Additive.ofMul.injective
    change cocyclePairLinear ω x.quotient 1 z.kernel = 0
    rw [cocyclePairLinear_one_right, LinearMap.zero_apply]
  one₃ x y := by
    apply Additive.ofMul.injective
    change cocyclePairLinear (R := R) ω x.quotient y.quotient 0 = 0
    exact map_zero _

/-- The explicit third cochain really trivializes the pulled-back fourth
cocycle pointwise on the actual group extension. -/
lemma extensionPrimitive_spec (x y z w : UniversalExtension G R) :
    dThree (extensionPrimitive (R := R) ω).val x y z w =
      ω.val x.quotient y.quotient z.quotient w.quotient := by
  apply Additive.ofMul.injective
  simp only [dThree, extensionPrimitive, ofMul_mul, ofMul_inv, ofMul_toMul]
  simpa only [sub_eq_add_neg] using extensionPrimitiveAdd_spec ω x y z w

end Paper18.Category.FiniteCohomologyKilling
