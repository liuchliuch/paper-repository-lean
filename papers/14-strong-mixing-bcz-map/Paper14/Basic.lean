import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Data.Int.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Core definitions for the Boca–Cobeli–Zaharescu map

Independently readable Lean definitions of the paper's objects.
No substantive result of the paper is claimed here.
-/

open MeasureTheory Filter Topology Function Set
open scoped ENNReal
open Classical

noncomputable section

namespace Paper14

/-! ## Phase space and measure -/

/-- Farey triangle `Ω = {(a,b) ∈ (0,1]² : a+b > 1}`. -/
def Omega : Set (ℝ × ℝ) :=
  {x | 0 < x.1 ∧ x.1 ≤ 1 ∧ 0 < x.2 ∧ x.2 ≤ 1 ∧ 1 < x.1 + x.2}

lemma mem_Omega {a b : ℝ} :
    (a, b) ∈ Omega ↔ 0 < a ∧ a ≤ 1 ∧ 0 < b ∧ b ≤ 1 ∧ 1 < a + b :=
  Iff.rfl

/-- Closed triangle cut of the unit square; equal to `Omega` up to a null set. -/
def OmegaBox : Set (ℝ × ℝ) :=
  {x | 0 ≤ x.1 ∧ x.1 ≤ 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ 1 ∧ 1 ≤ x.1 + x.2}

/-- Normalized Lebesgue measure on `Ω`: `dm = 2 da db`, zero outside `Ω`. -/
def m : Measure (ℝ × ℝ) :=
  (2 : ℝ≥0∞) • volume.restrict Omega

/-- Unnormalized area form on `Ω`. -/
def areaOmega : Measure (ℝ × ℝ) := volume.restrict Omega

/-! ## The BCZ map and return time -/

/-- Boca–Cobeli–Zaharescu map `B(a,b) = (b, ⌊(1+a)/b⌋·b - a)`. -/
def B (x : ℝ × ℝ) : ℝ × ℝ :=
  let a := x.1
  let b := x.2
  (b, ((⌊(1 + a) / b⌋ : ℤ) : ℝ) * b - a)

/-- Coordinate form of `B`. -/
def B' (a b : ℝ) : ℝ × ℝ :=
  (b, ((⌊(1 + a) / b⌋ : ℤ) : ℝ) * b - a)

lemma B_eq_B' (a b : ℝ) : B (a, b) = B' a b := rfl

/-- Inverse of `B` (mod null sets): `B^{-1}(a,b) = (⌊(1+b)/a⌋·a - b, a)`. -/
def Binv (x : ℝ × ℝ) : ℝ × ℝ :=
  let a := x.1
  let b := x.2
  (((⌊(1 + b) / a⌋ : ℤ) : ℝ) * a - b, a)

/-- Horocycle section return time `τ(a,b) = 1/(ab)`. -/
def tau (x : ℝ × ℝ) : ℝ := 1 / (x.1 * x.2)

lemma tau_apply (a b : ℝ) : tau (a, b) = 1 / (a * b) := rfl

/-- Birkhoff sums of the return time: `H_n(x) = ∑_{i=0}^{n-1} τ(B^i x)`. -/
def H (n : ℕ) (x : ℝ × ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, tau (B^[i] x)

/-! ## Smaller sections and self-induction -/

/-- Smaller section `Y_r = {(a,b) ∈ Ω : a ≤ r}` for `0 < r < 1`. -/
def Yr (r : ℝ) : Set (ℝ × ℝ) := Omega ∩ {x | x.1 ≤ r}

lemma mem_Yr {r a b : ℝ} : (a, b) ∈ Yr r ↔ (a, b) ∈ Omega ∧ a ≤ r := Iff.rfl

/-- Normalized restriction `m_r = r^{-2} · m|_{Y_r}` (paper: `m(Y_r) = r²`). -/
def mr (r : ℝ) : Measure (ℝ × ℝ) :=
  (ENNReal.ofReal r ^ (2 : ℝ))⁻¹ • m.restrict (Yr r)

/-- Integer step appearing in `φ_r`: `j = ⌊(r^{-1} - b)/a⌋`. -/
def phiJ (r a b : ℝ) : ℤ := ⌊(r⁻¹ - b) / a⌋

/-- Self-induction conjugacy `φ_r(a,b) = (r a, r(b + j a))`. -/
def phiR (r : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  let a := x.1
  let b := x.2
  let j : ℝ := (phiJ r a b : ℤ)
  (r * a, r * (b + j * a))

lemma phiR_eq (r a b : ℝ) :
    phiR r (a, b) = (r * a, r * (b + ((phiJ r a b : ℤ) : ℝ) * a)) := rfl

/-- Inverse of `φ_r` (paper §2). -/
def phiRInv (r : ℝ) (y : ℝ × ℝ) : ℝ × ℝ :=
  let s := y.1
  let t := y.2
  let j : ℝ := (Int.ceil ((t - r) / s) : ℤ)
  (s / r, (t - j * s) / r)

/-! ## Lattices and primitive vectors -/

/-- Lattice `Λ_x = ℤ·(a,0) + ℤ·(b, a⁻¹)` attached to `x = (a,b)`. -/
def Lambda (x : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {v | ∃ p q : ℤ,
    v = ((p : ℝ) * x.1 + (q : ℝ) * x.2, (q : ℝ) / x.1)}

lemma mem_Lambda {a b u v : ℝ} :
    (u, v) ∈ Lambda (a, b) ↔ ∃ p q : ℤ, u = (p : ℝ) * a + (q : ℝ) * b ∧ v = (q : ℝ) / a := by
  constructor
  · rintro ⟨p, q, h⟩
    exact ⟨p, q, congrArg Prod.fst h, congrArg Prod.snd h⟩
  · rintro ⟨p, q, hu, hv⟩
    refine ⟨p, q, ?_⟩
    rw [Prod.ext_iff]
    exact ⟨hu, hv⟩

/-- Nonzero lattice vectors. -/
def LambdaNe (x : ℝ × ℝ) : Set (ℝ × ℝ) := Lambda x \ {0}

/-- `v` is primitive in `Λ_x` if it is not a proper integer multiple of another lattice vector. -/
def IsPrimitiveVec (x : ℝ × ℝ) (v : ℝ × ℝ) : Prop :=
  v ∈ Lambda x ∧ v ≠ 0 ∧
    ∀ (k : ℤ) (w : ℝ × ℝ), w ∈ Lambda x → v = (k : ℝ) • w → |k| = 1 ∨ w = 0

/-- Integer-coefficient primitivity `gcd(p,q)=1`. -/
def IsPrimitivePair (p q : ℤ) : Prop := IsCoprime p q

/-! ## Primitive-point count `Z_{n,α}` (Lemma 5) -/

/-- Predicate: integer pair `(p,q)` contributes a primitive vector of `Λ_x`
to the rectangle `(1-ε,1] × (0,2n]`. -/
def inZRect (n : ℕ) (ε : ℝ) (x : ℝ × ℝ) (p q : ℤ) : Prop :=
  let u := (q : ℝ) * x.2 - (p : ℝ) * x.1
  let v := (q : ℝ) / x.1
  0 < q ∧ (q : ℝ) ≤ 2 * n ∧
    1 - ε < u ∧ u ≤ 1 ∧ 0 < v ∧ v ≤ 2 * n ∧
      IsCoprime p q

/-- `Z_{n,α}(x)` counts primitive vectors of `Λ_x` in `(1-ε,1] × (0,2n]`, `ε = α/n`. -/
def ZCount (n : ℕ) (α : ℝ) (x : ℝ × ℝ) : ℕ :=
  let ε : ℝ := α / n
  letI := Classical.decPred (fun pr : ℤ × ℤ => inZRect n ε x pr.1 pr.2)
  Finset.card <|
    (Finset.Icc (-(4 * n : ℤ)) (4 * n) ×ˢ Finset.Icc (1 : ℤ) (2 * n)).filter
      fun pr => inZRect n ε x pr.1 pr.2

/-- Coordinate `c = a^{-1}` (paper §4). -/
def cOf (x : ℝ × ℝ) : ℝ := x.1⁻¹

/-- Coordinate `θ = b/a (mod 1)`. -/
def thetaOf (x : ℝ × ℝ) : ℝ := Int.fract (x.2 / x.1)

/-- The narrow band (15), with integer coefficient order `(p,q)`. -/
def inSieveBand (Q : ℕ) (c θ ε : ℝ) (pq : ℤ × ℤ) : Prop :=
  1 ≤ pq.2 ∧ pq.2 ≤ (Q : ℤ) ∧
    c - ε < (pq.2 : ℝ) * θ - pq.1 ∧ (pq.2 : ℝ) * θ - pq.1 ≤ c

/-- Finite-sieve count in (15), valid for all real `c, θ, ε`.
The set is finite: `q` is bounded, and each `p` lies in a bounded interval. -/
def GM (M Q : ℕ) (c θ ε : ℝ) : ℕ :=
  {pq : ℤ × ℤ | inSieveBand Q c θ ε pq ∧
    IsCoprime pq.1 ((Int.gcd pq.2 (Int.ofNat M) : ℕ) : ℤ)}.ncard

/-- Primitive count in the same band; no unintended restriction on `p`. -/
def GPrim (Q : ℕ) (c θ ε : ℝ) : ℕ :=
  {pq : ℤ × ℤ | inSieveBand Q c θ ε pq ∧ IsCoprime pq.1 pq.2}.ncard

/-- `ϱ_M(q) = ∏_{ℓ | gcd(q,M), ℓ prime} (1 - ℓ^{-1})`. -/
def varrho (M q : ℕ) : ℝ :=
  (Nat.divisors (Nat.gcd q M)).prod fun ℓ =>
    if Nat.Prime ℓ then (1 - (ℓ : ℝ)⁻¹) else 1

/-- `β_n = ε ∑_{q ≤ Q} ϱ_M(q)`. -/
def betaN (M Q : ℕ) (ε : ℝ) : ℝ :=
  ε * ∑ q ∈ Finset.range Q, varrho M (q + 1)

/-- `δ_M = ∏_{ℓ ≤ P, ℓ prime} (1 - ℓ^{-2})`. -/
def deltaM (P : ℕ) : ℝ :=
  (Finset.range (P + 1)).prod fun ℓ => if Nat.Prime ℓ then (1 - (ℓ : ℝ)⁻¹ ^ 2) else 1

/-- `S_P = ∑_{ℓ > P, ℓ prime} ℓ^{-2}`. -/
def SP (P : ℕ) : ℝ :=
  ∑' ℓ : ℕ, if P < ℓ ∧ Nat.Prime ℓ then (ℓ : ℝ)⁻¹ ^ 2 else 0

/-! ## Induced maps and excess returns (Theorem 4) -/

/-- First return time to `Y` along `T`, defaulting to `0` if no return exists.
Paper convention: `r_Y(y) = min {k ≥ 1 : T^k y ∈ Y}`. -/
def firstReturnTime {α : Type*} (T : α → α) (Y : Set α) (y : α) : ℕ :=
  letI := Classical.decPred (fun k : ℕ => 0 < k ∧ T^[k] y ∈ Y)
  if h : ∃ k, 0 < k ∧ T^[k] y ∈ Y then Nat.find h else 0

/-- Induced map `T_Y(y) = T^{r_Y(y)} y`. -/
def inducedMap {α : Type*} (T : α → α) (Y : Set α) (y : α) : α :=
  T^[firstReturnTime T Y y] y

/-- Time of the `n`th induced return: `R_Y^{(n)}(y) = ∑_{i=0}^{n-1} r_Y(T_Y^i y)`. -/
def Rn {α : Type*} (T : α → α) (Y : Set α) (n : ℕ) (y : α) : ℕ :=
  ∑ i ∈ Finset.range n, firstReturnTime T Y ((inducedMap T Y)^[i] y)

/-- Excess ordinary iterates `D_n = R_Y^{(n)} - n`. -/
def excessDn {α : Type*} (T : α → α) (Y : Set α) (n : ℕ) (y : α) : ℕ :=
  Rn T Y n y - n

/-- The set `E_{n,j} = {y ∈ Y : D_n(y) = j}`. -/
def excessLevel {α : Type*} (T : α → α) (Y : Set α) (n j : ℕ) : Set α :=
  {y ∈ Y | excessDn T Y n y = j}

/-! ## Mixing predicates -/

/-- Strong mixing of a map: `μ(T^{-n}A ∩ C) → μ(A) μ(C)` for all measurable `A, C`. -/
def StrongMixing {α : Type*} [MeasurableSpace α] (T : α → α) (μ : Measure α) : Prop :=
  ∀ A C : Set α, MeasurableSet A → MeasurableSet C →
    Tendsto (fun n : ℕ => μ ((T^[n]) ⁻¹' A ∩ C)) atTop (𝓝 (μ A * μ C))

/-- Strong mixing as an `L²` correlation statement (paper §1, Ex4). -/
def StrongMixingL2 {α : Type*} [MeasurableSpace α] (T : α → α) (μ : Measure α) : Prop :=
  ∀ f g : α → ℝ, MemLp f 2 μ → MemLp g 2 μ →
    Tendsto (fun n : ℕ => ∫ x, f x * g (T^[n] x) ∂μ) atTop
      (𝓝 ((∫ x, f x ∂μ) * (∫ x, g x ∂μ)))

/-- Weak mixing: `T` is measure-preserving and `T × T` is ergodic for `μ × μ`. -/
def WeakMixing {α : Type*} [MeasurableSpace α] (T : α → α) (μ : Measure α) : Prop :=
  MeasurePreserving T μ μ ∧
    Ergodic (fun p : α × α => (T p.1, T p.2)) (μ.prod μ)

/-- Normalized section measure, using the actual measure of the section. -/
def normalizedRestriction {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (Y : Set α) : Measure α := (μ Y)⁻¹ • μ.restrict Y

/-- Hypothesis (i): a.e. invertible measure-preserving conjugacies to the
induced systems, eventually at each scale, converging in measure to `id`. -/
def ConjNearId {α : Type*} [MeasurableSpace α] [MetricSpace α]
    (T : α → α) (μ : Measure α)
    (Y : ℕ → ℝ → Set α) (φ : ℕ → ℝ → α → α) : Prop :=
  ∀ αp : ℝ, 0 < αp →
    (∀ᶠ n : ℕ in atTop,
      MeasurePreserving (φ n αp) μ (normalizedRestriction μ (Y n αp)) ∧
      (∃ ψ : α → α, Measurable ψ ∧
        (∀ᵐ x ∂μ, ψ (φ n αp x) = x) ∧
        (∀ᵐ y ∂(normalizedRestriction μ (Y n αp)), φ n αp (ψ y) = y)) ∧
      (∀ᵐ x ∂μ, inducedMap T (Y n αp) (φ n αp x) = φ n αp (T x))) ∧
    TendstoInMeasure μ (fun n => φ n αp) atTop id

/-- Hypothesis (ii) of Theorem 4: `ρ_{n,α} → 1` and `limsup n(ρ^{-1}-1) < ∞`. -/
def ExcessMomentBound (ρ : ℕ → ℝ → ℝ) : Prop :=
  ∀ αp : ℝ, 0 < αp →
    Tendsto (fun n => ρ n αp) atTop (𝓝 1) ∧
      (∃ C : ℝ, ∀ᶠ n in atTop, n * ((ρ n αp)⁻¹ - 1) ≤ C)

/-- Hypothesis (iii) of Theorem 4 / equation (5): the probability of zero excess
is made small after `α → ∞` then `n → ∞`. -/
def ZeroExcessSmall {α : Type*} [MeasurableSpace α] (T : α → α) (μ : Measure α)
    (Y : ℕ → ℝ → Set α) (_ρ : ℕ → ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ α₀ : ℝ, ∀ αp : ℝ, α₀ < αp →
    ∃ N : ℕ, ∀ n ≥ N,
      (normalizedRestriction μ (Y n αp)
        {y ∈ Y n αp | Rn T (Y n αp) n y = n}) ≤ ENNReal.ofReal ε

/-- Theorem 4 statement (paper §3). -/
def Theorem4Statement {α : Type*} [MeasurableSpace α] [MetricSpace α] [CompactSpace α] [BorelSpace α]
    (T : α → α) (μ : Measure α) (Y : ℕ → ℝ → Set α) (φ : ℕ → ℝ → α → α)
    (ρ : ℕ → ℝ → ℝ) : Prop :=
  IsProbabilityMeasure μ →
    (∃ S : α → α, Measurable S ∧
      (∀ᵐ x ∂μ, S (T x) = x) ∧ (∀ᵐ x ∂μ, T (S x) = x)) →
    MeasurePreserving T μ μ → WeakMixing T μ →
    (∀ αp : ℝ, 0 < αp → ∀ᶠ n : ℕ in atTop,
      MeasurableSet (Y n αp) ∧ 0 < μ (Y n αp) ∧
      ρ n αp = (μ (Y n αp)).toReal) →
    ConjNearId T μ Y φ → ExcessMomentBound ρ → ZeroExcessSmall T μ Y ρ →
      StrongMixing T μ

/-- Theorem 1 statement (paper §1): the BCZ map is strongly mixing for `m`. -/
def Theorem1Statement : Prop := StrongMixing B m

/-- Proposition 3 statement (paper §2 / Appendix A): the BCZ map is weakly mixing. -/
def Proposition3Statement : Prop := WeakMixing B m

/-- Lemma 5 statement (paper §4): void probability of primitive points vanishes. -/
def Lemma5Statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ α₀ : ℝ, ∀ αp : ℝ, α₀ < αp → ∃ N : ℕ, ∀ n ≥ N,
    m {x | ZCount n αp x = 0} ≤ ENNReal.ofReal ε

/-- Flow time to the `n`th induced return, summing the ordinary roof function
up to its discrete return time. -/
def Hr (r : ℝ) (n : ℕ) (y : ℝ × ℝ) : ℝ := H (Rn B (Yr r) n y) y

/-- Lemma 2, all conclusions, with the actual induced flow time. -/
def Lemma2Statement : Prop :=
  ∀ r : ℝ, 0 < r → r < 1 →
    (∀ x ∈ Omega, phiR r x ∈ Yr r) ∧
    (∀ x ∈ Omega, phiRInv r (phiR r x) = x) ∧
    (∀ y ∈ Yr r, phiR r (phiRInv r y) = y) ∧
    MeasurePreserving (phiR r) m (mr r) ∧
    (∀ᵐ x ∂m, inducedMap B (Yr r) (phiR r x) = phiR r (B x)) ∧
    (∀ n : ℕ, ∀ᵐ x ∂m, Hr r n (phiR r x) = r⁻¹ ^ 2 * H n x) ∧
    TendstoInMeasure m phiR (𝓝[<] (1 : ℝ)) id

end Paper14
