import Verification.Model

/-!
# Paper-facing contracts for "The space of Delzant polytopes is an absolute retract"

Isolated Comparator placeholders.  Statements follow the paper's quantifiers
for the twelve numbered results (Definition 1.1 through Theorem 4.4).  Proofs
are `sorry` here; `Verification.Solution` supplies the matching statements with
production proofs (`Paper17.*`).

Never imported by the proof library or by `Verification.Solution`.
-/

noncomputable section

open scoped Topology BigOperators Pointwise

namespace P17Contract

/-! ## Definition 1.1: absolute extensors imply absolute retracts -/

/-- **Definition 1.1** (characterization).
The extensor property implies the retract property: if `Y` is a nonempty
absolute extensor for metrizable spaces then `Y` is an absolute retract. -/
theorem def_1_1 {Y : Type*} [TopologicalSpace Y]
    (h : IsAbsoluteExtensor Y) (hne : Nonempty Y) :
    IsAbsoluteRetract Y := by
  sorry

/-! ## Theorem 1.2 (main theorem) -/

/-- **Theorem 1.2** (Main theorem).
For every `n ≥ 1`, the space `𝒟(n)` of full-dimensional Delzant polytopes in
`ℝ^n`, with the Hausdorff metric, is an absolute extensor for metrizable
spaces. -/
theorem theorem_1_2 (n : ℕ) (hn : 1 ≤ n) :
    IsAbsoluteExtensor (DelzantSpace n) ∧ IsAbsoluteRetract (DelzantSpace n) := by
  sorry

/-- The locally finite normal-fan conclusion of Theorem 1.2. -/
theorem theorem_1_2_controlled (n : ℕ) (hn : 1 ≤ n)
    (X : Type) [MetricSpace X] (A : Set X) (hA : IsClosed A)
    (f : A → DelzantSpace n) (hf : Continuous f) :
    ∃ F : X → DelzantSpace n, Continuous F ∧
      (∀ a : A, F a = f a) ∧ LocallyFiniteFansOn F Aᶜ := by
  sorry

/-- The open convex support-space restriction in Theorem 1.2. -/
theorem theorem_1_2_open (n : ℕ) (hn : 1 ≤ n)
    (W : Set (PaperSupportSpace n)) (hW : IsOpen W) (hWc : Convex ℝ W)
    (hne : Nonempty {P : DelzantSpace n // InSupportSet W P}) :
    IsAbsoluteExtensor {P : DelzantSpace n // InSupportSet W P} ∧
    IsAbsoluteRetract {P : DelzantSpace n // InSupportSet W P} := by
  sorry

/-! ## Corollary 1.3: strong deformation retraction -/

/-- **Corollary 1.3**.
For every `n ≥ 1` and every `P* ∈ 𝒟(n)`, there is a strong deformation
retraction of `𝒟(n)` onto `{P*}`: a continuous `H : 𝒟(n) × [0,1] → 𝒟(n)`
with `H(P,0) = P`, `H(P,1) = P*`, and `H(P*,t) = P*`.  Consequently `𝒟(n)` is
path connected and `π_k(𝒟(n), P*) = 0` for all `k ≥ 1`. -/
theorem corollary_1_3 (n : ℕ) (hn : 1 ≤ n) (Pstar : DelzantSpace n) :
    ∃ H : DelzantSpace n × ℝ → DelzantSpace n,
      Continuous H ∧
      (∀ P, H (P, 0) = P) ∧
      (∀ P, H (P, 1) = Pstar) ∧
      (∀ t, H (Pstar, t) = Pstar) := by
  sorry

/-! ## Lemma 2.1: interpolation along a chain -/

/-- **Lemma 2.1** (Interpolation along a chain).
Suppose `P₀,…,P_k ∈ 𝒟(n)` and `N(P_j)` refines `N(P_i)` whenever `i < j`.
Every convex combination `P = ∑ λᵢ Pᵢ` is Delzant.  More precisely, if
`j = max {i : λᵢ > 0}`, then `N(P) = N(P_j)`. -/
theorem lemma_2_1 {n k : ℕ} (P : Fin (k + 1) → DelzantSpace n)
    (hchain : ∀ i j : Fin (k + 1), (i : ℕ) ≤ j → DelzantPolytope.le (P i) (P j))
    (w : Fin (k + 1) → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) :
    ∃ j, 0 < w j ∧ (∀ i, 0 < w i → (i : ℕ) ≤ j) ∧
      ∃ Q : DelzantSpace n,
        Q.carrier = ∑ i, w i • (P i).carrier ∧
        DelzantPolytope.le (P j) Q ∧ DelzantPolytope.le Q (P j) := by
  sorry

/-! ## Lemma 2.2: smooth projective refinement -/

/-- **Lemma 2.2** (Smooth projective refinement).
Every rational polytopal complete fan has a smooth polytopal refinement.
Consequently, the normal fans of finitely many full-dimensional Delzant
polytopes have a common smooth polytopal refinement (abstract existence form:
a single Delzant polytope whose fan refines all of the given ones). -/
theorem lemma_2_2 {n : ℕ} (K : PosBody n) (hK : HasRationalNormalFan K) :
    ∃ Q : DelzantSpace n, bodyRefines Q.1 K := by
  sorry

/-! ## Lemma 2.3: common refinements close to a target -/

/-- **Lemma 2.3** (Common refinements close to a target).
Let `P, P₁, …, P_m ∈ 𝒟(n)` and `η > 0`.  There exists `Q ∈ 𝒟(n)` such that
`d_H(Q,P) < η` and `N(Q)` refines `N(P), N(P₁), …, N(P_m)`. -/
theorem lemma_2_3 {n m : ℕ} (P : DelzantSpace n) (Ps : Fin m → DelzantSpace n)
    {η : ℝ} (hη : 0 < η) :
    ∃ Q : DelzantSpace n,
      delzantDist Q P < η ∧
      DelzantPolytope.le P Q ∧
      ∀ i, DelzantPolytope.le (Ps i) Q := by
  sorry

/-! ## Example 2.4: Minkowski sums need not be Delzant -/

/-- **Example 2.4** (determinant 2).
Both `A = conv{(0,0),(1,0),(0,1)}` and `B' = conv{(0,0),(-1,0),(0,1)}` are
Delzant.  The adjacent primitive outward rays `(1,1)` and `(-1,1)` of the
normal fan of `A + B'` have determinant `2`, so `A + B'` is not Delzant. -/
theorem example_2_4_determinant :
    ∃ (u v : Fin 2 → ℤ), AdjacentRays2 u v ∧ det2 u v = 2 := by
  sorry

/-- The actual geometric counterexample in Example 2.4. -/
theorem example_2_4 :
    ∃ P Q : DelzantSpace 2,
      P.carrier = convexHull ℝ ({![0,0], ![1,0], ![0,1]} : Set (V 2)) ∧
      Q.carrier = convexHull ℝ ({![0,0], ![-1,0], ![0,1]} : Set (V 2)) ∧
      ∃ K : PosBody 2, K.carrier = P.carrier + Q.carrier ∧ ¬ IsDelzant K := by
  sorry

/-- **Example 2.4** (geometric form).
The adjacent pair of outward rays of the sum has determinant `2`, so the
primitive edge directions fail the unimodular (Delzant) condition
`|det| = 1`. -/
theorem example_2_4_minkowski :
    ∃ (u v : Fin 2 → ℤ), AdjacentRays2 u v ∧ det2 u v = 2 ∧
      abs (det2 u v) ≠ 1 := by
  sorry

/-! ## Proposition 2.5: equivalence of the metrics -/

/-- **Proposition 2.5** (one direction of the volume bound).
If `r B ⊂ K` and `δ = d_H(K,L) < r`, then
`d_V(K,L) ≤ ((1+δ/r)^n − (1−δ/r)^n) Vol_n(K)`.
This is the implication `d_H → 0 ⇒ d_V → 0`. -/
theorem prop_2_5 {n : ℕ} (K : PosBody n) (L : ℕ → PosBody n) :
    Filter.Tendsto (fun j => Metric.hausdorffDist K.carrier (L j).carrier)
      Filter.atTop (𝓝 0) ↔
    Filter.Tendsto (fun j => volSymmDiff K.carrier (L j).carrier)
      Filter.atTop (𝓝 0) := by
  sorry

/-! ## Equation (2.2): convex-combination error estimate -/

/-- **Equation (2.2)**.
`d_H(∑ λⱼ P_j, K) ≤ ∑ λⱼ d_H(P_j, K) ≤ max_j d_H(P_j, K)` for `λⱼ ≥ 0`,
`∑ λⱼ = 1`.  The bound is independent of the number of summands. -/
theorem equation_2_2 {n : ℕ} {K : Set (V n)}
    (hK : IsCompact K) (hneK : K.Nonempty) (hconv : Convex ℝ K)
    (ι : Type*) (s : Finset ι) (w : ι → ℝ) (P : ι → Set (V n))
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1)
    (hP : ∀ i ∈ s, IsCompact (P i) ∧ (P i).Nonempty)
    {δ : ℝ} (hδ : ∀ i ∈ s, Metric.hausdorffDist (P i) K ≤ δ) :
    Metric.hausdorffDist ((∑ i ∈ s, (w i) • (P i : Set (V n)) : Set (V n))) K ≤ δ := by
  sorry

/-! ## Theorem 3.1: extension by refinement chains -/

/-- **Theorem 3.1** (Extension by refinement chains).
Let `Y` be a nonempty subset of a real normed vector space `E`, with
preorder `≼`.  If (i) finite upper bounds sit arbitrarily close to any
`y ∈ Y`, and (ii) the convex hull of every finite chain lies in `Y`, then `Y`
is an absolute extensor for metrizable spaces. -/
theorem theorem_3_1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Y : Set E} {preceq : E → E → Prop}
    (hY : Y.Nonempty) (h : ExtensionHypotheses Y preceq) :
    IsAbsoluteExtensor Y := by
  sorry

/-! ## Corollary 4.1: filling arbitrary spheres -/

/-- **Corollary 4.1** (Filling arbitrary spheres).
Every continuous map `f : S^k → 𝒟(n)`, for `k ≥ 0`, extends to a continuous
map `F : B^{k+1} → 𝒟(n)`.  Stated as a continuous extension of `f` to an
ambient map that agrees with `f` on the sphere. -/
theorem corollary_4_1 (n k : ℕ) (hn : 1 ≤ n)
    (f : sphere k → DelzantSpace n) (hf : Continuous f) :
    ∃ F : ball k → DelzantSpace n, Continuous F ∧
      (∀ x : sphere k, F ⟨x.val, x.property.le⟩ = f x) ∧
      (∀ C : Set (ball k), IsCompact C →
        (∀ x ∈ C, ∑ i, x.val i ^ 2 < 1) →
        (normalFan ∘ DelzantPolytope.carrier ∘ F '' C).Finite) := by
  sorry

/-! ## Lemma 4.2: approximation compatible with prescribed fans -/

/-- **Lemma 4.2**.
Given `K ∈ 𝒞_p(n)`, finitely many polytopes `P₁,…,P_m ∈ 𝒟(n)`, and `η > 0`,
there exists `Q ∈ 𝒟(n)` with `d_H(Q,K) < η` whose fan refines every `N(P_i)`.
The collection of prescribed polytopes may be empty. -/
theorem lemma_4_2 {n m : ℕ} (K : PosBody n) (Ps : Fin m → DelzantSpace n)
    {η : ℝ} (hη : 0 < η) :
    ∃ Q : DelzantSpace n,
      Metric.hausdorffDist Q.carrier K.carrier < η ∧
      ∀ i, DelzantPolytope.le (Ps i) Q := by
  sorry

/-- Proposition 4.3, including continuity, Delzant values and locally finite normal fans. -/
theorem proposition_4_3 {X : Type} [MetricSpace X] {n : ℕ}
    (f : X → PosBody n) (hf : Continuous f)
    (ε : X → ℝ) (hε : Continuous ε) (hpos : ∀ x, 0 < ε x) :
    ∃ g : X → DelzantSpace n, Continuous g ∧
      (∀ x, Metric.hausdorffDist (g x).carrier (f x).carrier < ε x) ∧
      LocallyFiniteFansOn g Set.univ := by
  sorry

/-! ## Theorem 4.4: homotopy density -/

/-- **Theorem 4.4** (Homotopy density).
There exists a continuous map `H : 𝒞_p(n) × [0,1] → 𝒞_p(n)` such that
`H(K,0) = K` and, for every `t > 0`, `H(K,t) ∈ 𝒟(n)` and
`d_H(H(K,t), K) < t`. -/
theorem theorem_4_4 (n : ℕ) :
    ∃ H : PosBody n × ℝ → PosBody n,
      Continuous H ∧
      (∀ K, H (K, 0) = K) ∧
      (∀ K t, 0 < t → t ≤ 1 →
        ∃ P : DelzantSpace n, (H (K, t)).carrier = P.carrier ∧
          Metric.hausdorffDist (H (K, t)).carrier K.carrier < t) := by
  sorry

end P17Contract
