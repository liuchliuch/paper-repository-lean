# External mathematical inputs

The release retains **13 exact generic external theorem interfaces**. Their proposition arguments have no supplied Lean inhabitants, and no custom production axiom or production `sorry` supplies them. Six required numbered results use no external mathematical input; nine are proved relative to the named generic interfaces. The separate Appendix A.3 instantiation uses two generic convex-selection facts.

[external-inputs.json](external-inputs.json) preserves exact original hypotheses/types and use-site bindings from the independent delivery review. Standard generic chaining, Gram-radius stability, finite-interval covering, Lewis normalization, Shannon information and finite-dimensional convex selection are distinguished from paper-owned Huber algorithms, centered transfer, pilot, query lower bound and measurable-selector instantiations.

## AnchoredChaining

`Paper29/ExternalProcess.lean` contains the exact interface.

Jambulapati–Lee–Liu–Sidford arXiv:2311.18145v1 §1.6.2 Lemma1.14 first inequality (1.20), symmetrization/generic chaining

Universal bounded anchored population function class; no Huber, score, transfer, pilot or query-complexity conclusion

```lean
def AnchoredChaining (C : ℝ) : Prop :=
  ∀ (n m : ℕ) (T : Type) (t₀ : T) (π : Fin n → ℝ) (f : Fin n → T → ℝ),
    0 < m → (∀ i, 0 < π i) → (∑ i, π i = 1) →
    (∀ i, f i t₀ = 0) →
    (∀ i, BddAbove (Set.range (fun t => |f i t|))) →
    ∀ G : (Fin m → Fin n) → ℝ, (∀ ν, 0 ≤ G ν) →
      (∀ ν, Chaining.gamma2 (sampleMetric π f ν) ≤ ENNReal.ofReal (G ν)) →
      Sampling.expectation π (errorSup (m := m) π f) ≤ C * Sampling.expectation π G
```

Primary sources: [reference 1](https://arxiv.org/html/2311.18145v1#S1.SS6.SSS2).

Missing formalization: This published generic result is a Prop parameter with no supplied Lean inhabitant, custom production axiom or sorry. Its application is in the own proof; the external theorem itself is not machine-proved.

## RadiusLogNonexpansive

`Paper29/WeightLogMetric.lean` contains the exact interface.

Same source Lemma2.6

Loss-independent weighted Gram inverse/radius-squared log stability; own scalar contraction and finite construction proved locally

```lean
def RadiusLogNonexpansive : Prop :=
  ∀ (n d : ℕ) (A : Matrix (Fin n) (Fin d) ℝ), A.rank = d →
    (∀ i, A i ≠ 0) → ∀ u w : PositiveWeights n, ∀ i,
      |Real.log (Leverage.radiusSq A u i) - Real.log (Leverage.radiusSq A w i)| ≤ logDist u w
```

Primary sources: [reference 1](https://arxiv.org/html/2311.18145v1#S2.SS1).

Missing formalization: This published generic result is a Prop parameter with no supplied Lean inhabitant, custom production axiom or sorry. Its application is in the own proof; the external theorem itself is not machine-proved.

## HuberPrimitive

`Paper29/ExternalCovering.lean` contains the exact interface.

Same source Definition1.8 and covering/Dudley argument in proof of Theorem3.14; P29 imported (3.11)/(A.3)

Only finite interval covering estimate given actual normalized schemes; no existence, mass, all-radius assembly or sampling probability

```lean
def HuberPrimitive (α C : ℝ) : Prop :=
  ∀ (n d : ℕ) (A : Matrix (Fin n) (Fin d) ℝ), A.rank = d → (∀ i, A i ≠ 0) →
    ∀ (a b : ℤ), a ≤ b → 4 * Real.log (2*(n:ℝ)) ≤ ((Finset.Icc a b).card : ℝ) →
    ∀ scheme : HuberScheme A a b α,
      gamma2 (T := Ball A ((2:ℝ)^(b+1)))
        (fun h k => huberMetric A (maxScore A (Finset.Icc a b) scheme.w) h k) ≤
      ENNReal.ofReal (C * Real.sqrt ((2:ℝ)^(b+1)) * ProcessTools.logFactor n)
```

Primary sources: [reference 1](https://arxiv.org/html/2311.18145v1#S3.Thmtheorem14).

Missing formalization: This published generic result is a Prop parameter with no supplied Lean inhabitant, custom production axiom or sorry. Its application is in the own proof; the external theorem itself is not machine-proved.

## PowerPrimitive

`Paper29/ExternalCovering.lean` contains the exact interface.

Same source Definition1.8 and covering/Dudley argument in proof of Theorem3.14; P29 imported (3.11)/(A.3)

Only finite interval covering estimate given actual normalized schemes; no existence, mass, all-radius assembly or sampling probability

```lean
def PowerPrimitive (C : ℝ) : Prop :=
  ∀ (n d p : ℕ), (p = 1 ∨ p = 2) → ∀ (A : Matrix (Fin n) (Fin d) ℝ),
    A.rank = d → (∀ i, A i ≠ 0) → ∀ (a b : ℤ), a ≤ b →
    4 * Real.log (2*(n:ℝ)) ≤ ((Finset.Icc a b).card : ℝ) →
    ∀ w : ℤ → PositiveWeights n,
      (∀ j ∈ Finset.Icc a b, ∀ i,
        |Leverage.radius A (w j) i|^p / Leverage.leverage A (w j) i = (2:ℝ)^j) →
      (∀ j, j ∈ Finset.Icc a b → j+1 ∈ Finset.Icc a b → ∀ i, w (j+1) i ≤ w j i) →
      gamma2 (T := PowerBall A p ((2:ℝ)^(b+1)))
        (fun h k => powerMetric A p (maxScore A (Finset.Icc a b) w) h k) ≤
      ENNReal.ofReal (C * Real.sqrt ((2:ℝ)^(b+1)) * ProcessTools.logFactor n)
```

Primary sources: [reference 1](https://arxiv.org/html/2311.18145v1#S3.Thmtheorem14).

Missing formalization: This published generic result is a Prop parameter with no supplied Lean inhabitant, custom production axiom or sorry. Its application is in the own proof; the external theorem itself is not machine-proved.

## LewisOneNormalization

`Paper29/LewisInput.lean` contains the exact interface.

Cohen–Peng arXiv:1412.0588v1 Definition2.2 and Corollary3.4

Exact l1 endpoint normalization existence; finite stopped approximation, safe factor16 inflation and trace mass proved locally

```lean
def LewisOneNormalization : Prop :=
  ∀ (n d : ℕ) (A : Matrix (Fin n) (Fin d) ℝ), A.rank = d → (∀ i, A i ≠ 0) →
    ∃ w : PositiveWeights n, ∀ i,
      Leverage.radius A w i / Leverage.leverage A w i = 1
```

Primary sources: [reference 1](https://arxiv.org/pdf/1412.0588).

Missing formalization: This published generic result is a Prop parameter with no supplied Lean inhabitant, custom production axiom or sorry. Its application is in the own proof; the external theorem itself is not machine-proved.

## ConditionalChainRule

`Paper29/GeneralInformation.lean` contains the exact interface.

R. M. Gray, Entropy and Information Theory, corrected first edition (3 June 2023), §§5.3/5.5, equation5.28, Corollary5.5.3 and Lemma5.5.7; general source quantization and data processing

Generic Shannon/KL rules only. Chain theorem uses standard Borel source/response/tagged observation, arbitrary conditioning alphabet and an actual conditional kernel. Arbitrary source handled by local finite quantization. No algorithm, active-slot inequality, stopping, query count or Lemma4.3 bound is an input.

```lean
def ConditionalChainRule : Prop :=
  ∀ {Ω S B H Z : Type} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace B]
    [MeasurableSpace H] [MeasurableSpace Z] [StandardBorelSpace S] [StandardBorelSpace B]
    [StandardBorelSpace Z] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → S) (Bsrc : Ω → B) (Hrv : Ω → H) (Zrv : Ω → Z)
    (K : H → Measure (S × B)) (f : H → (S × B) → Z),
    Measurable X → Measurable Bsrc → Measurable Hrv → Measurable Zrv →
    Measurable (Function.uncurry f) → ConditionalLaw μ (fun ω => (X ω,Bsrc ω)) Hrv K →
    (∀ ω,Zrv ω=f (Hrv ω) (X ω,Bsrc ω)) →
    information μ X (fun ω => (Hrv ω,Zrv ω)) = information μ X Hrv +
      ∫⁻ h,information (K h) Prod.fst (f h) ∂μ.map Hrv
```

Primary sources: [reference 1](https://ee.stanford.edu/~gray/it1_corrected_6-23.pdf).

Missing formalization: This published generic result is a Prop parameter with no supplied Lean inhabitant, custom production axiom or sorry. Its application is in the own proof; the external theorem itself is not machine-proved.

## IndependentInformation

`Paper29/GeneralInformation.lean` contains the exact interface.

R. M. Gray, Entropy and Information Theory, corrected first edition (3 June 2023), §§5.3/5.5, equation5.28, Corollary5.5.3 and Lemma5.5.7; general source quantization and data processing

Generic Shannon/KL rules only. Chain theorem uses standard Borel source/response/tagged observation, arbitrary conditioning alphabet and an actual conditional kernel. Arbitrary source handled by local finite quantization. No algorithm, active-slot inequality, stopping, query count or Lemma4.3 bound is an input.

```lean
def IndependentInformation : Prop :=
  ∀ {Ω S T : Type} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → S) (Y : Ω → T),
    Measurable X → Measurable Y → ProbabilityTheory.IndepFun X Y μ → information μ X Y=0
```

Primary sources: [reference 1](https://ee.stanford.edu/~gray/it1_corrected_6-23.pdf).

Missing formalization: This published generic result is a Prop parameter with no supplied Lean inhabitant, custom production axiom or sorry. Its application is in the own proof; the external theorem itself is not machine-proved.

## ReversibleRelabeling

`Paper29/GeneralInformation.lean` contains the exact interface.

R. M. Gray, Entropy and Information Theory, corrected first edition (3 June 2023), §§5.3/5.5, equation5.28, Corollary5.5.3 and Lemma5.5.7; general source quantization and data processing

Generic Shannon/KL rules only. Chain theorem uses standard Borel source/response/tagged observation, arbitrary conditioning alphabet and an actual conditional kernel. Arbitrary source handled by local finite quantization. No algorithm, active-slot inequality, stopping, query count or Lemma4.3 bound is an input.

```lean
def ReversibleRelabeling : Prop :=
  ∀ {Ω S T Z : Type} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace Z]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → S) (Y : Ω → T) (f : T → Z) (g : Z → T),
    Measurable X → Measurable Y → Measurable f → Measurable g → Function.LeftInverse g f →
    information μ X (fun ω => f (Y ω))=information μ X Y
```

Primary sources: [reference 1](https://ee.stanford.edu/~gray/it1_corrected_6-23.pdf).

Missing formalization: This published generic result is a Prop parameter with no supplied Lean inhabitant, custom production axiom or sorry. Its application is in the own proof; the external theorem itself is not machine-proved.

## ConstantInformation

`Paper29/GeneralInformation.lean` contains the exact interface.

R. M. Gray, Entropy and Information Theory, corrected first edition (3 June 2023), §§5.3/5.5, equation5.28, Corollary5.5.3 and Lemma5.5.7; general source quantization and data processing

Generic Shannon/KL rules only. Chain theorem uses standard Borel source/response/tagged observation, arbitrary conditioning alphabet and an actual conditional kernel. Arbitrary source handled by local finite quantization. No algorithm, active-slot inequality, stopping, query count or Lemma4.3 bound is an input.

```lean
def ConstantInformation : Prop :=
  ∀ {Ω S Z : Type} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace Z]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → S) (z : Z),
    Measurable X → information μ X (fun _ => z)=0
```

Primary sources: [reference 1](https://ee.stanford.edu/~gray/it1_corrected_6-23.pdf).

Missing formalization: This published generic result is a Prop parameter with no supplied Lean inhabitant, custom production axiom or sorry. Its application is in the own proof; the external theorem itself is not machine-proved.

## SourceQuantization

`Paper29/GeneralInformation.lean` contains the exact interface.

R. M. Gray, Entropy and Information Theory, corrected first edition (3 June 2023), §§5.3/5.5, equation5.28, Corollary5.5.3 and Lemma5.5.7; general source quantization and data processing

Generic Shannon/KL rules only. Chain theorem uses standard Borel source/response/tagged observation, arbitrary conditioning alphabet and an actual conditional kernel. Arbitrary source handled by local finite quantization. No algorithm, active-slot inequality, stopping, query count or Lemma4.3 bound is an input.

```lean
def SourceQuantization : Prop :=
  ∀ {Ω S T : Type} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → S) (Y : Ω → T),
    Measurable X → Measurable Y → information μ X Y =
      ⨆ (m : ℕ) (f : S → Fin m) (_ : Measurable f),information μ (fun ω => f (X ω)) Y
```

Primary sources: [reference 1](https://ee.stanford.edu/~gray/it1_corrected_6-23.pdf).

Missing formalization: This published generic result is a Prop parameter with no supplied Lean inhabitant, custom production axiom or sorry. Its application is in the own proof; the external theorem itself is not machine-proved.

## SourceDataProcessing

`Paper29/GeneralInformation.lean` contains the exact interface.

R. M. Gray, Entropy and Information Theory, corrected first edition (3 June 2023), §§5.3/5.5, equation5.28, Corollary5.5.3 and Lemma5.5.7; general source quantization and data processing

Generic Shannon/KL rules only. Chain theorem uses standard Borel source/response/tagged observation, arbitrary conditioning alphabet and an actual conditional kernel. Arbitrary source handled by local finite quantization. No algorithm, active-slot inequality, stopping, query count or Lemma4.3 bound is an input.

```lean
def SourceDataProcessing : Prop :=
  ∀ {Ω S T Z : Type} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace Z]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → S) (Y : Ω → T) (f : S → Z),
    Measurable X → Measurable Y → Measurable f → information μ (fun ω => f (X ω)) Y ≤ information μ X Y
```

Primary sources: [reference 1](https://ee.stanford.edu/~gray/it1_corrected_6-23.pdf).

Missing formalization: This published generic result is a Prop parameter with no supplied Lean inhabitant, custom production axiom or sorry. Its application is in the own proof; the external theorem itself is not machine-proved.

## ParametricQuadraticSelection

`Paper29/ExternalConvexSelection.lean` contains the exact interface.

Classical measurable/continuous maximum theorem specialized to positive quadratic regularization; Terazono–Matani SIAM J. Optim.23(2), 2013; classical convex Tikhonov/proximal limit, Bauschke–Combettes regularization of minimization problems

Generic finite-dimensional convex objectives only. No Huber, sample, pilot or regression conclusion. Actual Huber joint continuity, convexity, nonnegativity and unregularized minimum-norm point checked locally, then general regularization/parameter theorems instantiated.

```lean
def ParametricQuadraticSelection : Prop :=
  ∀ n d (F : (Fin n → ℝ) × Space d → ℝ),Continuous F →
    (∀ b,ConvexOn ℝ Set.univ (fun x => F (b,x))) → (∀ b x,0 ≤ F (b,x)) →
    ∃ z : ℕ → (Fin n → ℝ) → Space d,
      (∀ k,Measurable (z k)) ∧ ∀ k b,
        RegularizedMinimizer (fun x => F (b,x)) k (z k b) ∧
        ∀ x,RegularizedMinimizer (fun x => F (b,x)) k x → x=z k b
```

Primary sources: [reference 1](https://doi.org/10.1137/110850189), [reference 2](https://doi.org/10.1007/978-3-319-48311-5).

Missing formalization: This published generic result is a Prop parameter with no supplied Lean inhabitant, custom production axiom or sorry. Its application is in the own proof; the external theorem itself is not machine-proved.

## TikhonovConvergence

`Paper29/ExternalConvexSelection.lean` contains the exact interface.

Classical measurable/continuous maximum theorem specialized to positive quadratic regularization; Terazono–Matani SIAM J. Optim.23(2), 2013; classical convex Tikhonov/proximal limit, Bauschke–Combettes regularization of minimization problems

Generic finite-dimensional convex objectives only. No Huber, sample, pilot or regression conclusion. Actual Huber joint continuity, convexity, nonnegativity and unregularized minimum-norm point checked locally, then general regularization/parameter theorems instantiated.

```lean
def TikhonovConvergence : Prop :=
  ∀ d (f : Space d → ℝ),Continuous f → ConvexOn ℝ Set.univ f →
    ∀ v,(∀ y,f v ≤ f y) → (∀ y,(∀ u,f y ≤ f u) → ‖v‖ ≤ ‖y‖) →
    ∀ z : ℕ → Space d,(∀ k,RegularizedMinimizer f k (z k)) → Tendsto z atTop (nhds v)
```

Primary sources: [reference 1](https://doi.org/10.1137/110850189), [reference 2](https://doi.org/10.1007/978-3-319-48311-5).

Missing formalization: This published generic result is a Prop parameter with no supplied Lean inhabitant, custom production axiom or sorry. Its application is in the own proof; the external theorem itself is not machine-proved.

## Source qualifications

The process/geometry interfaces are universal specializations of the cited JLLS statements, rather than claims that every project type appears verbatim there. Lewis normalization uses the exact positive auxiliary fixed-point equivalence. The information theorem assumes actual regular conditional kernels and standard-Borel response/tagged spaces; it does not assert existence for every arbitrary source. The two convex-selection inputs are standard consequences/specializations; historical primary publisher metadata and abstract were checked, while the DOI body was inaccessible. No verified verbatim numbered-body statement or Lean witness is claimed for that source.
