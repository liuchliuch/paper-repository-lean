# Explicit external inputs and the gate convention

The production files contain no `sorry`, `admit`, or new axiom declaration.
The following results are retained as explicit parameters. A theorem proved
relative to these parameters does not assert that their existence has been
formalized. All P25-specific deductions from them, including source-channel
reduction, actual native circuits and propagation of numerical error, are
separate proof obligations in the production modules.

## Finite complex unitary spectral theorem

**Source:** Sheldon Axler, *Linear Algebra Done Right*, fourth edition,
Theorem 7.55, printed page 262, [author's PDF](https://linear.axler.net/LADR4e.pdf).

For every unitary operator on a finite-dimensional complex inner-product
space, there is an orthonormal eigenbasis and all eigenvalues have modulus
one. `Paper25.UnitarySpectralTheorem.eigenbasis` specializes exactly this
statement to every finite matrix index type. `UnitaryEigenbasis` is supplied
as correctness proof data. The chosen eigenvectors and phases are absent from
the generated circuit and its payloads; `SourceCircuitSimulation` proves the
implemented matrix and probability independent of the eigenbasis choice.

The absent formalization is existence of that eigenbasis in the pinned
library. The phase-estimation distribution, spectral filter estimates,
compression-to-walk deductions and final probability bounds are proved here.
Use sites are `FullspaceFilter`, `GlobalFilterError`, `WalkSelectedFilter`,
`ActualFilterImplementation`, and `SourceCircuitSimulation.spectralData`.

## Elementary real function approximation

**Source:** Emil Jeřábek, *Elementary analytic functions in VTC^0*,
arXiv:2206.12164v3, [primary PDF](https://arxiv.org/pdf/2206.12164v3).
The interface `OperationalModel.ElementaryAnalyticInputs` retains:

- Lemma 3.46(ii), printed p.31: for a positive rational argument, a rational
  square-root approximation with relative error at most `2^(-n)`.
- Proposition 5.8 with Definition 5.4 and Table 1, printed p.45: additive
  approximation to principal real arccos on rational inputs in `[-1,1]`.
- Proposition 5.11 and Table 2, printed pp.46–47: additive sine and cosine
  approximation, specialized to real inputs, whose imaginary-part bound is 0.

Precision `n` is unary; fraction numerators and positive denominators are
binary and need not be relatively prime. The cited algorithms are uniform
TC^0 and hence logspace. The finite-transducer realization and changes to the
project's exact encodings remain explicit external inputs. Square root is
never incorrectly given an additive guarantee over an unbounded domain.

`RationalRep` stores actual unreduced fraction bytes. Runtime arithmetic and
numerical primitive emission use those bytes. Mathematical canonical-rational
helpers do not carry a claim of a logspace gcd or normalization algorithm.
The P25-specific label phase, bounded rational quotient, clipping, inverse
cosine angle, fixed selector angle and their complete error propagation are
proved in `RepresentedAnalytic` and `SelectorArithmetic`. No external field
asserts a label-filter compiler, a whole filter approximation, or the final
simulator.

## Generic classical description generation

**Source:** Neil D. Jones, *Computability and Complexity: From a Programming
Perspective*, Proposition 21.6.1, Lemma 21.6.2 and Theorem 21.6.3, printed
pp.327–329, [author's PDF](https://hjemmesider.diku.dk/~neil/comp2book2007/book-whole.pdf).

These results concern binary arithmetic, bit-query versus polynomial-output
logspace computation, and closure of deterministic logspace functions under
composition. The explicit interfaces in `CircuitRecipe`,
`RepresentedAnalytic`, `UniformCompilation`, `FourierCompilation` and the
simulator uniformity modules specialize those generic facts to fixed string
encodings, polynomial counters, array lookup, list recomputation and a fixed
instruction byte grammar. They quantify over classical strings/natural
numbers. They do not supply quantum matrices, quantum correctness or the
P25 simulator's uniformity as a conclusion.

The final concrete interface is `Paper25.ClassicalSimulationInputs G` in
`SimulatorExternalInputs.lean`. Its twelve fields are `lists`, `instructions`,
`arithmetic`, `unaryPrefix`, `queries`, `source`, `sourceOperations`, `binary`,
`vectors`, `shift`, `rational`, and `recipes`. All source parser fields only
read literal fields of the original source grammar. `NatVectorParsing.entry`
only reads an indexed unary natural from a literal vector; it does not perform
wire placement. Binary-to-unary conversion has explicit unary range padding.
Unary division/modulo use polynomial bounded counters; no stronger binary
division or canonical-fraction algorithm is silently inferred from Jones.
The separate QFT counter grammar and clock-specific queries are derived here
from these generic inputs, rather than retained as additional assumptions.

The missing formalization is the generic simulation/composition of finite
transducers and standard recoding of polynomial-sized descriptions. The
actual P25 list transformations, the fixed Fourier double loop, source gate
expansion, clock, history, walk, filter, wire placement and readout are
constructed separately. Every caller-specific numeric query is required to be derived from these
generic interfaces and the given source family's generator. The final complete
source-to-target theorem must retain no component-generator premise.

## Fixed ideal QFT network identity

**Source:** Cleve, Ekert, Macchiavello and Mosca, *Quantum Algorithms
Revisited*, quant-ph/9708016, §4, Fig.5 and equations (4.1)–(4.6), printed
pp.8–9, [primary PDF](https://arxiv.org/pdf/quant-ph/9708016).

`OperationalModel.FourierCompilation.StandardQFTCorrectness.network_correct`
is limited to the already specified ideal network: increasing physical wire
index, Hadamard on each wire, controlled phase `pi/2^(j-i)` for each later
wire, followed by reversing output wire order. It identifies that network
with the positive, normalized Fourier matrix at the file's binary indexing.
The identity's formal derivation is absent.

The actual rational-angle native network, three-CNOT swaps, inverse/data
variants, quadratic gate count, approximation bound, precision choice,
counter enumeration and complete generated description are proved here.
Phase-estimation and P25-filter correctness are not inputs of this interface.

## Model convention, rather than an exempt P25 theorem

The source paper explicitly fixes the same effective elementary-gate
convention for source and simulator (the source paper, introduction's gate-convention
paragraph and Appendix A.2). `EffectiveGateSet` requires constant locality,
unitarity and an actual finite-transducer entry-approximation certificate.
`LocalCompilation.GateConvention` and
`UniformCompilation.PrimitiveDescriptionConvention` make the additional
single-primitive operations and their description machines explicit: H, X,
CNOT, raw rational phases/rotations, adjoint, complex conjugate, control and
phase-sensitive pattern control. They are assumptions of the stated model.
They do not accept a whole source history, filter or simulator as an argument.

Barenco et al., *Elementary gates for quantum computation*, Physical Review A
52 (1995), [primary preprint](https://arxiv.org/pdf/quant-ph/9503016),
Corollary 7.6, gives the familiar ancilla-free polynomial implementation of
multi-controlled two-dimensional unitaries. It is context for the primitive
convention, not a cited theorem asserting P25's whole compiler or logspace
uniformity. No broad compiler-existence exemption is claimed.

## Unused literature comparison

Fefferman–Remscrim measurement elimination, Gilyén–Su–Low–Wiebe block-encoding
and QSVT results, and later DQC1 trace algorithms are not used to replace the
P25-specific proofs. In particular, no external input is a whole catalytic
simulation theorem or a whole-filter implementation certificate.
