# External dependencies and scope

The final result is to be checked relative to the inputs listed here. No
inhabitant of an external-input proposition is asserted by the production
sources. An external input therefore remains visible in the final theorem's
type. The permitted kernel axioms remain `propext`, `Classical.choice`, and
`Quot.sound`; `sorryAx` is not added to the permitted list.

## JF 23: a nonspherical Galois braided extension

**Published source.** T. Johnson–Freyd, *Schopieray's Galois-modular extension
conjecture*, [arXiv:2601.23192v1](https://arxiv.org/abs/2601.23192v1), Proposition
2.3. The primary TeX theorem label is `prop:summarytannakian`.

**Original statement.** Every braided fusion category over the complex numbers
with Tannakian center admits a nondegenerate braided extension whose
centralizer is integral. The source need not be pseudounitary. The conclusion
does not supply a pivotal structure on the ambient category or compatibility
with a prescribed source structure.

**Lean interface.** `Paper18.External.JohnsonFreyd23At` (with canonical-size
abbreviation `Paper18.External.JohnsonFreyd23`), defined in
`Paper18/External/JohnsonFreyd23.lean`, quantifies over an actual complex-linear
braided fusion category, a finite semisimple skeleton, a group, and an actual
`TannakianCenter`. It returns `Nonempty (GaloisBraidedExtension C)`. The latter
contains the actual ambient fusion category, a complex-linear fully faithful
braided tensor functor, actual Müger nondegeneracy, and intrinsic integrality
of the actual centralizer. Its universe bounds describe an essentially small
presentation and are bookkeeping, rather than a new mathematical assumption.

**Uses in this paper.** The first use supplies the initial ambient category
in equation (3.1). A second use supplies a braided extension of the positive
sign kernel in Case 2. In the second use, the separately proved literal JF
Proposition 2.4 and positivity uniqueness construct the positive pivotal
structure and its compatibility with the source. JF 23 itself is not silently
strengthened to a spherical extension theorem.

**Formalization status.** The type of this external result is formalized. No
proof of its universal existence assertion is supplied. The actual graph,
module-category, crossed-gauging, finite-cohomology, and relative-center
results previously developed in an attempt to prove it remain available as
genuine independent proofs; they are not represented as a completed proof of
JF 23.

## This paper's own required arguments

The following remain production proofs, rather than external assumptions:
the categorical Lemma 2.1 including its inverse-twist constraint; the
fixed-boundary classification for every actual minimal C 2 extension with
the specified boundary isomorphism retained; the negative-dimensional boson
exclusion and prescribed spherical enhancement; the C 2 cochain calculations;
the preliminary centralizer calculation after sphericalization; both actual
integrality branches; the diagonal local-module construction and its fully
faithful spherical embedding; and the pointed obstruction in Appendix B.

## ENO: realization after trivializing the relative fourth obstruction

**Published source.** P. Etingof, D. Nikshych, and V. Ostrik, *Fusion categories
and homotopy theory*, Quantum Topology 1 (2010), 209–273,
[arXiv:0909.3140](https://arxiv.org/abs/0909.3140), Theorem 5.2, Propositions
7.3 and 7.5, Proposition 7.8(ii), Sections 7.1–7.2 and 7.5, and Theorem 7.12.
This input is the relative fixed-action existence formulation of those
results, rather than this paper's Lemma A.1.

**Original hypotheses and quantifiers.** Fix a nondegenerate complex braided
fusion category and its specified complex-linear braided categorical action
of C₂. The categorical action includes its coherence, hence the lifting data
through the second homotopy stage. There is a normalized fourth obstruction
cocycle with trivial complex-unit coefficients. Every normalized third
cochain whose coboundary is that cocycle realizes the specified action as a
faithfully graded braided crossed fusion extension, with the neutral
category and its action identified with the specified ones.

**Lean interface.** `Paper18.External.ENOExtensionTheory.ObstructionRealization`
in `Paper18/External/ENOExtensionTheory.lean` is the explicit proposition
`∃ ω : FourCocycle C2 ℂˣ, ∀ ψ : ThreeCochain C2 ℂˣ, dThree ψ.val = ω.val →
Nonempty (FaithfulCrossedRealization A)`. The source fusion structures,
nondegeneracy, and all additive, linear, braided and monoidal action
structures are explicit parameters. The output contains actual category
structures, actual crossed braiding, faithful grading, and an actual neutral
action intertwiner. It contains no pivotal structure, minimal extension,
nondegeneracy of equivariantization, or boundary-classification conclusion.
No inhabitant of this proposition is asserted.

**Own-paper use.** `c2_fourCocycle_is_coboundary` constructs the primitive in
Lean. `FixedBoundary.MinimalExistence.minimalExtension_exists` constructs the
actual equivariantization and its embedding of the original source, proves
nondegeneracy, and proves its dimension is twice the source dimension.
`lemmaA1_relative_to_ENO` combines this existence with the internally proved
universal specified-boundary classification. The prescribed spherical
structure in `proposition2_2_relative_to_ENO` is constructed from that actual
classification and the internally proved negative-boson exclusion.

DGNO, *On braided fusion categories I*, Theorem 4.44 is the published
2-equivalence referenced by Appendix A. The actual de-equivariantization,
descent and gauging steps needed here have been proved in the project, so
that correspondence is not an additional external-input proposition.

The existence of a minimal extension is therefore a derived conclusion
relative to the precise ENO realization input. The entire statement of
this paper's own Lemma A.1 has not been assumed as an external result.


## Secondary Galois-orbit consequence

The implication from the proved integral-centralizer output to a union of
ambient Galois orbits is the separately cited result of Plavnik, Schopieray,
Yu and Zhang, *Modular tensor categories, subcategories, and Galois orbits*,
Transform. Groups 29 (2024), 1623–1648,
[arXiv:2111.05228](https://arxiv.org/abs/2111.05228),
[DOI](https://doi.org/10.1007/s00031-022-09787-9). It requires a full fusion
subcategory of a modular category and identifies Galois closure of its
simple classes with integrality of its centralizer. The actual modular-data
Galois action and this criterion are not formalized here. This remains the
previously authorized secondary-consequence exemption; it is not an input
to the actual integral-centralizer main theorem.



The shared release tooling installs the pinned official Comparator. Comparator challenge modules may contain specification placeholders; these are isolated from production proofs. Negative controls intentionally contain an added premise or an illegal axiom and are verification fixtures. No new axioms or proof placeholders were introduced by release curation.
