import Paper19.Presentation
import Paper19.PathIso
import Paper19.Coding

namespace Paper19

/-- Uniform path-to-isomorphism program. The proof argument is erased. -/
def pathToPresentation {T : Tree} {f : Stream} (hf : T.IsPath f) :
    PresentationIso T (Carrier.zeroVec 0) Carrier.rootOne :=
  validIsoToPresentation (validIsoOfPath (path_to_STree hf))

/-- Uniform extraction program: evaluate the isomorphism at the zero
vectors, follow least children in the finite fibres, then decode the binary
path. All choices in this program are finite, executable searches. -/
def presentationToPath {T : Tree}
    (f : PresentationIso T (Carrier.zeroVec 0) Carrier.rootOne) : Stream :=
  let c := f.toValidIso
  let g := pathOfCoherent c.val c.property
  pathOfQT (streamBits g) (streamBounds g)

theorem presentationToPath_correct {T : Tree}
    (f : PresentationIso T (Carrier.zeroVec 0) Carrier.rootOne) :
    T.IsPath (presentationToPath f) :=
  path_from_STree (isPath_of_coherent f.toValidIso.val f.toValidIso.property)

/-- Theorem 1(2), for the genuine finite-language presentations. -/
theorem theorem1_isomorphic (T : Tree) :
    Nonempty (PresentationIso T (Carrier.zeroVec 0) Carrier.rootOne) ↔ ∃ f, T.IsPath f :=
  ⟨fun ⟨f⟩ => ⟨presentationToPath f, presentationToPath_correct f⟩,
   fun ⟨f, hf⟩ => ⟨pathToPresentation hf⟩⟩

end Paper19
