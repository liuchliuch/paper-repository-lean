import Paper19.UniformReductions
import Paper19.NatIsomorphism

namespace Paper19
open UniformOracleComputable

noncomputable def forwardNatProgram (T : Tree) (o : Stream) (n : ℕ) : ℕ :=
  rankInDomain T (rawIsoProgram o (enumerateDomain T n))

theorem forwardNat_uniform (T : Tree) (hT : ComputablePred T.mem) :
    UniformOracleComputable (forwardNatProgram T) :=
  (base (rankInDomain_computable T hT)).comp
    (rawIso_uniform.comp (base (enumerateDomain_computable T hT)))

theorem forwardNat_correct {T : Tree} {o : Stream} (ho : T.IsPath o) (n : ℕ) :
    forwardNatProgram T o n = (PresentationIso.toNatIso (a := false) (b := true) (pathToPresentation ho)).map n := by
  obtain ⟨x,rfl⟩ := (carrierEquivNat T).surjective n
  simp only [forwardNatProgram,enumerate_equiv,rawIsoProgram_correct ho]
  change carrierEquivNat T ((pathToPresentation ho).map x) = _
  simp only [PresentationIso.toNatIso,Equiv.trans_apply,Equiv.symm_apply_apply]

noncomputable def rawFromNatProgram (T : Tree) (o : Stream) (code : ℕ) : ℕ :=
  enumerateDomain T (o (rankInDomain T code))

theorem rawFromNat_uniform (T : Tree) (hT : ComputablePred T.mem) :
    UniformOracleComputable (rawFromNatProgram T) :=
  (base (enumerateDomain_computable T hT)).comp
    (query.comp (base (rankInDomain_computable T hT)))

noncomputable def backwardNatProgram (T : Tree) (o : Stream) : Stream :=
  backwardIsoProgram (rawFromNatProgram T o)

theorem backwardNat_uniform (T : Tree) (hT : ComputablePred T.mem) :
    UniformOracleComputable (backwardNatProgram T) :=
  backwardIso_uniform.substitute (rawFromNat_uniform T hT)

@[simp] theorem rawCode_equiv_symm (T : Tree) (n : ℕ) :
    rawCode ((carrierEquivNat T).symm n).val = enumerateDomain T n :=
  rawCode_rawDecode T (enumerateDomain T n)

theorem backwardNat_correct {T : Tree} (f : NatIso (natModel T false) (natModel T true)) :
    T.IsPath (backwardNatProgram T f.map) := by
  let c : PresentationIso T (Carrier.zeroVec 0) Carrier.rootOne := f.toCarrier
  have hquery (n : ℕ) : rawFromNatProgram T f.map (zeroCode n) = isoOracle c (zeroCode n) := by
    change rawFromNatProgram T f.map (rawCode (Carrier.zeroVec n : Carrier T).val) =
      isoOracle c (rawCode (Carrier.zeroVec n : Carrier T).val)
    rw [isoOracle_valid c (Carrier.zeroVec n)]
    change enumerateDomain T (f.map (carrierEquivNat T (Carrier.zeroVec n))) =
      rawCode ((carrierEquivNat T).symm (f.map (carrierEquivNat T (Carrier.zeroVec n)))).val
    exact (rawCode_equiv_symm T _).symm
  have hg : groupFromIsoProgram (rawFromNatProgram T f.map) = groupFromIsoProgram (isoOracle c) := by
    funext n
    unfold groupFromIsoProgram
    rw [hquery n]
  change T.IsPath (originalPathProgram (groupFromIsoProgram (rawFromNatProgram T f.map)))
  rw [hg]
  exact backwardIso_correct c

end Paper19
