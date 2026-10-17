import Paper19.UniformIso
import Paper19.CodedPresentation
import Paper19.Reduction
import Paper19.InputTree

namespace Paper19
open UniformOracleComputable
open scoped symmDiff

def rawIsoProgram (o : Stream) (code : ℕ) : ℕ :=
  if code%2=0 then code else
    2 * Nat.pair (Nat.unpair (code/2)).1
      (translateCode (singletonProgram o) (Nat.unpair (code/2))) + 1

theorem rawIso_uniform : UniformOracleComputable rawIsoProgram := by
  have hp : Primrec (fun code : ℕ => Nat.unpair (code/2)) :=
    Primrec.unpair.comp (Primrec.nat_div.comp Primrec.id (Primrec.const 2))
  have hv := (translate_uniform.substitute singleton_uniform).comp (base hp.to_comp)
  have hn : UniformOracleComputable (fun _ (code : ℕ) => (Nat.unpair (code/2)).1) :=
    base (Primrec.fst.comp hp).to_comp
  have he : Primrec (fun p : ℕ × ℕ => 2 * Nat.pair p.1 p.2 + 1) :=
    Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec₂.natPair.comp Primrec.fst Primrec.snd))
  have hvec := (base he.to_comp).comp (hn.pair hv)
  have ht : UniformOracleComputable (fun _ (code : ℕ) => decide (code%2=0)) :=
    base (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2)) (Primrec.const 0)).decide.to_comp
  exact (UniformOracleComputable.cond ht id hvec).of_eq (by simp [rawIsoProgram,Bool.cond_decide])

theorem rawIsoProgram_correct {T : Tree} {o : Stream} (ho : T.IsPath o) (x : Carrier T) :
    rawIsoProgram o (rawCode x.val) = rawCode ((pathToPresentation ho).map x).val := by
  rcases x with ⟨x,hx⟩
  cases x with
  | idx k => simp [rawIsoProgram,rawCode,pathToPresentation,validIsoToPresentation,translationIso,
      Carrier.translate,translateDom]
  | vec n F =>
    change rawIsoProgram o (rawCode (Dom.vec n F : Dom T)) =
      rawCode (Dom.vec n (F ∆ {streamPrefix (pairStream (binaryOf o) (decodeBoundOf o)) n}) : Dom T)
    simp [rawIsoProgram,rawCode,encIndex,translateCode,singletonProgram,
      FiniteCoding.symmDiffCodes,streamPrefix]

/-- Standard total oracle representation of a structure isomorphism on its
computable coded domain; invalid domain codes are assigned zero. -/
def isoOracle {T : Tree} (f : PresentationIso T (Carrier.zeroVec 0) Carrier.rootOne) : Stream :=
  fun code => if h : GoodDom (rawDecode T code) then rawCode (f.map ⟨rawDecode T code,h⟩).val else 0

theorem isoOracle_valid {T : Tree} (f : PresentationIso T (Carrier.zeroVec 0) Carrier.rootOne) (x : Carrier T) :
    isoOracle f (rawCode x.val) = rawCode (f.map x).val := by
  rcases x with ⟨x,hx⟩
  simp [isoOracle,hx]

def zeroCode (n : ℕ) : ℕ := 2 * encIndex n ∅ + 1

theorem zeroCode_primrec : Primrec zeroCode :=
  Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2)
    (encIndex_primrec.comp (Primrec.id.pair (Primrec.const ∅))))

def groupFromIsoProgram (o : Stream) (n : ℕ) : ℕ := (Nat.unpair (o (zeroCode n)/2)).2

theorem groupFromIso_uniform : UniformOracleComputable groupFromIsoProgram := by
  have hp : Primrec (fun n : ℕ => (Nat.unpair (n/2)).2) :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.nat_div.comp Primrec.id (Primrec.const 2)))
  exact (base hp.to_comp).comp (query.comp (base zeroCode_primrec.to_comp))

theorem groupFromIso_correct {T : Tree} (f : PresentationIso T (Carrier.zeroVec 0) Carrier.rootOne) :
    groupFromIsoProgram (isoOracle f) = groupOracle f.toValidIso.val := by
  funext n
  have hz : isoOracle f (zeroCode n) = rawCode (f.map (Carrier.zeroVec n)).val := by
    change isoOracle f (rawCode (Dom.vec n ∅ : Dom T)) = _
    simp [isoOracle,GoodDom,GMem_empty,Carrier.zeroVec,Carrier.vec]
  change (Nat.unpair (isoOracle f (zeroCode n)/2)).2 = _
  rw [hz,f.on_zero]
  simp [rawCode,encIndex,groupOracle,PresentationIso.toValidIso,Carrier.vec]

def backwardIsoProgram (o : Stream) : Stream := originalPathProgram (groupFromIsoProgram o)

theorem backwardIso_uniform : UniformOracleComputable backwardIsoProgram :=
  originalPath_uniform.substitute groupFromIso_uniform

theorem backwardIso_correct {T : Tree} (f : PresentationIso T (Carrier.zeroVec 0) Carrier.rootOne) :
    T.IsPath (backwardIsoProgram (isoOracle f)) := by
  simp only [backwardIsoProgram,groupFromIso_correct,originalPathProgram]
  rw [liftPathProgram_correct f.toValidIso.val f.toValidIso.property]
  exact path_from_STree (isPath_of_coherent f.toValidIso.val f.toValidIso.property)

/-- The two conversions use fixed oracle programs for every input tree,
including the empty tree after its uniform root completion. -/
theorem uniform_reductions_all_inputs :
    UniformOracleComputable rawIsoProgram ∧ UniformOracleComputable backwardIsoProgram ∧
    (∀ (T : InputTree) (o : Stream) (ho : T.IsPath o) (x : Carrier T.rootCompletion),
      rawIsoProgram o (rawCode x.val) =
        rawCode ((pathToPresentation ((T.path_iff_rootCompletion o).mp ho)).map x).val) ∧
    (∀ (T : InputTree) (f : PresentationIso T.rootCompletion (Carrier.zeroVec 0) Carrier.rootOne),
      T.IsPath (backwardIsoProgram (isoOracle f))) :=
  ⟨rawIso_uniform, backwardIso_uniform,
   fun T o ho x => rawIsoProgram_correct ((T.path_iff_rootCompletion o).mp ho) x,
   fun T f => (T.path_iff_rootCompletion _).mpr (backwardIso_correct f)⟩

end Paper19
