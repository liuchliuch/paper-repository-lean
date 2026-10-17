import Paper19.UniformReductions

namespace Paper19
open UniformOracleComputable
open scoped symmDiff

def singletonSProgram (o : Stream) (n : ℕ) : ℕ :=
  @Encodable.encode (Finset Node) (Primcodable.toEncodable) ({streamPrefix o n} : Finset Node)

theorem singletonS_uniform : UniformOracleComputable singletonSProgram := by
  have hc : Computable (fun σ : Node => @Encodable.encode (Finset Node) (Primcodable.toEncodable)
      ({σ} : Finset Node)) := Primrec.encode.to_comp.comp FiniteCoding.singleton_computable
  exact (base hc).comp prefix_uniform

def sIsoProgram (o : Stream) (code : ℕ) : ℕ :=
  if code%2=0 then code else
    2 * Nat.pair (Nat.unpair (code/2)).1
      (translateCode (singletonSProgram o) (Nat.unpair (code/2))) + 1

theorem sIso_uniform : UniformOracleComputable sIsoProgram := by
  have hp : Primrec (fun code : ℕ => Nat.unpair (code/2)) :=
    Primrec.unpair.comp (Primrec.nat_div.comp Primrec.id (Primrec.const 2))
  have hv := (translate_uniform.substitute singletonS_uniform).comp (base hp.to_comp)
  have hn : UniformOracleComputable (fun _ (code : ℕ) => (Nat.unpair (code/2)).1) :=
    base (Primrec.fst.comp hp).to_comp
  have he : Primrec (fun p : ℕ × ℕ => 2 * Nat.pair p.1 p.2 + 1) :=
    Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec₂.natPair.comp Primrec.fst Primrec.snd))
  have ht : UniformOracleComputable (fun _ (code : ℕ) => decide (code%2=0)) :=
    base (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2)) (Primrec.const 0)).decide.to_comp
  exact (cond ht id ((base he.to_comp).comp (hn.pair hv))).of_eq (by simp [sIsoProgram,Bool.cond_decide])

theorem sIsoProgram_correct {T : Tree} {o : Stream} (ho : (STree T).IsPath o) (x : Carrier T) :
    sIsoProgram o (rawCode x.val)=rawCode ((validIsoToPresentation (validIsoOfPath ho)).map x).val := by
  rcases x with ⟨x,hx⟩
  cases x with
  | idx k => simp [sIsoProgram,rawCode,validIsoToPresentation,translationIso,Carrier.translate,translateDom]
  | vec n F =>
    change sIsoProgram o (rawCode (Dom.vec n F : Dom T)) = rawCode (Dom.vec n (F ∆ {streamPrefix o n}) : Dom T)
    simp [sIsoProgram,rawCode,encIndex,translateCode,singletonSProgram,FiniteCoding.symmDiffCodes]

def sPathProgram (o : Stream) : Stream := liftPathProgram (groupFromIsoProgram o)

theorem sPath_uniform : UniformOracleComputable sPathProgram := liftPath_uniform.substitute groupFromIso_uniform

theorem sPath_correct {T : Tree} (f : PresentationIso T (Carrier.zeroVec 0) Carrier.rootOne) :
    (STree T).IsPath (sPathProgram (isoOracle f)) := by
  simp only [sPathProgram,groupFromIso_correct]
  rw [liftPathProgram_correct f.toValidIso.val f.toValidIso.property]
  exact isPath_of_coherent f.toValidIso.val f.toValidIso.property

def Lemma5UniformStatement : Prop :=
  UniformOracleComputable sIsoProgram ∧ UniformOracleComputable sPathProgram ∧
  (∀ (T : Tree) (o : Stream) (ho : (STree T).IsPath o) (x : Carrier T),
    sIsoProgram o (rawCode x.val)=rawCode ((validIsoToPresentation (validIsoOfPath ho)).map x).val) ∧
  (∀ (T : Tree) (f : PresentationIso T (Carrier.zeroVec 0) Carrier.rootOne),
    (STree T).IsPath (sPathProgram (isoOracle f)))

theorem lemma5_uniform : Lemma5UniformStatement :=
  ⟨sIso_uniform,sPath_uniform,fun _ _ ho x => sIsoProgram_correct ho x,fun _ f => sPath_correct f⟩

end Paper19
