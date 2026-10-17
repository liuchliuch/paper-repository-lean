import Paper19.CodedPresentation

namespace Paper19
open scoped symmDiff

def decodeVector (code : ℕ) : ℕ × Finset Node := decodeIndex (code/2)

theorem decodeVector_primrec : Primrec decodeVector :=
  decodeIndex_primrec.comp (Primrec.nat_div.comp Primrec.id (Primrec.const 2))

def codedSucc (code : ℕ) : ℕ := if code%2=0 then 2*(code/2+1) else code

def codedLevel (code : ℕ) : ℕ := if code%2=0 then code else 2*(decodeVector code).1

def codedProj (T : Tree) (code : ℕ) : ℕ :=
  if code%2=0 then code else
    let (n,F) := decodeVector code
    if n=0 then code else 2 * encIndex (n-1) (proj T (n-1) F) + 1

theorem codedSucc_computable : Computable codedSucc := by
  exact (Primrec.ite
    (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2)) (Primrec.const 0))
    (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.succ.comp
      (Primrec.nat_div.comp Primrec.id (Primrec.const 2)))) Primrec.id).to_comp

theorem codedLevel_computable : Computable codedLevel := by
  exact (Primrec.ite
    (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2)) (Primrec.const 0))
    Primrec.id (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.fst.comp decodeVector_primrec))).to_comp

theorem codedProj_computable (T : Tree) : Computable (codedProj T) := by
  have hn := Primrec.pred.comp (Primrec.fst.comp decodeVector_primrec)
  have hf := Primrec.snd.comp decodeVector_primrec
  have hp := (FiniteCoding.proj_computable T).comp (hn.pair hf).to_comp
  have hi := encIndex_primrec.to_comp.comp (hn.to_comp.pair hp)
  have hv := Primrec.succ.to_comp.comp
    (Primrec.nat_mul.to_comp.comp (Computable.const 2) hi)
  have hzero : ComputablePred (fun code : ℕ => code%2=0) :=
    (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2)) (Primrec.const 0)).computablePred
  have hnzero : ComputablePred (fun code : ℕ => (decodeVector code).1=0) :=
    (Primrec.eq.comp (Primrec.fst.comp decodeVector_primrec) (Primrec.const 0)).computablePred
  exact hzero.ite Computable.id (hnzero.ite Computable.id hv)

@[simp] theorem codedSucc_correct {T : Tree} (x : Dom T) : codedSucc (rawCode x) = rawCode (Dom.succ x) := by
  cases x <;> simp [codedSucc,rawCode,Dom.succ]

@[simp] theorem codedLevel_correct {T : Tree} (x : Dom T) : codedLevel (rawCode x) = rawCode (Dom.levelOf x) := by
  cases x <;> simp [codedLevel,rawCode,decodeVector,Dom.levelOf]

@[simp] theorem codedProj_correct (T : Tree) (x : Dom T) : codedProj T (rawCode x) = rawCode (Dom.projD x) := by
  cases x with
  | idx k => simp [codedProj,rawCode,Dom.projD]
  | vec n F => cases n <;> simp [codedProj,rawCode,decodeVector,Dom.projD]

def codedD (T : Tree) (p : ℕ × (ℕ × ℕ)) : Bool :=
  let K := decodeVector p.1
  let X := decodeVector p.2.1
  let Y := decodeVector p.2.2
  decide (p.1%2=0 ∧ p.2.1%2≠0 ∧ p.2.2%2≠0 ∧ K.1=X.1 ∧ Y.1=X.1 ∧
    GMem T X.1 K.2 ∧ Y.2 = X.2 ∆ K.2)

open scoped symmDiff

theorem codedD_computable (T : Tree) (hT : ComputablePred T.mem) : Computable (codedD T) := by
  let K := fun p : ℕ × (ℕ × ℕ) => decodeVector p.1
  let X := fun p : ℕ × (ℕ × ℕ) => decodeVector p.2.1
  let Y := fun p : ℕ × (ℕ × ℕ) => decodeVector p.2.2
  have hk : Primrec K := decodeVector_primrec.comp Primrec.fst
  have hx : Primrec X := decodeVector_primrec.comp (Primrec.fst.comp Primrec.snd)
  have hy : Primrec Y := decodeVector_primrec.comp (Primrec.snd.comp Primrec.snd)
  have htK : PrimrecPred (fun p : ℕ × (ℕ × ℕ) => p.1%2=0) :=
    Primrec.eq.comp (Primrec.nat_mod.comp Primrec.fst (Primrec.const 2)) (Primrec.const 0)
  have htX : PrimrecPred (fun p : ℕ × (ℕ × ℕ) => p.2.1%2≠0) :=
    (Primrec.eq.comp (Primrec.nat_mod.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 2)) (Primrec.const 0)).not
  have htY : PrimrecPred (fun p : ℕ × (ℕ × ℕ) => p.2.2%2≠0) :=
    (Primrec.eq.comp (Primrec.nat_mod.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 2)) (Primrec.const 0)).not
  have hnK := (Primrec.eq.comp (Primrec.fst.comp hk) (Primrec.fst.comp hx)).computablePred
  have hnY := (Primrec.eq.comp (Primrec.fst.comp hy) (Primrec.fst.comp hx)).computablePred
  have hG := (GMem_computable T hT).comp' ((Primrec.fst.comp hx).pair (Primrec.snd.comp hk)).to_comp
  have hdiff := FiniteCoding.symmDiff_computable.comp ((Primrec.snd.comp hx).pair (Primrec.snd.comp hk)).to_comp
  have he := (Primrec.eq.decide.to_comp.comp (Primrec.snd.comp hy).to_comp hdiff).computablePred
  have hall := htK.computablePred.and' (htX.computablePred.and' (htY.computablePred.and'
    (hnK.and' (hnY.and' (hG.and' he)))))
  exact hall.decide

theorem codedD_correct {T : Tree} (k x y : Dom T) :
    codedD T (rawCode k,rawCode x,rawCode y)=true ↔ isD k x y := by
  rw [← DAlgorithm_correct T k x y]
  cases k <;> cases x <;> cases y <;>
    simp [codedD,DAlgorithm,rawCode,decodeVector]

end Paper19
