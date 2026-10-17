import Paper25.ClassicalDataCompilation
import Paper25.FourierCompilation

/-! Derive the QFT counter grammar from the common classical arithmetic
interface; no separate Fourier-specific arithmetic assumption is needed. -/
noncomputable section
namespace Paper25.OperationalModel.UniformCompilation

lemma fourier_pair_unprefix (classical : FLListClosure) (parsing : UnaryPrefixParsing) :
    LogspaceComputes FourierCompilation.unaryPairInput natPairInput := by
  let recode (p : ℕ × ℕ) : ℕ × Input := ((encodeNat p.1).length,natPairInput p)
  have he : (fun p => unaryPrefixInput (recode p)) = FourierCompilation.unaryPairInput := by
    funext p
    simp only [recode,unaryPrefixInput,natPairInput,FourierCompilation.unaryPairInput,
      List.append_assoc]
  have h : LogspaceComputes FourierCompilation.unaryPairInput
      (fun p => unaryPrefixInput (recode p)) := by
    rw [he]
    exact classical.strings.identity _

  exact classical.strings.compose FourierCompilation.unaryPairInput unaryPrefixInput recode
    Prod.snd h parsing.rest

def fourierArithmetic (classical : FLListClosure) (arithmetic : NatArithmeticDescription)
    (parsing : UnaryPrefixParsing) : FourierCompilation.UnaryCounterArithmetic where
  add := classical.strings.compose FourierCompilation.unaryPairInput natPairInput id _
    (fourier_pair_unprefix classical parsing) arithmetic.add
  sub := classical.strings.compose FourierCompilation.unaryPairInput natPairInput id _
    (fourier_pair_unprefix classical parsing) arithmetic.sub
  half := nat_div classical arithmetic encodeNat id (fun _ => 2)
    (classical.strings.identity _) (nat_const classical _ 2)

end Paper25.OperationalModel.UniformCompilation
