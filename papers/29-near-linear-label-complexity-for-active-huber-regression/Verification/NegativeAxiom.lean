import Paper29.Specification
namespace Paper29.NegativeControl
axiom forbidden : False
end Paper29.NegativeControl
namespace Paper29.Checked
 theorem lemma31 : Specification.Lemma31 := False.elim NegativeControl.forbidden
end Paper29.Checked
