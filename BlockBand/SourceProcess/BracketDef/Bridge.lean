module

public import BlockBand.SourceProcess.BracketDef.Interface
public import BlockBand.SourceProcess.ComplexCutoff.BracketPin

/-!
# Agreement of the two forms of `StoppedBracketCoupling`

The statement `BracketDef.StoppedBracketCoupling`, stated with minimal imports, is definitionally
the statement `ComplexCutoff.StoppedBracketCoupling`.
-/

set_option autoImplicit false

@[expose] public section

namespace BlockBand.SourceProcess.BracketDef

/-- The two statements are the same `Prop`, by unfolding. -/
theorem stoppedBracketCoupling_iff :
    StoppedBracketCoupling ↔ ComplexCutoff.StoppedBracketCoupling := Iff.rfl

/-- A proof of `BracketDef.StoppedBracketCoupling` gives `ComplexCutoff.StoppedBracketCoupling`. -/
theorem stoppedBracketCoupling_of (h : StoppedBracketCoupling) :
    ComplexCutoff.StoppedBracketCoupling := stoppedBracketCoupling_iff.1 h

end BlockBand.SourceProcess.BracketDef
