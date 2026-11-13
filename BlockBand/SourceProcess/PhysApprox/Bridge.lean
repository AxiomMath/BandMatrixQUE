module

public import BlockBand.SourceProcess.PhysApprox.Statement
public import BlockBand.SourceProcess.ComplexFreq.Interface

/-!
# Two forms of the frequent-`h` physical approximation

`complexFreq_iff`: the statement `ComplexPhysicalApproximationFreq` of this directory is, by
definition, `ComplexFreq.ComplexPhysicalApproximationFreq`.
-/

set_option autoImplicit false

@[expose] public section

namespace BlockBand.SourceProcess.PhysApprox

/-- The frequent-`h` statement of this namespace is, by definition,
`ComplexFreq.ComplexPhysicalApproximationFreq`. -/
theorem complexFreq_iff :
    ComplexPhysicalApproximationFreq ↔
      BlockBand.SourceProcess.ComplexFreq.ComplexPhysicalApproximationFreq :=
  Iff.rfl

end BlockBand.SourceProcess.PhysApprox
