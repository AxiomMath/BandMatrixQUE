module

public import BlockBand.Statements
public import BlockBand.Internal.Composition.QUEUnconditional
public import BlockBand.Internal.Composition.CriticalUnconditional
public import BlockBand.Internal.Composition.EndpointsUnconditional
public import BlockBand.Internal.Composition.CriticalConstruction
public import BlockBand.Internal.Composition.CriticalSourceConstruction

/-!
# Quantum unique ergodicity and the critical crossover for band matrices

The root of the library: the definitions used by the three main statements (`BlockBand.Statements`) and the
modules proving them, `que_unconditional`, `critical_unconditional`, `endpoints_unconditional`, and the companion
`critical_determined_unconditional` for the last sentence of Theorem 1.3.
-/
