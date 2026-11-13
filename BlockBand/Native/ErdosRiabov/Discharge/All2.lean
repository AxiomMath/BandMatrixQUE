module

public import BlockBand.Native.ErdosRiabov.Discharge.All
public import BlockBand.Native.ErdosRiabov.Discharge.QV
public import BlockBand.Native.ErdosRiabov.Discharge.Forcing
public import BlockBand.Native.ErdosRiabov.Discharge.MBoundAux

/-!
# Unconditional corollaries: second part

Collects further unconditional corollaries:
* the quadratic-variation estimates, with `Split.ExplicitShortStatement` discharged by
  `MTerms.explicitShort_holds`;
* the forcing estimates, with `Split.CyclicStatement` discharged by `MTerms.cyclic_holds` (the
  `M`-bound and a priori hypotheses of `forcing_av` are kept);
* the twenty intermediate lemmas of the `M`-bounds, with `MBAlg` discharged by
  `Discharge.mbAlg_holds`.
-/

set_option autoImplicit false

@[expose] public section
