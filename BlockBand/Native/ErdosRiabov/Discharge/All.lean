module

public import BlockBand.Native.ErdosRiabov.Discharge.Psi
public import BlockBand.Native.ErdosRiabov.Discharge.Evol
public import BlockBand.Native.ErdosRiabov.Discharge.Circ
public import BlockBand.Native.ErdosRiabov.Discharge.MBound

/-!
# Unconditional corollaries: first part

Collects the corollaries in which the deterministic `M`-term statements of `Split` are
discharged by their proofs in `MTerms`: the control quantities at time zero and the stopping
time, the chain evolution equations, the regularized chains, and the `M`-bounds, including
`mbBounds_joint_uncond` (only `MBCtx`) and `mbBounds_joint_log_uncond(_sum)`.
-/

set_option autoImplicit false

@[expose] public section
