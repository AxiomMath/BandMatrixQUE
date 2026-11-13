module

public import BlockBand.Native.ErdosRiabov.MTerms.Explicit
public import BlockBand.Native.ErdosRiabov.MTerms.Cyclic
public import BlockBand.Native.ErdosRiabov.MTerms.Ward
public import BlockBand.Native.ErdosRiabov.MTerms.Deriv
public import BlockBand.Native.ErdosRiabov.MTerms.Zero

/-!
# The M-term algebra at profile `σ S`

`mTermAlgebra_holds` proves `BlockBand.Native.ErdosRiabov.Split.MTermAlgebra`: the definition
of the `M`-terms, their explicit form, the identities (a)–(c) and the value at `t = 0`, i.e. the
variance-scaling forms of the `M`-recursion, the cyclic and Ward identities and the derivative
formula of Erdős–Riabov (arXiv 2506.06441v1), without the OU term `k/2 · M`.

Setting and hypotheses: exactly those of the five `Split` statements (`n`, a profile `S` with `ProfileHyp`,
`σ ∈ [0,1]`, `‖m i‖ < 1`; Ward also `m i ≠ 0`, `m j ≠ m (j+1)`; `ZeroStatement` none). Deterministic; no
measure.

Components: `explicitShort_holds`, `cyclic_holds`, `ward_holds`, `deriv_holds` and `zero_holds`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Native.ErdosRiabov.MTerms

open BlockBand.Native.ErdosRiabov.Split

/-- The M-term algebra at profile `σ S`. -/
theorem mTermAlgebra_holds : MTermAlgebra :=
  ⟨explicitShort_holds, cyclic_holds, ward_holds, deriv_holds, zero_holds⟩

end BlockBand.Native.ErdosRiabov.MTerms
