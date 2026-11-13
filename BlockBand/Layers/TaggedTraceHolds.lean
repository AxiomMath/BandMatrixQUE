module

public import BlockBand.Layers.TaggedLambda

/-!
# The tagged-trace lemma: assembled constructors

The tagged-trace lemma, stated as `TaggedTraceStatement`, from `ConditionalBlockGUECount` and
`GaussianLpGradient` alone:

* `tgtDecayBound_holds`: the tagged decay bound (`TgtDecayBound`), i.e. `tgtDecayBound_of_fet`
  with the residual pair bound `fetResidualBound_holds`;
* `taggedTrace_holds`: all clauses of `TaggedTraceStatement` (the tagged base case for `ε` and `λ`,
  the tagged decay bound, `∂_{ξ_e} = 0`), i.e. `taggedTrace_of_fet` with `fetResidualBound_holds`.

Law: every edge splitting `IsCenterSplitting X G` of an extension of the exact physical ring (the law
of `H^{(e)} = H - G_e`); domain `4 ≤ n ≤ TW`, `W > W₀`, deterministic `E ∈ bulkInterval κ`, edges
`g ≠ e`, blocks `k ∈ {e, e+1}`; norms `L^q(X.P)`, `q ≥ 1`; quantifier order and uniformity as in
`TaggedTraceStatement` (`b, κ, T` first, then `ρ < 1`, then for each `q` the constants `C, W₀`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open BlockBand.Internal.Contracts.Inputs (GaussianLpGradient ConditionalBlockGUECount)

/-- **The tagged decay bound** (`TgtDecayBound`) from `ConditionalBlockGUECount` and
`GaussianLpGradient`: `tgtDecayBound_of_fet` with `fetResidualBound_holds`. -/
theorem tgtDecayBound_holds (hcount : ConditionalBlockGUECount) (hgrad : GaussianLpGradient) :
    TgtDecayBound :=
  tgtDecayBound_of_fet hcount hgrad (fetResidualBound_holds hcount hgrad)

/-- **The tagged-trace lemma** (`TaggedTraceStatement`) from `ConditionalBlockGUECount` and
`GaussianLpGradient`: `taggedTrace_of_fet` with `fetResidualBound_holds`. Law, domain, norms and
quantifiers: those of `TaggedTraceStatement`. -/
theorem taggedTrace_holds (hcount : ConditionalBlockGUECount) (hgrad : GaussianLpGradient) :
    TaggedTraceStatement :=
  taggedTrace_of_fet hcount hgrad (fetResidualBound_holds hcount hgrad)

end BlockBand.Layers
