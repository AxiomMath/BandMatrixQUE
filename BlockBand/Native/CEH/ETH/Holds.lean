module

public import BlockBand.Native.CEH.ETH.ZigClosure

/-!
# CEH ETH: `externalETH_holds`

CEH = Cipolloni–Erdős–Henheik, arXiv:2607.02446v2 (ETH for deformed Wigner matrices, the
fixed-point `θ = 1` bound (4.4) for `⟨Im G₁ A° Im G₂ A°*⟩` transported to `gueLawFamily`).

**Main result** (`BlockBand.Native.CEH.externalETH_holds`): the statement
`BlockBand.Internal.Contracts.Inputs.ExternalETH`, with no hypotheses. It is
`externalETH_of_zigImChainBound` (`LawThetaOne`: law transport to the concrete Brownian space
and `externalETH_of_fixedPointThetaOne`) applied to `zigImChainBound_holds` (`ZigClosure`).
`ZigImChainBound` is proved, not assumed.

This is a different declaration from `BlockBand.Adapters.CEH.externalETH_holds`.
-/

set_option autoImplicit false

@[expose] public section

namespace BlockBand.Native.CEH

/-- **`Inputs.ExternalETH`**, with no hypotheses: `externalETH_of_zigImChainBound` applied to
the proved `zigImChainBound_holds`. -/
theorem externalETH_holds : BlockBand.Internal.Contracts.Inputs.ExternalETH :=
  ETH.externalETH_of_zigImChainBound ETH.zigImChainBound_holds

end BlockBand.Native.CEH
