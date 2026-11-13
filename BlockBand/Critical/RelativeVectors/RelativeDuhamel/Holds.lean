module

public import BlockBand.Critical.RelativeVectors.RelativeDuhamel.Limit

/-!
# The relative Duhamel identity holds

`relativeDuhamel_holds`: `ComplexAngularContract` implies `RelativeDuhamelStatement N r` for every
`N, r`. The statement quantifies over the reference flow and its event `B` carries simple spectrum
and long gaps almost surely, so no reference-flow statement and no Dyson Brownian motion
hypothesis is used. The proof is `relativeDuhamel_identity` with `ℓ ≥ 1` from `0 < ℓ`; the `g` of
the statement is `backwardFn` by definition.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors.RelativeDuhamel

/-- `ComplexAngularContract` implies the relative Duhamel identity `RelativeDuhamelStatement N r`
for every `N, r`. -/
theorem relativeDuhamel_holds
    (hAng : BlockBand.Internal.Contracts.TransmissionAngular.ComplexAngularContract) :
    ∀ N r, BlockBand.Critical.RelativeVectors.RelativeDuhamelStatement N r := by
  intro N r F a c b₀ ℓ hF _ hac _ hℓ Ωaux _ Paux _ 𝓜 Ξ hMΞ hRF V C h hh hC δ hδ B hB hBae
  exact relativeDuhamel_identity hAng F a c b₀ ℓ hF hac hℓ Paux 𝓜 Ξ hMΞ hRF V C h hh hC δ hδ B
    hB hBae

end BlockBand.Critical.RelativeVectors.RelativeDuhamel
