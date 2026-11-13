module

public import BlockBand.Internal.Contracts.TransmissionStatements

/-!
# Bulk-uniform passive covariance

`PassiveCovarianceBulk`: the bound of `PassiveCovarianceContract` with `C, W₀` uniform on
`bulkInterval κ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.CovarianceBulk

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ComplexConjugate ComplexOrder Matrix

/-- **Bulk-uniform passive covariance**: the bound of `PassiveCovarianceContract` with `C, W₀`
uniform on `bulkInterval κ`. -/
def PassiveCovarianceBulk : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
      ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
        ∀ s : ℂ, IsStationaryJet b E s → ∀ X : Matrix (Fin W) (Fin W) ℂ,
        (passiveY X).PosSemidef → ∀ v₁ v₂ v₃ v₄ : Fin W → ℂ,
        let T := passiveTransmission b E X
        let f := passiveF b E X
        let I : Matrix (Fin W) (Fin W) ℂ := 1
        ‖bilinearCovariance (freshLaw W b) (freshU b E X) v₁ v₂ v₃ v₄ -
            ((((transportD0 b E / (2 * W) : ℝ)) : ℂ) *
                (crossedTensor v₁ v₂ v₃ v₄ I (I - T) + crossedTensor v₁ v₂ v₃ v₄ (I - T) I) +
              sigmaMinus b E s / W * crossedTensor v₁ v₂ v₃ v₄ f f +
              conj (sigmaMinus b E s) / W * crossedTensor v₁ v₂ v₃ v₄ fᴴ fᴴ)‖ ≤
          C * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ *
            (jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W)) *
            fourNorm v₁ v₂ v₃ v₄

end BlockBand.Transmission.CovarianceBulk
