module

public import BlockBand.Transmission.LawClauses.EntryVarianceBulk
public import BlockBand.Transmission.PassiveCovarianceBulk.Holds

/-!
# `TransmissionLawContract.entryVariance` from the Gaussian inputs

`entryVariance_holds`: given `GaussianAbsorptionContract`, `GaussianLpGradient` and
`GaussianPoincare`, for `0 < b < 1/2` and a bulk margin `κI > 0` there are `d, γ, c > 0` and
`W₀` such that, for `W ≥ W₀`, bulk energies, stationary jets and passive `X` with
`δ₀, δ₁ ≤ d` and `g ≤ γW`, every entry of the centred fresh layer in an eigenbasis of `T` with
`t_i, t_j ≤ 1/2` has variance at least `c/W`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawClauses

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open scoped ComplexConjugate ComplexOrder

/-- **`TransmissionLawContract.entryVariance`** (with exactly the field type), from the input
hypotheses. -/
theorem entryVariance_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI →
    ∃ d γ c : ℝ, 0 < d ∧ 0 < γ ∧ 0 < c ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ E ∈ bulkInterval κI, ∀ s : ℂ, IsStationaryJet b E s →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
        jetDistance0 b E X ≤ d → jetDistance1 b E s X ≤ d →
        conductanceOf (passiveTransmission b E X) ≤ γ * W →
        ∀ (u : Fin W → Fin W → ℂ) (t : Fin W → ℝ),
          IsOrthonormalEigenbasis (passiveTransmission b E X) u t →
          ∀ i j, t i ≤ 1 / 2 → t j ≤ 1 / 2 →
            c / W ≤ ∫ ω, ‖star (u i) ⬝ᵥ ((freshU b E X ω -
                matrixExpect (layerLaw W b .oneBlockOnePort) (freshU b E X)) *ᵥ u j)‖ ^ 2
              ∂layerLaw W b .oneBlockOnePort :=
  entryVariance_of_bulk (CovarianceBulk.passiveCovarianceBulk_holds hGA hLp hP)

end BlockBand.Transmission.LawClauses
