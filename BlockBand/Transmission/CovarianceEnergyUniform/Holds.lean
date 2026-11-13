module

public import BlockBand.Internal.Contracts.TransmissionUniform4
public import BlockBand.Transmission.PassiveCovarianceBulk.Holds
public import BlockBand.Transmission.PassiveCovariance.StationaryJet

/-!
# Energy-uniform passive covariance bound

Proves `PassiveCovarianceEnergyUniformContract` from the Gaussian absorption, `L^p` gradient and
Poincaré inputs, and shows that it implies `PassiveCovarianceContract` at every bulk energy
`E ∈ (-2, 2)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.CovarianceEnergyUniform

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.TransmissionUniform4

/-- **`PassiveCovarianceEnergyUniformContract`**: the passive covariance bound uniformly on
compact bulk sets, from the input hypotheses. -/
theorem passiveCovarianceEnergyUniform_holds (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) :
    PassiveCovarianceEnergyUniformContract :=
  CovarianceBulk.passiveCovarianceBulk_holds hGA hLp hP

/-- A bulk energy `E ∈ (-2, 2)` lies in `bulkInterval κ` for `κ = min(E+2, 2-E) > 0`. -/
theorem mem_bulkInterval_min {E : ℝ} (h1 : -2 < E) (h2 : E < 2) :
    0 < min (E + 2) (2 - E) ∧ E ∈ bulkInterval (min (E + 2) (2 - E)) := by
  refine ⟨lt_min (by linarith) (by linarith), ?_, ?_⟩
  · have := min_le_left (E + 2) (2 - E); linarith
  · have := min_le_right (E + 2) (2 - E); linarith

/-- The energy-uniform clause implies the fixed-`E` `PassiveCovarianceContract`. -/
theorem passiveCovariance_of_energyUniform (h : PassiveCovarianceEnergyUniformContract) :
    PassiveCovarianceContract := by
  intro b hb0 hb E h1 h2
  obtain ⟨hκ, hE⟩ := mem_bulkInterval_min h1 h2
  refine ⟨PassiveCovariance.stationaryJet_exists hb0 hb h1 h2, fun s hs => ?_⟩
  obtain ⟨C, W₀, hC⟩ := h b hb0 hb _ hκ
  exact ⟨C, W₀, fun W hW => hC W hW E hE s hs⟩

end BlockBand.Transmission.CovarianceEnergyUniform
