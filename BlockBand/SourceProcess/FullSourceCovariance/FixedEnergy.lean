module

public import BlockBand.SourceProcess.FullSourceCovariance.Assembly
public import BlockBand.Transmission.PassiveCovariance.StationaryJet

/-!
# The fixed-`E` full-source covariance statement from the energy-uniform one

`fullSourceCovariance_of_uniform`: the energy-uniform statement
`FullSourceCovarianceEnergyUniformContract` implies the fixed-energy statement
`FullSourceCovarianceContract`, using the bulk margin `min(E + 2, 2 - E)` (`mem_bulk_self`);
`fullSourceCovariance_of_delta` combines this with the two `Δ`-covariance statements.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceCovariance

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.TransmissionUniform2

theorem mem_bulk_self {E : ℝ} (h1 : -2 < E) (h2 : E < 2) :
    0 < min (E + 2) (2 - E) ∧ E ∈ bulkInterval (min (E + 2) (2 - E)) := by
  refine ⟨lt_min (by linarith) (by linarith), ?_, ?_⟩
  · have := min_le_left (E + 2) (2 - E); linarith
  · have := min_le_right (E + 2) (2 - E); linarith

/-- **Energy-uniform ⟹ fixed-`E`**: `FullSourceCovarianceEnergyUniformContract` implies
`FullSourceCovarianceContract`. -/
theorem fullSourceCovariance_of_uniform (h : FullSourceCovarianceEnergyUniformContract) :
    FullSourceCovarianceContract := by
  intro b hb0 hb E h1 h2
  obtain ⟨hκ, hE⟩ := mem_bulk_self h1 h2
  refine ⟨BlockBand.Transmission.PassiveCovariance.stationaryJet_exists hb0 hb h1 h2,
    fun s hs => ?_⟩
  obtain ⟨C, W₀, hC⟩ := h b hb0 hb _ hκ
  exact ⟨C, W₀, fun W hW => hC W hW E hE s hs⟩

/-- **`FullSourceCovarianceContract`** from `GaussianAbsorptionContract` and the two
`Δ`-covariance hypotheses `DeltaCovarianceSame`, `DeltaCovarianceOpposite`. -/
theorem fullSourceCovariance_of_delta (hGA : GaussianAbsorptionContract)
    (hS : DeltaCovarianceSame) (hO : DeltaCovarianceOpposite) : FullSourceCovarianceContract :=
  fullSourceCovariance_of_uniform (fullSourceCovarianceEnergyUniform_of_delta hGA hS hO)

end BlockBand.SourceProcess.FullSourceCovariance
