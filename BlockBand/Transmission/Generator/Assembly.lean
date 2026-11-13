module

public import BlockBand.Transmission.Generator.MeanConductance

/-!
# `TransmissionGeneratorContract` from its inputs

`transmissionGenerator_of`: from `MatchedTracesContract`, `GaussianAbsorptionContract`,
`GaussianLpGradient` and the three statements `PowerDriftSummable` (`hD`), `PowerModulusAlong`
(`hMod`), `ProductMartingaleAlong` (`hProd`). The fields of the contract:
* the conductance moments: `conductanceMoments_holds`, with no further hypothesis;
* tightness, first clause: `tightOne_along` at `e ≡ E`; second clause: `hMod`;
* the martingale clause, drift half: from `hD` (`limit_drift_martingale`); product half: `hProd`;
* the mean conductance: from `hD` (`meanConductance_along`).
Each clause is first proved along a moving energy and specialised at `e ≡ E`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionUniform

theorem transmissionGenerator_of (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hD : PowerDriftSummable) (hMod : PowerModulusAlong)
    (hProd : ProductMartingaleAlong) : TransmissionGeneratorContract where
  tight := fun b hb0 hb E hE1 hE2 k hk ε T hε hεT =>
    ⟨tightOne_along (LengthUniform.transmissionLengthUniform_holds hMT hGA hLp) hb0 hb hE1 hE2
      (isMovingEnergy_const E) hk hε,
     hMod b hb0 hb E hE1 hE2 0 (fun _ => E) (isMovingEnergy_const E) k hk ε T hε hεT⟩
  martingale := fun b hb0 hb E hE1 hE2 Ω _ P Pk hP =>
    ⟨fun _ hk => limit_drift_martingale (LengthUniform.transmissionLengthUniform_holds hMT hGA hLp)
      hD hb0 hb hE1 hE2 (isMovingEnergy_const E) (isPowerTraceLimitAlong_const hP) hk,
     hProd b hb0 hb E hE1 hE2 0 (fun _ => E) (isMovingEnergy_const E) Ω _ P Pk
      (isPowerTraceLimitAlong_const hP)⟩
  conductanceMoments := conductanceMoments_holds hMT hGA hLp
  meanConductance := fun _ hb0 hb E hE1 hE2 _ _ _ _ hP _ ht =>
    meanConductance_along (LengthUniform.transmissionLengthUniform_holds hMT hGA hLp) hD hb0 hb
      hE1 hE2 (isMovingEnergy_const E) (isPowerTraceLimitAlong_const hP) ht

end BlockBand.Transmission.Generator
