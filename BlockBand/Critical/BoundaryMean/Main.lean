module

public import BlockBand.Critical.BoundaryMean.SharpDensity
public import BlockBand.Critical.BoundaryMean.Reduction

/-!
# The exact boundary mean theorem

The exact boundary mean theorem follows from the fresh Palm, point-density, common-port
mean and trace-matrix inputs and the external PSSS input:

* `SharpDensity.hermitianCollarMean_holds : … → HermitianCollarMeanStatement` (the Hermitian
  collar mean, which is the main part of the proof);
* `exactBoundaryMean_of_inputs : … → ExactBoundaryMeanContract`, through the reduction
  `exactBoundaryMean_of_hermitian` (the last step and the radial regulator).

The hypotheses are `FreshPalmContract`, `PointDensityContract`, `CommonPortMeanContract`,
`TraceMatrixContract` and the external `PSSS.SourceContract`; the regularity certificate
`Palm.certificate_full_uniform` and the conditional Schur identity
`collarConditionalDensityIdentity_holds` are proved results used in the proof.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.BoundaryMean

open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Critical

/-- The exact boundary mean theorem, conditional on the listed inputs. -/
theorem exactBoundaryMean_of_inputs (hP : FreshPalmContract) (hPD : PointDensityContract)
    (hCM : CommonPortMeanContract) (hTM : TraceMatrixContract)
    (source : BlockBand.External.PSSS.SourceContract.{0}) : ExactBoundaryMeanContract :=
  exactBoundaryMean_of_hermitian (hermitianCollarMean_holds hP hPD hCM hTM source)

end BlockBand.Critical.BoundaryMean
