module

public import BlockBand.SourceProcess.FullSourceGenerator.Interface
public import BlockBand.SourceProcess.FullSource.DeltaHolds

/-!
# The full-source generator theorem: assembly

`fullSourceGenerator_of`: the generator and tightness clauses, together with the full-source
moments, give `FullSourceGeneratorContract`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceGenerator

open BlockBand.Internal.Contracts.Inputs BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionStatements

/-- `FullSourceGeneratorContract` from its three fields. -/
theorem fullSourceGenerator_of_clauses (hG : GeneratorClause) (hT : TightClause)
    (hM : FullSourceMomentsContract) : FullSourceGeneratorContract :=
  ⟨hG, hT, hM⟩

/-- `FullSourceGeneratorContract` from `GeneratorClause`, `TightClause` and the input hypotheses
of the full-source moments (`FullSource.fullSourceMoments_holds`). -/
theorem fullSourceGenerator_of (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hG : GeneratorClause) (hT : TightClause) :
    FullSourceGeneratorContract :=
  fullSourceGenerator_of_clauses hG hT (FullSource.fullSourceMoments_holds hGA hLp hSR)

end BlockBand.SourceProcess.FullSourceGenerator
