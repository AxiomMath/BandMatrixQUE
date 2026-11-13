module

public import BlockBand.SourceProcess.PhysApprox.B3JetRecur
public import BlockBand.SourceProcess.PhysApprox.B3JetNbhd

/-!
# The closed jets from the closing shift

With `closedInputPassive_b3ClosedX` and `closedInputRecursion_b3ClosedX` proved, the closed jets
need only the closing shift at the closing time:

* **`closedJet0Fam_of_disc`**: `MatchedTracesContract + GaussianAbsorptionContract +
  GaussianLpGradient + ClosedShiftDiscTrace + FarFracTraceMoments ⇒ ClosedJet0Fam`;
* `closedJet0Fam_of_shiftLp`: the same with `ClosedJetShiftStartLp b3ClosedX`;
* `closedJetL4Fam_b3ClosedX_of_entrance`: `GaussianAbsorptionContract`, `GaussianLpGradient` and
  `ClosedJetEntrance 4 b3ClosedX` give `ClosedJetL4Fam b3ClosedX`;
* `closedJetHalf_b3ClosedX_of_entrance`: the same with the entrance at `q = 2`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.Jet

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs

/-- **`ClosedJet0Fam`** from the contract hypotheses, the cavity-kernel bound and the fractional
moments. -/
theorem closedJet0Fam_of_disc (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hA : ClosedShiftDiscTrace) (hB : FarFracTraceMoments) :
    ClosedJet0Fam :=
  closedJet0Fam_of_frac hMT hGA hLp closedInputPassive_b3ClosedX closedInputRecursion_b3ClosedX
    hA hB

/-- **`ClosedJet0Fam`** from the contract hypotheses and the closing shift at the closing time in
`L^p`. -/
theorem closedJet0Fam_of_shiftLp (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSh : ClosedJetShiftStartLp b3ClosedX) : ClosedJet0Fam :=
  closedJet0Fam_of_shift hMT hGA hLp closedInputPassive_b3ClosedX closedInputRecursion_b3ClosedX
    hSh

/-- **`ClosedJetL4Fam b3ClosedX`** from `GaussianAbsorptionContract`, `GaussianLpGradient` and
the entrance estimate. -/
theorem closedJetL4Fam_b3ClosedX_of_entrance (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hEnt : ClosedJetEntrance 4 b3ClosedX) :
    ClosedJetL4Fam b3ClosedX :=
  closedJetL4Fam_b3ClosedX hGA hLp closedInputPassive_b3ClosedX closedInputRecursion_b3ClosedX
    hEnt

/-- **`ClosedJetHalf b3ClosedX`** from `GaussianAbsorptionContract`, `GaussianLpGradient` and the
entrance estimate at `q = 2`. -/
theorem closedJetHalf_b3ClosedX_of_entrance (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hEnt : ClosedJetEntrance 2 b3ClosedX) :
    ClosedJetHalf b3ClosedX :=
  closedJetHalf_b3ClosedX hGA hLp closedInputPassive_b3ClosedX closedInputRecursion_b3ClosedX
    hEnt

end BlockBand.SourceProcess.PhysApprox.B3.Jet
