module

public import BlockBand.SourceProcess.PhysApprox.B3Jet1Shift
public import BlockBand.SourceProcess.PhysApprox.B3Jet1Bridge

/-!
# Both closed jets from the one closing-shift estimate

* `closedJetShiftStartLp_of_nbhd`: `ClosedJetShiftNbhdLp ⇒ ClosedJetShiftStartLp b3ClosedX`
  (the estimate at `w = z_∂`; the integrands agree by definition);
* `closedJets_of_nbhd`: both closed jets `ClosedJet0Lp`, `ClosedJet1Lp` from this one estimate.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.Jet1

open MeasureTheory Filter Metric
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Inputs

/-- **The `δ₀` closing-shift estimate is the common estimate at `w = z_∂`.** -/
theorem closedJetShiftStartLp_of_nbhd (hN : ClosedJetShiftNbhdLp) :
    Jet.ClosedJetShiftStartLp b3ClosedX := by
  intro b E np τ m T s h K Vs hFD p hp
  obtain ⟨r, C, hr, hev⟩ := hN b E np τ m T s h K Vs hFD p hp
  exact ⟨C, hev.mono fun W hW => hW _ (mem_closedBall_self hr.le)⟩

/-- **Both closed jets `ClosedJet0Lp`, `ClosedJet1Lp` from one closing-shift estimate.** -/
theorem closedJets_of_nbhd (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : Jet.ClosedInputPassive b3ClosedX)
    (hRec : Jet.ClosedInputRecursion b3ClosedX) (hN : ClosedJetShiftNbhdLp) :
    ClosedJet0Lp ∧ ClosedJet1Lp :=
  closedJets_b3ClosedX hMT hGA hLp hP hRec (closedJetShiftStartLp_of_nbhd hN)
    (closedJet1ShiftLp_of_nbhd hP hN)

end BlockBand.SourceProcess.PhysApprox.B3.Jet1
