module

public import BlockBand.SourceProcess.PhysApprox.B3Jet1Main
public import BlockBand.SourceProcess.PhysApprox.B3JetLp
public import BlockBand.SourceProcess.PhysApprox.B3JetFam

/-!
# The closed `δ₁` jet from the closed `δ₀` jet

Connects the closed `δ₁` jet `ClosedJet1Lp` to the `δ₀` side:

* `closedJet0LpSteps_of_fam`: the whole-space `ClosedJet0Fam` implies the alive-set
  `ClosedJet0LpSteps` (`‖1_A f‖_p ≤ ‖f‖_p`);
* `closedJet0Fam_of_start`: `closedJetLp_of` at `b3ClosedX` is `ClosedJet0Fam`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.Jet1

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.LengthUniform
open scoped ENNReal

/-- **`ClosedJet0Fam ⇒ ClosedJet0LpSteps`** (restriction to the alive set). -/
theorem closedJet0LpSteps_of_fam (hJ : ClosedJet0Fam) : ClosedJet0LpSteps := by
  intro b E np τ m T s h K Vs hFD R p hp
  obtain ⟨⟨-, -, hE1, hE2, -, -, -, -⟩, -, -, -, -, -⟩ := id hFD
  have hb : b < 1 := by linarith [hFD.1.2.1]
  obtain ⟨C, hC⟩ := hJ b E np τ m T s h K Vs hFD p hp
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  filter_upwards [hC, hFD.2.2.2.2.2] with W hW hVW j hj
  have hV : Measurable (Vs W) :=
    hVW.1.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  exact (eLpNorm_indicator_le _ (nullMeasurableSet_b3Alive hb hE1 hE2 s h τ m R W j hV)).trans
    ((hW j hj).trans (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))))

/-- **The closed `δ₀` in every `L^p` at `b3ClosedX` is `ClosedJet0Fam`.** -/
theorem closedJet0Fam_of_start (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : Jet.ClosedInputPassive b3ClosedX) (hRec : Jet.ClosedInputRecursion b3ClosedX)
    (hS : Jet.ClosedJetStartLp b3ClosedX) : ClosedJet0Fam := by
  intro b E np τ m T s h K Vs hFD p hp
  obtain ⟨C, -, hC⟩ := Jet.closedJetLp_of hGA hLp (Jet.closedInputRegular_b3ClosedX hP) hRec hS
    b E np τ m T s h K Vs hFD p hp
  exact ⟨C, hC⟩

/-- **`ClosedJet1Lp` from the input hypotheses**, the three closed-input hypotheses
`ClosedInputPassive`, `ClosedInputRecursion`, `ClosedJetShiftStartLp` at `b3ClosedX`, and the `δ₁`
closing shift `ClosedJet1ShiftLp`. -/
theorem closedJet1Lp_b3ClosedX (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : Jet.ClosedInputPassive b3ClosedX)
    (hRec : Jet.ClosedInputRecursion b3ClosedX) (hSh0 : Jet.ClosedJetShiftStartLp b3ClosedX)
    (hSh1 : ClosedJet1ShiftLp) : ClosedJet1Lp :=
  closedJet1Lp_of_shift hMT hGA hLp hP hRec
    (closedJet0LpSteps_of_fam (closedJet0Fam_of_start hGA hLp hP hRec
      (Jet.closedJetStartLp_of_shift (deltaZeroLengthUniform_holds hMT hGA hLp)
        (fun b E s h _ τ m _ j => measurable_b3ClosedX b E s h τ m j) hSh0)))
    hSh1

/-- **Both closed jets `ClosedJet0Lp`, `ClosedJet1Lp` at once** from the same hypotheses. -/
theorem closedJets_b3ClosedX (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : Jet.ClosedInputPassive b3ClosedX)
    (hRec : Jet.ClosedInputRecursion b3ClosedX) (hSh0 : Jet.ClosedJetShiftStartLp b3ClosedX)
    (hSh1 : ClosedJet1ShiftLp) : ClosedJet0Lp ∧ ClosedJet1Lp :=
  ⟨Jet.closedJet0Lp_b3ClosedX hMT hGA hLp hP hRec hSh0,
    closedJet1Lp_b3ClosedX hMT hGA hLp hP hRec hSh0 hSh1⟩

end BlockBand.SourceProcess.PhysApprox.B3.Jet1
