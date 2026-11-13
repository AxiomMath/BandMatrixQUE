module

public import BlockBand.QUE.Assembly.PhysicalAngularOfParts
public import BlockBand.Angular.AssemblyGood
public import BlockBand.DeterminantScore.DeterminantScoreHolds
public import BlockBand.DeterminantScore.MinorTailInverse
public import BlockBand.DeterminantScore.NegativeSpreadInverse
public import BlockBand.DeterminantScore.EigenDensityGT
public import BlockBand.DeterminantScore.BrascampLieb
public import BlockBand.DeterminantScore.RealLoop
public import BlockBand.DeterminantScore.WeightedTrace
public import BlockBand.DeterminantScore.BorderLaw
public import BlockBand.DeterminantScore.GelfandTsetlin

/-!
# `QUE.PhysicalAngularModeContract`: the dependency chain

Composition of the physical angular theorem and its use in the QUE theorem.

`physicalAngularModeContract_of_score`: the physical angular statement from `CoareaContract`,
`FreshPalmContract`, `FreshEigenpairDensityContract`, `PairPoleExclusionContract` and the
determinant score `DeterminantScoreStatement` (`goodPart_min_of` and the Gaussian tails).

`physicalAngularModeContract_of_open`: the same with the determinant score unfolded through the
chain determinant score ← physical minor tail ← negative spread ← indexed spectral convexity ←
ordered eigenvalue density and Brascamp–Lieb, and the physical real loop
(`determinantScore_of_open`). Its hypotheses are the four statements above,
`Prekopa.SourceContract`, the physical local window `LocalWindow.PhysicalLocalWindowStatement`,
the physical weighted trace `RealLoop.PhysicalWeightedTraceStatement`, and two classical
identities: the Weyl integration formula `EigenDensity.WeylIntegrationStatement` and HCIZ in
Gelfand–Tsetlin form `EigenDensity.GelfandTsetlinStatement`.

`physicalAngularModeContract_of_open'`: the same with `PhysicalWeightedTraceStatement` replaced by
`WeightedTrace.SelectedResolventStatement` (the averaged local law at the selected energy), via
`physicalWeightedTrace_holds`. `physicalAngularModeContract_of_remaining` and
`physicalAngularModeContract_of_window` then discharge the Weyl integration formula
(`weylIntegration_holds`) and the Gelfand–Tsetlin statement (`gelfandTsetlin_of_border`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.QUE.PhysicalAngularHolds

open BlockBand.Internal.Contracts.QUE BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.DeterminantScore

/-- **The physical angular theorem from the determinant score**, for every Dyson centre family,
`0 < θ`. -/
theorem physicalAngularModeContract_of_score (hC : CoareaContract) (hP : FreshPalmContract)
    (hD : FreshEigenpairDensityContract) (hPole : PairPoleExclusionContract)
    (hScore : DeterminantScoreStatement) {b θ T : ℝ} (hb : 0 < b) (hb' : b < 1 / 2)
    (hθ : 0 < θ) (w : PairCenterFamily)
    (hw : BlockBand.Internal.Contracts.Layers.IsCenterSupply w) :
    PhysicalAngularModeContract b θ T hb hb' w :=
  PhysicalAngularOfParts.physicalAngularModeContract_of_goodPart hb hb' hθ
    (Angular.AssemblyGood.goodPart_min_of hC hP hD hScore hb hb' hθ) hPole w hw

/-- **The determinant score theorem** from `CoareaContract`, Prékopa and the local window,
weighted trace, Weyl integration and Gelfand–Tsetlin statements. -/
theorem determinantScore_of_open (hC : CoareaContract)
    (hPre : BlockBand.External.Prekopa.SourceContract)
    (hLW : BlockBand.LocalWindow.PhysicalLocalWindowStatement)
    (hWT : RealLoop.PhysicalWeightedTraceStatement)
    (hW : EigenDensity.WeylIntegrationStatement) (hG : EigenDensity.GelfandTsetlinStatement) :
    DeterminantScoreStatement :=
  DeterminantScoreHolds.determinantScore_holds hC
    (MinorTailInverse.physicalMinorTail_holds hC
      (NegativeSpread.negativeSpread_of_convexity_of_prekopa
        (SpectralConvexity.indexedSpectralConvexity_of
          (EigenDensity.orderedEigenDensity_of_weyl_gt hPre hW hG)
          (SpectralConvexity.BrascampLieb.brascampLieb hPre)) hPre)
      hLW (RealLoop.physicalRealLoop_of_weightedTrace hC hWT))

/-- **The physical angular theorem, full chain**: from the four Palm and coarea statements,
Prékopa and the local window, weighted trace, Weyl integration and Gelfand–Tsetlin statements. -/
theorem physicalAngularModeContract_of_open (hC : CoareaContract) (hP : FreshPalmContract)
    (hD : FreshEigenpairDensityContract) (hPole : PairPoleExclusionContract)
    (hPre : BlockBand.External.Prekopa.SourceContract)
    (hLW : BlockBand.LocalWindow.PhysicalLocalWindowStatement)
    (hWT : RealLoop.PhysicalWeightedTraceStatement)
    (hW : EigenDensity.WeylIntegrationStatement) (hG : EigenDensity.GelfandTsetlinStatement)
    {b θ T : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) (hθ : 0 < θ) (w : PairCenterFamily)
    (hw : BlockBand.Internal.Contracts.Layers.IsCenterSupply w) :
    PhysicalAngularModeContract b θ T hb hb' w :=
  physicalAngularModeContract_of_score hC hP hD hPole
    (determinantScore_of_open hC hPre hLW hWT hW hG) hb hb' hθ w hw

/-- **The physical angular theorem, with the weighted trace proved**: from the four Palm and coarea
statements, Prékopa and `PhysicalLocalWindowStatement`, `SelectedResolventStatement`,
`WeylIntegrationStatement`, `GelfandTsetlinStatement`. -/
theorem physicalAngularModeContract_of_open' (hC : CoareaContract) (hP : FreshPalmContract)
    (hD : FreshEigenpairDensityContract) (hPole : PairPoleExclusionContract)
    (hPre : BlockBand.External.Prekopa.SourceContract)
    (hLW : BlockBand.LocalWindow.PhysicalLocalWindowStatement)
    (hSR : WeightedTrace.SelectedResolventStatement)
    (hW : EigenDensity.WeylIntegrationStatement) (hG : EigenDensity.GelfandTsetlinStatement)
    {b θ T : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) (hθ : 0 < θ) (w : PairCenterFamily)
    (hw : BlockBand.Internal.Contracts.Layers.IsCenterSupply w) :
    PhysicalAngularModeContract b θ T hb hb' w :=
  physicalAngularModeContract_of_open hC hP hD hPole hPre hLW
    (WeightedTrace.physicalWeightedTrace_holds hC hLW hSR) hW hG hb hb' hθ w hw

/-- **The physical angular theorem, with the Weyl formula proved**: from the four Palm and coarea
statements, Prékopa and `PhysicalLocalWindowStatement`, `SelectedResolventStatement`,
`GelfandTsetlinStatement`. -/
theorem physicalAngularModeContract_of_remaining (hC : CoareaContract) (hP : FreshPalmContract)
    (hD : FreshEigenpairDensityContract) (hPole : PairPoleExclusionContract)
    (hPre : BlockBand.External.Prekopa.SourceContract)
    (hLW : BlockBand.LocalWindow.PhysicalLocalWindowStatement)
    (hSR : WeightedTrace.SelectedResolventStatement) (hG : EigenDensity.GelfandTsetlinStatement)
    {b θ T : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) (hθ : 0 < θ) (w : PairCenterFamily)
    (hw : BlockBand.Internal.Contracts.Layers.IsCenterSupply w) :
    PhysicalAngularModeContract b θ T hb hb' w :=
  physicalAngularModeContract_of_open' hC hP hD hPole hPre hLW hSR
    WeylIntegration.weylIntegration_holds hG hb hb' hθ w hw

/-- **The physical angular theorem, with the spectral chain proved**: from the four Palm and
coarea statements, Prékopa, `PhysicalLocalWindowStatement` and `SelectedResolventStatement`. -/
theorem physicalAngularModeContract_of_window (hC : CoareaContract) (hP : FreshPalmContract)
    (hD : FreshEigenpairDensityContract) (hPole : PairPoleExclusionContract)
    (hPre : BlockBand.External.Prekopa.SourceContract)
    (hLW : BlockBand.LocalWindow.PhysicalLocalWindowStatement)
    (hSR : WeightedTrace.SelectedResolventStatement)
    {b θ T : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) (hθ : 0 < θ) (w : PairCenterFamily)
    (hw : BlockBand.Internal.Contracts.Layers.IsCenterSupply w) :
    PhysicalAngularModeContract b θ T hb hb' w :=
  physicalAngularModeContract_of_remaining hC hP hD hPole hPre hLW hSR
    (GelfandTsetlin.gelfandTsetlin_of_border WeylIntegration.diagonalBorderLaw_holds) hb hb' hθ w hw

end BlockBand.QUE.PhysicalAngularHolds
