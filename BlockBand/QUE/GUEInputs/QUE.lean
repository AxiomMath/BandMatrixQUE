module

public import BlockBand.QUE.Assembly.PairResidual
public import BlockBand.QUE.GUEInputs.PhysicalAngular
public import BlockBand.Center.PhysicalCenterW0Holds
public import BlockBand.Center.CenterSupplyHolds
public import BlockBand.Wegner.ConditionalCount
public import BlockBand.Wegner.PhysicalConditionalCount
public import BlockBand.GaussianCalculus.Poincare
public import BlockBand.GaussianCalculus.MultivariateCircularIBP
public import BlockBand.Coarea.PoleExclusion
public import BlockBand.Coarea.CoareaContract
public import BlockBand.Coarea.FreshPalmDensity
public import BlockBand.Coarea.PairLawBridge
public import BlockBand.Coarea.CompressedLawBridge
public import BlockBand.Native.Prekopa.SourceContract
public import BlockBand.Layers.MatchedTraces
public import BlockBand.Layers.HeatMeanSquare
public import BlockBand.Palm.ConditionalMomentsHolds
public import BlockBand.SourceProcess.Stochastic.Assembly.Contracts
public import BlockBand.SourceProcess.Stochastic.Assembly.ContractB

/-!
# The QUE theorem from the GUE-scope inputs

`que_of_gueInputs` has the binders and conclusion of `BlockBand.que`. Its additional hypotheses
are the PSSS source contract `External.PSSS.SourceContract.{0}` (Wegner counts); the types of the
`W`-independent deterministic fields `eigenpairs_exist` and `spacing_exists` of
`External.CEH.SourceContract` (hypotheses hEig and hSp); and the statements
`Inputs.ExternalLocalGUE`, `Inputs.ExternalETH` and `Inputs.MDEBranchIdentification`.

The deterministic fields are proved unconditionally in `BlockBand.Native.CEH`
(`eigenpairs_exist`, `spacing_exists`, `mdeBranchIdentification_holds`), and so is the local law
(`externalLocalGUE_holds`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.QUE.GUEInputs

open MeasureTheory

-- The linter option silences the unused binders `hnW` and `hθ'`, kept to match `BlockBand.que`.
set_option linter.unusedVariables false in
/-- **The QUE theorem** (the QUE bound) with the conclusion of `BlockBand.que`, from PSSS, the
deterministic fields of `External.CEH.SourceContract` and the hypotheses `ExternalLocalGUE`,
`ExternalETH`, `MDEBranchIdentification`. -/
theorem que_of_gueInputs (hpsss : BlockBand.External.PSSS.SourceContract.{0})
    (hEig : ∀ (N : ℕ), 0 < N → Nonempty (BlockBand.External.CEH.EigenpairSelection N))
    (hSp : ∀ {N : ℕ} {lambda : ℝ} {H0 : BlockBand.External.CEH.SourceHermitian N},
      4 ≤ N → 0 < lambda → ∀ M : BlockBand.External.CEH.MDEBranch lambda H0,
        Nonempty (BlockBand.External.CEH.TypicalSpacing M))
    (hELG : BlockBand.Internal.Contracts.Inputs.ExternalLocalGUE)
    (hETH : BlockBand.Internal.Contracts.Inputs.ExternalETH)
    (hMDE : BlockBand.Internal.Contracts.Inputs.MDEBranchIdentification)
    (b θ T : ℝ)
    (hb : 0 < b) (hb' : b < 1 / 2)
    (hθ : 0 < θ) (hθ' : θ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (n W : ℕ)
        (hn : 4 ≤ n) (hW : 0 < W)
        (hnW : (n : ℝ) ≤ T * (W : ℝ)),
      let p : Parameters := ⟨n, W, b, hn, hW, hb, hb'⟩
      Nonempty (FiniteRealization p) ∧
        ∀ (R : FiniteRealization p) (α : Fin p.N),
          IsBulkRank p θ α →
        ∀ v : p.Site → ℝ, (∀ x, |v x| ≤ 1) →
          R.spectral.queStatistic α v ≤
            C * (p.ratio + Real.rpow p.ratio (3 / 2 : ℝ)) +
              1 / ((W : ℝ) + 1) := by
  
  have hcount : BlockBand.Internal.Contracts.Inputs.ConditionalBlockGUECount :=
    BlockBand.Wegner.conditionalBlockGUECount_holds hpsss
  have hgrad : BlockBand.Internal.Contracts.Inputs.GaussianLpGradient :=
    BlockBand.GaussianCalculus.gaussianGradientInequalities_holds.2
  have hIBP : BlockBand.Internal.Contracts.Inputs.MultivariateGaussianIBP :=
    BlockBand.GaussianCalculus.gaussianIdentitiesMultivariate_holds.1
  have hPBC : BlockBand.Internal.Contracts.Inputs.PhysicalBlockConditionalCount :=
    BlockBand.Wegner.physicalBlockConditionalCount_holds hpsss
  -- Prékopa
  have hPre : BlockBand.External.Prekopa.SourceContract :=
    BlockBand.Native.Prekopa.sourceContract_holds
  
  have hMT : BlockBand.Internal.Contracts.Layers.MatchedTracesContract :=
    BlockBand.Layers.matchedTraces_holds hcount hgrad
  have hRank : BlockBand.Internal.Contracts.Layers.RankLocationContract :=
    BlockBand.Layers.rankLocation_holds hcount hgrad
  
  have hpole : BlockBand.Internal.Contracts.CoareaPalm.PairPoleExclusionContract :=
    BlockBand.Coarea.PoleExclusion.pairPoleExclusionContract_holds
  have hC : BlockBand.Internal.Contracts.CoareaPalm.CoareaContract :=
    BlockBand.Coarea.coareaContract_holds
  have hP : BlockBand.Internal.Contracts.CoareaPalm.FreshPalmContract :=
    BlockBand.Palm.freshPalmContract_holds
      (fun d => (BlockBand.SourceProcess.Stochastic.Assembly.contractA_holds d).1)
      (BlockBand.SourceProcess.Stochastic.Assembly.contractA_holds 1).2
      BlockBand.SourceProcess.Stochastic.Assembly.contractB_holds
      hELG hMDE hgrad hIBP
  have hD : BlockBand.Internal.Contracts.CoareaPalm.FreshEigenpairDensityContract :=
    BlockBand.Coarea.FreshPalm.freshEigenpairDensityContract_holds
  
  have hBridge : BlockBand.LocalWindow.LawBridge.PairGUELawBridgeStatement := by
    exact BlockBand.Coarea.LawBridge.pairGUELawBridge_holds
  have hComp : BlockBand.LocalWindow.ProofPartTwo.CompressedGUELawBridgeStatement := by
    exact BlockBand.Coarea.LawBridge.compressedGUELawBridge_holds
  -- center and angular contracts at `pairCenterFamily0`
  have hc := BlockBand.Center.physicalCenter_holds hcount hgrad hpole b θ T hb hb' hθ
  have ha := physicalAngularModeContract_of_gueInputs (T := T) hEig hSp hPre hMDE hETH hELG hgrad
    hPBC hMT hRank hC hP hD hpole hBridge hComp hb hb' hθ BlockBand.Center.pairCenterFamily0
    (BlockBand.Center.centerSupply_holds hcount hgrad hpole)
  exact BlockBand.QUE.PairResidual.que_of_contracts b θ T hb hb'
    BlockBand.Center.pairCenterFamily0 hc ha

end BlockBand.QUE.GUEInputs
