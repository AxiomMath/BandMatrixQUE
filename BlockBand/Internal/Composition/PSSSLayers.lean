module

public import BlockBand.Wegner.ConditionalCount
public import BlockBand.Wegner.ProjectedWegner
public import BlockBand.Wegner.RingBlockModel
public import BlockBand.GaussianCalculus.Poincare
public import BlockBand.GaussianCalculus.MultivariateCircularIBP
public import BlockBand.Layers.GaussianAbsorption
public import BlockBand.Layers.TraceMatrix
public import BlockBand.Layers.LayerContraction
public import BlockBand.Layers.MatchedTraces
public import BlockBand.Layers.MatchedPath
public import BlockBand.Palm.CoarseRelativeHolds
public import BlockBand.Endpoints.Poisson.FiniteLogRecoveryRing

/-!
# The layer statements from the PSSS input

Each layer statement of `Internal.Contracts.Layers` listed here (Gaussian absorption, the trace matrix, layer contraction and comparison, matched traces, and the scalar
recursion) is derived here from `PSSS.SourceContract` alone.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Internal.Composition

open BlockBand.External BlockBand.Internal.Contracts

/-- The Gaussian absorption lemma, from `PSSS.SourceContract` only. -/
theorem gaussianAbsorption_native (source : BlockBand.External.PSSS.SourceContract.{0}) :
    BlockBand.Internal.Contracts.Layers.GaussianAbsorptionContract :=
  BlockBand.Layers.gaussianAbsorption_holds (BlockBand.Wegner.conditionalBlockGUECount_holds source)

/-- The trace-matrix lemma, from `PSSS.SourceContract` only. -/
theorem traceMatrix_native (source : BlockBand.External.PSSS.SourceContract.{0}) :
    BlockBand.Internal.Contracts.Layers.TraceMatrixContract :=
  BlockBand.Layers.traceMatrix_holds (BlockBand.Wegner.conditionalBlockGUECount_holds source)
    BlockBand.GaussianCalculus.gaussianGradientInequalities_holds.2

/-- The layer-contraction lemma, from `PSSS.SourceContract` only. -/
theorem layerContraction_native (source : BlockBand.External.PSSS.SourceContract.{0}) :
    BlockBand.Internal.Contracts.Layers.LayerContractionContract :=
  BlockBand.Layers.layerContraction_holds (BlockBand.Wegner.conditionalBlockGUECount_holds source)

/-- The comparison clause in the proof of the layer-contraction lemma, from `PSSS.SourceContract`
only. -/
theorem layerComparison_native (source : BlockBand.External.PSSS.SourceContract.{0}) :
    BlockBand.Internal.Contracts.Layers.LayerComparisonContract :=
  BlockBand.Layers.layerComparison_holds (BlockBand.Wegner.conditionalBlockGUECount_holds source)

/-- The matched-traces theorem (path, common port, residual pair), from `PSSS.SourceContract`
only. -/
theorem matchedTraces_native (source : BlockBand.External.PSSS.SourceContract.{0}) :
    BlockBand.Internal.Contracts.Layers.MatchedTracesContract :=
  BlockBand.Layers.matchedTraces_holds (BlockBand.Wegner.conditionalBlockGUECount_holds source)
    BlockBand.GaussianCalculus.gaussianGradientInequalities_holds.2

/-- The one-step matched-trace recursion and the scalar exit bound, from `PSSS.SourceContract`
only. -/
theorem scalarRecursion_native (source : BlockBand.External.PSSS.SourceContract.{0}) :
    BlockBand.Internal.Contracts.Layers.ScalarRecursionContract :=
  BlockBand.Layers.scalarRecursionContract_holds
    (BlockBand.Wegner.conditionalBlockGUECount_holds source)
    BlockBand.GaussianCalculus.gaussianGradientInequalities_holds.2

/-- `CoarseRelativeContract` with no hypothesis: both Gaussian inputs of `coarseRelative_holds` are
proved. -/
theorem coarseRelative_unconditional :
    BlockBand.Internal.Contracts.CoareaPalm.CoarseRelativeContract :=
  BlockBand.Palm.CoarseRelative.coarseRelative_holds
    BlockBand.GaussianCalculus.gaussianGradientInequalities_holds.2
    BlockBand.GaussianCalculus.gaussianIdentitiesMultivariate_holds.1

end BlockBand.Internal.Composition

namespace BlockBand.Endpoints

open MeasureTheory Matrix
open scoped ContDiff
open BlockBand.Internal.Contracts.Inputs BlockBand.Internal.Contracts.InputsRing

/-- **Finite logarithmic recovery** (ring and direct-sum clauses, one constant), from
`PSSS.SourceContract` only: for a smooth compactly supported `f ≥ 0`, the positive logarithmic
statistic differs from the raw unfolded spectral sum by at most
`C_f (δ(1 + |log δ|) + |Cᶜ|/n)` in mean, on the ring and on direct sums of rings.
-/
theorem finiteLogRecovery_ring_and_ringSum_native
    (source : BlockBand.External.PSSS.SourceContract.{0})
    (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (ρ : ℝ) (hρ : 0 < ρ)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hfs : HasCompactSupport f) (hf0 : ∀ x, 0 ≤ f x) :
    ∃ Cf : ℝ, 0 ≤ Cf ∧
      (∀ (p : Parameters), p.b = b → ∀ (model : p.GaussianRingModel) (E δ : ℝ), 0 < δ →
        ∀ C : Finset (ZMod p.n),
          Integrable (fun H => |positiveLogStatistic H E ((p.N : ℝ) * ρ) δ
              (physicalBlockProjector p C) f -
            rawUnfoldedSpectralSum H E ((p.N : ℝ) * ρ) f|)
            (model.law : Measure p.SiteMatrix) ∧
          ∫ H, |positiveLogStatistic H E ((p.N : ℝ) * ρ) δ (physicalBlockProjector p C) f -
              rawUnfoldedSpectralSum H E ((p.N : ℝ) * ρ) f|
              ∂(model.law : Measure p.SiteMatrix) ≤
            Cf * (δ * (1 + |Real.log δ|) + ((Cᶜ).card : ℝ) / p.n)) ∧
      (∀ (r W : ℕ) (n : Fin r → ℕ) (hn : ∀ i, 4 ≤ n i) (hW : 0 < W)
        (models : ∀ i, (ringParameters (n i) W b (hn i) hW hb hb').GaussianRingModel),
        0 < ∑ i, n i → ∀ (E δ : ℝ), 0 < δ → ∀ C : Finset (Fin (∑ i, n i)),
          Integrable (fun H => |positiveLogStatistic (directSumBlockCoords n
                (fun i => toBlockCoords (ringParameters (n i) W b (hn i) hW hb hb') (H i)))
              E ((((∑ i, n i) * W : ℕ) : ℝ) * ρ) δ (blockProjector C) f -
            rawUnfoldedSpectralSum (directSumBlockCoords n
                (fun i => toBlockCoords (ringParameters (n i) W b (hn i) hW hb hb') (H i)))
              E ((((∑ i, n i) * W : ℕ) : ℝ) * ρ) f|)
            (Measure.pi (fun i => ((models i).law :
              Measure (ringParameters (n i) W b (hn i) hW hb hb').SiteMatrix))) ∧
          ∫ H, |positiveLogStatistic (directSumBlockCoords n
                (fun i => toBlockCoords (ringParameters (n i) W b (hn i) hW hb hb') (H i)))
              E ((((∑ i, n i) * W : ℕ) : ℝ) * ρ) δ (blockProjector C) f -
            rawUnfoldedSpectralSum (directSumBlockCoords n
                (fun i => toBlockCoords (ringParameters (n i) W b (hn i) hW hb hb') (H i)))
              E ((((∑ i, n i) * W : ℕ) : ℝ) * ρ) f|
              ∂(Measure.pi (fun i => ((models i).law :
                Measure (ringParameters (n i) W b (hn i) hW hb hb').SiteMatrix))) ≤
            Cf * (δ * (1 + |Real.log δ|) + ((Cᶜ).card : ℝ) / (∑ i, n i : ℕ))) :=
  finiteLogRecovery_ring_and_ringSum BlockBand.Wegner.ringBlockModels_holds
    (BlockBand.Wegner.projectedWegner_holds source)
    (BlockBand.Wegner.conditionalBlockGUECount_holds source)
    b hb hb' ρ hρ f hf hfs hf0

end BlockBand.Endpoints
