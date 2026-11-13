module

public import BlockBand.Endpoints.Normalization.PhysicalLeadProfileAssembly
public import BlockBand.Endpoints.Normalization.ExactPalmAssembly

/-!
# The Palm and normalizer statements from the PSSS source theorem alone

Versions of the exact Palm, one-block Palm, regular-event, normalizer and physical lead-profile
statements with the hypothesis `inputs : NativeInputs.{0}` replaced by
`hpsss : PSSS.SourceContract.{0}` (the results named `…_psss` here). The original proofs, in other
modules, use `inputs` only through its `psss` field:
* `exactPalm_upper_of`, `oneBlockPalm_upper_of`: only through
  `palmMass_le inputs.psss`;
* `pairRegularEvent_of_native`, `blockRegularEvent_of_native`: only through
  `Wegner.physicalBlockConditionalCount_holds native.psss`;
* `exactPalmContract_of`, `exactPalmContract_holds`, `oneBlockPalmContract_of`,
  `oneBlockPalmContract_holds`, `normalizerContract_of`,
  `oneBlockNormalizerContract_of`, `physicalLeadProfileContract_of`: `inputs` is only passed to
  the results above (and to each other).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Internal.ReducedInputs

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Model.Construction BlockBand.Coarea BlockBand.Endpoints.Normalization
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.ClocksCommonPort
open BlockBand.Internal.Contracts.Critical
open scoped ENNReal NNReal ComplexConjugate

/-- `Endpoints.Normalization.exactPalm_upper_of` with `inputs` replaced by its `psss` field. -/
theorem exactPalm_upper_of_psss (hpsss : BlockBand.External.PSSS.SourceContract.{0})
    (hD : FreshEigenpairDensityContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∃ C : ℝ, ∀ (p : Parameters), p.b = b →
    ∀ (i : ZMod p.n) (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ),
    IsPairFrame p i U → ∀ ω : SplitState p i, IsHermitianExterior p i ω → ∀ e : ℝ,
      pairNormalizer p i U ω e ≤ ENNReal.ofReal (C * (2 * p.W)) := by
  obtain ⟨C, -, hZ⟩ := palmMass_le hpsss
  intro b _ _
  refine ⟨C / Real.sqrt (min b (1 - 2 * b)), ?_⟩
  intro p hpb i U hU ω hω e
  rw [pairNormalizer_eq_palmMass p i hD (FixedOmega.pairEquiv p i) U hU ω hω e]
  apply ENNReal.ofReal_le_ofReal
  have hF := reindex_isHermitian (physicalCoareaF_isHermitian' ω.1 ω.2.1 ω.2.2 hω.1 hω.2 e)
    (FixedOmega.pairEquiv p i)
  have hle := hZ (2 * p.W) (two_W_pos p) (pairS p) (pairS_pos p) _ hF e
  have hs : pairS p = min b (1 - 2 * b) := by subst hpb; rfl
  rw [hs] at hle ⊢
  refine hle.trans (le_of_eq ?_)
  push_cast
  ring

/-- `Endpoints.Normalization.oneBlockPalm_upper_of` with `inputs` replaced by its `psss` field. -/
theorem oneBlockPalm_upper_of_psss (hpsss : BlockBand.External.PSSS.SourceContract.{0})
    (hD : FreshEigenpairDensityContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∃ C : ℝ, ∀ (p : Parameters), p.b = b →
    ∀ (k : ZMod p.n) (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ),
    IsBlockFrame p k U → ∀ ω : BlockState p k, ω.1.IsHermitian → ∀ e : ℝ,
      blockNormalizer p k U ω e ≤ ENNReal.ofReal (C * p.W) := by
  obtain ⟨C, -, hZ⟩ := palmMass_le hpsss
  intro b _ _
  refine ⟨C / Real.sqrt (1 - 2 * b), ?_⟩
  intro p hpb k U hU ω hω e
  rw [blockNormalizer_eq_palmMass p k hD (blockEquiv p k) U hU ω hω e]
  apply ENNReal.ofReal_le_ofReal
  have hF := reindex_isHermitian (blockF_isHermitian p k ω hω e) (blockEquiv p k)
  have hle := hZ p.W p.W_pos p.c p.c_pos _ hF e
  have hs : p.c = 1 - 2 * b := by subst hpb; rfl
  rw [hs] at hle ⊢
  exact hle

/-- `pairRegularEvent_of_native` with `native` replaced by its `psss` field. -/
theorem pairRegularEvent_of_psss (hMT : MatchedTracesContract)
    (hpsss : BlockBand.External.PSSS.SourceContract.{0}) : PairRegularEventContract :=
  pairRegularEvent_of_inputs hMT (BlockBand.Wegner.physicalBlockConditionalCount_holds hpsss)

/-- `blockRegularEvent_of_native` with `native` replaced by its `psss` field. -/
theorem blockRegularEvent_of_psss (hMT : MatchedTracesContract)
    (hpsss : BlockBand.External.PSSS.SourceContract.{0}) : BlockRegularEventContract :=
  blockRegularEvent_of_inputs hMT (BlockBand.Wegner.physicalBlockConditionalCount_holds hpsss)

/-- `exactPalmContract_of`, PSSS-only. -/
theorem exactPalmContract_of_psss (hpsss : BlockBand.External.PSSS.SourceContract.{0})
    (hC : CoareaContract) (hD : FreshEigenpairDensityContract) : ExactPalmContract where
  mass := exactPalm_mass_of_coarea hC
  massReal := exactPalm_massReal_of_coarea hC
  index := exactPalm_index_of_coarea hC
  indexReal := exactPalm_indexReal_of_coarea hC
  upper := exactPalm_upper_of_psss hpsss hD

/-- **`exactPalmContract_holds`, from PSSS only**: `Clocks.ExactPalmContract`. -/
theorem exactPalmContract_holds_psss (hpsss : BlockBand.External.PSSS.SourceContract.{0}) :
    ExactPalmContract :=
  exactPalmContract_of_psss hpsss BlockBand.Coarea.coareaContract_holds
    BlockBand.Coarea.FreshPalm.freshEigenpairDensityContract_holds

/-- `oneBlockPalmContract_of`, PSSS-only. -/
theorem oneBlockPalmContract_of_psss (hpsss : BlockBand.External.PSSS.SourceContract.{0})
    (hD : FreshEigenpairDensityContract) : OneBlockPalmContract where
  splitting_exists := oneBlockPalm_splitting_exists
  frame_exists := oneBlockPalm_frame_exists
  mass := oneBlockPalm_mass
  massReal := oneBlockPalm_massReal
  index := oneBlockPalm_index
  indexReal := oneBlockPalm_indexReal
  upper := oneBlockPalm_upper_of_psss hpsss hD

/-- **`oneBlockPalmContract_holds`, from PSSS only.** -/
theorem oneBlockPalmContract_holds_psss (hpsss : BlockBand.External.PSSS.SourceContract.{0}) :
    OneBlockPalmContract :=
  oneBlockPalmContract_of_psss hpsss BlockBand.Coarea.FreshPalm.freshEigenpairDensityContract_holds

/-- `normalizerContract_of`, PSSS-only. -/
theorem normalizerContract_of_psss (hpsss : BlockBand.External.PSSS.SourceContract.{0})
    (hMT : MatchedTracesContract) (hPD : PointDensityContract) : NormalizerContract :=
  normalizer_of (pairRegularEvent_of_psss hMT hpsss) hPD
    BlockBand.Coarea.FreshPalm.freshEigenpairDensityContract_holds
    (exactPalm_upper_of_psss hpsss BlockBand.Coarea.FreshPalm.freshEigenpairDensityContract_holds)

/-- **`oneBlockNormalizerContract_of`, from PSSS only.** -/
theorem oneBlockNormalizerContract_of_psss (hpsss : BlockBand.External.PSSS.SourceContract.{0})
    (hMT : MatchedTracesContract) (hPD : PointDensityContract) : OneBlockNormalizerContract :=
  oneBlockNormalizer_of (blockRegularEvent_of_psss hMT hpsss) hPD
    BlockBand.Coarea.FreshPalm.freshEigenpairDensityContract_holds
    (oneBlockPalm_upper_of_psss hpsss BlockBand.Coarea.FreshPalm.freshEigenpairDensityContract_holds)

/-- **`physicalLeadProfileContract_of`, from PSSS**:
`Clocks.PhysicalLeadProfileContract`, with the other hypotheses `MatchedTracesContract`,
`PointDensityContract`, `FreshPalmContract`, `CommonPortMeanContract` and `VanishingBlockAtom`.
-/
theorem physicalLeadProfileContract_of_psss (hpsss : BlockBand.External.PSSS.SourceContract.{0})
    (hMT : MatchedTracesContract) (hPD : PointDensityContract) (hFP : FreshPalmContract)
    (hCPM : CommonPortMeanContract) (hVBA : VanishingBlockAtom) :
    PhysicalLeadProfileContract :=
  have hD : FreshEigenpairDensityContract :=
    BlockBand.Coarea.FreshPalm.freshEigenpairDensityContract_holds
  have hPalm : OneBlockPalmContract := oneBlockPalmContract_holds_psss hpsss
  have hNorm : OneBlockNormalizerContract := oneBlockNormalizerContract_of_psss hpsss hMT hPD
  physicalLeadProfile_of_gaussian_commonPort hPalm hNorm
    (leadGaussianStep_of_oneBlockPalm hD (gaussianRatios_of_contracts hFP hPD hD)
      (blockRegularEvent_of_psss hMT hpsss) hPalm hNorm hVBA)
    (leadCommonPortStep_of
      (BlockBand.Endpoints.Clock.commonPortRatios_of_commonPortMean hCPM) hMT)

end BlockBand.Internal.ReducedInputs
