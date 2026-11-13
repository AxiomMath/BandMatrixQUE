module

public import BlockBand.Endpoints.EndpointsAssemblyDefs
public import BlockBand.Endpoints.Sine.MicroscopicTagBridge
public import BlockBand.Endpoints.Poisson.PoissonEndpoint
public import BlockBand.Endpoints.Response.ResponseVariance
public import BlockBand.Endpoints.Sine.Law
public import BlockBand.Endpoints.Poisson.Law
public import BlockBand.Foundations.StatementDomains

/-!
# Assembly of the critical endpoints theorem

We prove `endpoints_of_inputs`: for every `b ∈ (0,1/2)`, bulk energy `E` and every family satisfying
`IsCriticalFamily`, `HasCriticalEndpoints b E hb hb' family` holds under the hypotheses in its
signature. The conjuncts of `HasCriticalEndpoints` are obtained as follows:
* the variance limit along every critical sequence, and its independence of the spectral weight
  `w`: from `EpMarkStatisticLimit` and `EpStationaryWeightFree`, with stationarity and unit
  intensity from `IsCriticalFamily`;
* `0 < V_τ(φ)`: from `EpRotationFourierDiagonal`, the positivity of each mode variance
  (`responseVariance` and `EpNonzeroResponse`) and a nonzero Fourier coefficient of a nonconstant
  `φ` (Parseval);
* `V_τ(φ) → 0` as `τ ↓ 0`: from `SmallCriticalContract.variance` with `η = 1/2`;
* existence and uniqueness of the sine law and of the unit Poisson law:
  `existsUnique_isSineLaw`, `existsUnique_isUnitPoissonLaw`;
* the sine limit as `τ ↓ 0` and the Poisson limit as `τ → ∞`: from `SineEndpointStatement` and
  `PoissonEndpointStatement`.

The variance is `V_τ(φ) = (markVariance (family τ) w₀ φ).toReal` for one fixed spectral weight `w₀`
(`spectralWeight_nonempty`). The last section gives corollaries in which some of these hypotheses
are discharged by the endpoint theorems.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.Clocks (physicalOneMark PhysicalLeadProfileContract
  NegativeClockContract)
open BlockBand.Internal.Contracts.WindowAngular
open BlockBand.Internal.Contracts.TransmissionPath (transportD0)
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionUniform
  BlockBand.Internal.Contracts.Inputs
open scoped ENNReal BoundedContinuousFunction
open AddCircle (haarAddCircle)

/-!
## 1. The profile functional `ν ↦ |ν(φ) - φ̄|²`
-/

/-- The bounded continuous mark functional `ν ↦ |ν(φ) - φ̄|²` of a profile test `φ`. -/
def ep_profileFunctional (φ : ProfileTest) : MassProfile →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun ν => |(∫ r, φ r ∂(ν : Measure Torus)) - ∫ r, φ r| ^ 2,
      ((ProbabilityMeasure.continuous_integral_boundedContinuousFunction
        (BoundedContinuousFunction.mkOfCompact φ.toContinuousMap)).sub
          continuous_const).abs.pow 2⟩

theorem ep_profileFunctional_apply (φ : ProfileTest) (ν : MassProfile) :
    ep_profileFunctional φ ν = |(∫ r, φ r ∂(ν : Measure Torus)) - ∫ r, φ r| ^ 2 := rfl

theorem ep_profileFunctional_nonneg (φ : ProfileTest) (ν : MassProfile) :
    0 ≤ ep_profileFunctional φ ν := by
  rw [ep_profileFunctional_apply]; positivity

theorem ep_rvFourierTest_nonneg (m : ℤ) (ν : MassProfile) : 0 ≤ rvFourierTest m ν := by
  simp only [rvFourierTest, BoundedContinuousFunction.mkOfBound_coe, ContinuousMap.coe_mk]
  positivity

/-- The finite profile variance is the physical one-mark statistic of the profile
functional. -/
theorem ep_profileVariance_eq {p : Parameters} (R : FiniteRealization p) (E : ℝ)
    (w : SpectralWeight) (φ : ProfileTest) :
    R.profileVariance E w φ = physicalOneMark R E w (ep_profileFunctional φ) := by
  have := BlockBand.Model.Construction.massProfile_opensMeasurableSpace
  unfold FiniteRealization.profileVariance physicalOneMark
  refine integral_congr_ae ?_
  filter_upwards [R.spectral.markedConfig_ae E] with H hH
  rw [hH]
  have hm : Measurable (fun x : MarkedSpectralSpace => w x.1 * ep_profileFunctional φ x.2) :=
    (w.toContinuousMap.continuous.measurable.comp measurable_fst).mul
      ((ep_profileFunctional φ).continuous.measurable.comp measurable_snd)
  rw [integral_finsetSum_measure (fun α _ => integrable_dirac' hm.stronglyMeasurable
    enorm_lt_top)]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [integral_dirac' _ _ hm.stronglyMeasurable]
  rfl

theorem ep_markVariance_eq (P : ProbabilityMeasure MarkedPointMeasure) (w : SpectralWeight)
    (φ : ProfileTest) : markVariance P w φ = ep_limitOneMark P w (ep_profileFunctional φ) := rfl

theorem ep_modeVariance_eq (P : ProbabilityMeasure MarkedPointMeasure) (w : SpectralWeight)
    (m : ℤ) : modeVariance P w m = ep_limitOneMark P w (rvFourierTest (-m)) := rfl

/-!
## 2. Positivity of the limiting mode variances
-/

/-- **Positive mode variance.** For each `m ≠ 0`, the nonzero response at a finite point and the
response variance bound give positive variance in that mode: for a critical family, every `τ > 0`,
every spectral weight `w` and every `m ≠ 0`, the limiting mode variance
`v_m = E Σ w(u)|ν(e^{-2πim·})|²` of `family τ` is positive. Inputs: `responseVariance`,
`EpNonzeroResponse` at `D0 = transportD0 b E`, and the mode limit from `EpMarkStatisticLimit`.
-/
theorem ep_modeVariance_pos (hMom : FullSourceMomentsContract)
    (hUnifLaw : TransmissionLawEnergyUniformContract)
    (hUnifMom : FullSourceMomentsEnergyUniformContract) (hBdry : DualBoundaryStartContract)
    (hLen : TransmissionLengthUniformContract) (hCount : ConditionalBlockGUECount)
    (hLead : PhysicalLeadProfileContract) (hNeg : NegativeClockContract)
    (hMS : EpMarkStatisticLimit) (hNZ : EpNonzeroResponse)
    {b E : ℝ} {hb : 0 < b} {hb' : b < 1 / 2} (hE1 : -2 < E) (hE2 : E < 2)
    {family : PositiveRatio → ProbabilityMeasure MarkedPointMeasure}
    (hfam : IsCriticalFamily b E hb hb' family) (τ : PositiveRatio) (w : SpectralWeight)
    {m : ℤ} (hm : m ≠ 0) : 0 < modeVariance (family τ) w m := by
  obtain ⟨x, hx, J, hJ, hJs⟩ :=
    hNZ (transportD0 b E) (transportD0_pos hb hE1 hE2) τ.1 τ.2 (-m) (neg_ne_zero.2 hm)
  obtain ⟨C, -, hall⟩ := responseVariance hMom hUnifLaw hUnifMom hBdry hLen hCount hLead hNeg
    b hb hb' E hE1 hE2 τ.1 τ.2 x 0 hx.le le_rfl one_pos
  let s := se_criticalSequence τ.1 τ.2
  obtain ⟨R⟩ := hfam.2.1 τ s
  have hlt := (hall (-m)).2 J hJs w s R
  obtain ⟨-, hconv⟩ := hMS b hb hb' E hE1 hE2 family hfam τ w (rvFourierTest (-m))
    (ep_rvFourierTest_nonneg (-m))
  have hc : Tendsto (fun j => ENNReal.ofReal (rvFourierVariance (R j) E w (-m))) atTop
      (𝓝 (ENNReal.ofReal (modeVariance (family τ) w m).toReal)) := by
    rw [ep_modeVariance_eq]
    refine (ENNReal.continuous_ofReal.tendsto _).comp ((hconv s R).congr fun j => ?_)
    exact (rvFourierVariance_eq_physicalOneMark (R j) E w (-m)).symm
  rw [hc.liminf_eq] at hlt
  have hρ := semicircleDensity_pos' hE1 hE2
  have hlhs : 0 < ENNReal.ofReal ((8 * Real.pi * Parameters.semicircleDensity E) ^ 2 * |J| ^ 2) :=
    ENNReal.ofReal_pos.2 (by have := abs_pos.2 hJ.ne'; positivity)
  have hne : ENNReal.ofReal (modeVariance (family τ) w m).toReal ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hlt
    exact (hlhs.trans_le hlt).ne' rfl
  have hpos : 0 < (modeVariance (family τ) w m).toReal := by
    by_contra hle
    exact hne (ENNReal.ofReal_of_nonpos (not_lt.1 hle))
  exact (ENNReal.toReal_pos_iff.1 hpos).1

/-!
## 3. A nonconstant test has a nonzero Fourier coefficient
-/

/-- A nonconstant (continuous) profile test has a nonzero Fourier coefficient at some `m ≠ 0`.
Proof: otherwise `φ - φ̂₀` has all Fourier coefficients zero, so by Parseval it vanishes
`haarAddCircle`-a.e., hence everywhere by continuity. -/
theorem ep_exists_fourierCoeff_ne_zero (φ : ProfileTest) :
    ∃ m : ℤ, m ≠ 0 ∧ fourierCoeff (fun r : Torus => ((φ r : ℝ) : ℂ)) m ≠ 0 := by
  by_contra h
  push Not at h
  set f : Torus → ℂ := fun r => ((φ r : ℝ) : ℂ) with hf
  set c : ℂ := fourierCoeff f 0
  have hfc : Continuous f := Complex.continuous_ofReal.comp φ.toContinuousMap.continuous
  let g : C(Torus, ℂ) := ⟨fun r => f r + (-c) • fourier (T := 1) 0 r,
    hfc.add ((fourier (T := 1) 0).continuous.const_smul (-c))⟩
  have hfi : Integrable f haarAddCircle :=
    (BoundedContinuousFunction.mkOfCompact ⟨f, hfc⟩).integrable _
  have hgi : Integrable (fun r => (-c) • fourier (T := 1) 0 r) haarAddCircle :=
    (BoundedContinuousFunction.mkOfCompact
      ⟨fun r => (-c) • fourier (T := 1) 0 r, (fourier (T := 1) 0).continuous.const_smul (-c)⟩).integrable _
  have hcoef : ∀ n : ℤ, fourierCoeff g n = 0 := by
    intro n
    have hadd := congrFun (fourierCoeff.add hfi hgi) n
    have hsm := fourierCoeff.const_smul (fun r => fourier (T := 1) 0 r) (-c) n
    have hF := congrFun (fourierCoeff_fourier (T := 1) 0) n
    have hg : fourierCoeff g n = fourierCoeff f n + (-c) • fourierCoeff (⇑(fourier (T := 1) 0)) n :=
      hadd.trans (by rw [Pi.add_apply]; exact congrArg _ hsm)
    rw [hg, hF]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [c]
    · simp [h n hn, hn]
  have hpars := tsum_sq_fourierCoeff (T := 1) (ContinuousMap.toLp (E := ℂ) 2 haarAddCircle ℂ g)
  simp only [fourierCoeff_toLp, hcoef, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, tsum_zero] at hpars
  have hae : (fun t => ‖(ContinuousMap.toLp (E := ℂ) 2 haarAddCircle ℂ g) t‖ ^ 2)
      =ᵐ[haarAddCircle] fun t => ‖g t‖ ^ 2 := by
    filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (E := ℂ) (p := 2) haarAddCircle g] with t ht
    rw [ht]
  rw [integral_congr_ae hae] at hpars
  have hgc : Continuous fun t => ‖g t‖ ^ 2 := g.continuous.norm.pow 2
  have hint : Integrable (fun t => ‖g t‖ ^ 2) haarAddCircle :=
    (BoundedContinuousFunction.mkOfCompact ⟨_, hgc⟩).integrable _
  have hz := (integral_eq_zero_iff_of_nonneg (fun t => by positivity) hint).1 hpars.symm
  have hz' : (fun t => ‖g t‖ ^ 2) = fun _ => (0 : ℝ) :=
    (Continuous.ae_eq_iff_eq haarAddCircle hgc continuous_const).1 hz
  obtain ⟨x, y, hxy⟩ := φ.nonconstant
  have hgx : ∀ t, f t = c := by
    intro t
    have := congrFun hz' t
    simp only [pow_eq_zero_iff two_ne_zero, norm_eq_zero] at this
    have h1 : g t = f t + (-c) • fourier 0 t := rfl
    rw [h1, fourier_zero, smul_eq_mul, mul_one] at this
    linear_combination this
  have := (hgx x).trans (hgx y).symm
  simp only [hf, Complex.ofReal_inj] at this
  exact hxy this

/-!
## 4. The small-ratio limit
-/

theorem ep_tendsto_val_atBot : Tendsto (fun τ : PositiveRatio => τ.1) atBot (𝓝 0) := by
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun τ => ha.trans τ.2,
    fun a ha => ?_⟩
  filter_upwards [eventually_le_atBot (⟨a / 2, by positivity⟩ : PositiveRatio)] with τ hτ
  have : τ.1 ≤ a / 2 := hτ
  linarith

/-!
## 5. The assembly
-/

/-- **The critical endpoints theorem**: for every `b ∈ (0,1/2)`, bulk `E` and family satisfying
`IsCriticalFamily`, `HasCriticalEndpoints b E hb hb' family`.

Besides the contract hypotheses, it assumes the sine endpoint statement `SineEndpointStatement`,
the Poisson endpoint statement `PoissonEndpointStatement`, the nonzero response
`EpNonzeroResponse`, and the variance statements `EpMarkStatisticLimit`,
`EpStationaryWeightFree` and `EpRotationFourierDiagonal`. -/
theorem endpoints_of_inputs (hMom : FullSourceMomentsContract)
    (hUnifLaw : TransmissionLawEnergyUniformContract)
    (hUnifMom : FullSourceMomentsEnergyUniformContract) (hBdry : DualBoundaryStartContract)
    (hLen : TransmissionLengthUniformContract) (hCount : ConditionalBlockGUECount)
    (hLead : PhysicalLeadProfileContract) (hNeg : NegativeClockContract)
    (hSmall : SmallCriticalContract)
    (hSE : SineEndpointStatement) (hPE : PoissonEndpointStatement) (hNZ : EpNonzeroResponse)
    (hMS : EpMarkStatisticLimit) (hSW : EpStationaryWeightFree)
    (hFD : EpRotationFourierDiagonal) :
    ∀ (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), (-2 < E ∧ E < 2) →
      ∀ family : PositiveRatio → ProbabilityMeasure MarkedPointMeasure,
        IsCriticalFamily b E hb hb' family →
          HasCriticalEndpoints b E hb hb' family := by
  intro b E hb hb' hE family hfam
  obtain ⟨w₀⟩ := BlockBand.Foundations.spectralWeight_nonempty
  have hstat : ∀ τ, IsSpectrallyStationary (family τ) := hfam.2.2.2.2.2.2.1
  have hrot : ∀ τ, IsMarkRotationInvariant (family τ) := hfam.2.2.2.2.2.2.2
  have hunit : ∀ τ, HasUnitSpectralIntensity (family τ) := hfam.2.2.2.2.1
  have hconv := hfam.2.2.1
  refine ⟨fun τ φ => (markVariance (family τ) w₀ φ).toReal, ?_, ?_, ?_, existsUnique_isSineLaw,
    hSE.2 b hb hb' E hE.1 hE.2 family hfam, existsUnique_isUnitPoissonLaw,
    hPE.2 b hb hb' E hE.1 hE.2 family hfam⟩
  · -- the variance limit exists and does not depend on `w`
    intro τ w φ s R
    obtain ⟨-, hc⟩ := hMS b hb hb' E hE.1 hE.2 family hfam τ w (ep_profileFunctional φ)
      (ep_profileFunctional_nonneg φ)
    show Tendsto _ atTop (𝓝 (markVariance (family τ) w₀ φ).toReal)
    rw [ep_markVariance_eq, hSW (family τ) (hstat τ) (hunit τ) _ (ep_profileFunctional_nonneg φ)
      w₀ w]
    exact (hc s R).congr fun j => (ep_profileVariance_eq (R j) E w φ).symm
  · -- positivity
    intro τ φ
    obtain ⟨hfin, -⟩ := hMS b hb hb' E hE.1 hE.2 family hfam τ w₀ (ep_profileFunctional φ)
      (ep_profileFunctional_nonneg φ)
    rw [← ep_markVariance_eq] at hfin
    refine ENNReal.toReal_pos ?_ hfin
    rw [hFD (family τ) (hrot τ) (hunit τ) w₀ φ]
    obtain ⟨m, hm, hcoef⟩ := ep_exists_fourierCoeff_ne_zero φ
    have hpos : 0 < (if m = 0 then 0 else
        ENNReal.ofReal (‖fourierCoeff (fun r : Torus => ((φ r : ℝ) : ℂ)) m‖ ^ 2) *
          modeVariance (family τ) w₀ (-m)) := by
      simp only [hm, ↓reduceIte]
      exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 (by positivity)).ne'
        (ep_modeVariance_pos hMom hUnifLaw hUnifMom hBdry hLen hCount hLead hNeg hMS hNZ hE.1 hE.2
          hfam τ w₀ (neg_ne_zero.2 hm)).ne'
    exact (hpos.trans_le (ENNReal.le_tsum (f := fun k : ℤ => if k = 0 then 0 else
      ENNReal.ofReal (‖fourierCoeff (fun r : Torus => ((φ r : ℝ) : ℂ)) k‖ ^ 2) *
        modeVariance (family τ) w₀ (-k)) m)).ne'
  · -- the variance tends to `0` as `τ ↓ 0`
    intro φ
    obtain ⟨C, hC0, hCb⟩ := hSmall.variance b hb hb' E (by nlinarith [hE.1, hE.2]) (1 / 2)
      (by norm_num) (by norm_num)
    have hφc : Continuous (φ : Torus → ℝ) := φ.toContinuousMap.continuous
    obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn
      (f := fun r : Torus => φ r - ∫ r', φ r') (hφc.sub continuous_const).continuousOn
    have hM' : ∀ r, |φ r - ∫ r', φ r'| ≤ M := fun r => by
      simpa [Real.norm_eq_abs] using hM r (mem_univ r)
    have key : ∀ τ : PositiveRatio, τ.1 ≤ 1 →
        (markVariance (family τ) w₀ φ).toReal ≤ C * M ^ 2 * τ.1 ^ (1 - 1 / 2 : ℝ) := by
      intro τ hτ1
      let s := se_criticalSequence τ.1 τ.2
      obtain ⟨R⟩ := hfam.2.1 τ s
      have hlim : IsCriticalMarkedLimit τ.1 b E hb hb' (family τ) :=
        ⟨s, R, id, strictMono_id, hconv τ s R⟩
      have hbd := hCb τ.1 τ.2 hτ1 (family τ) hlim w₀ φ ⟨hφc, φ.smooth_lift⟩ M hM'
      exact ENNReal.toReal_le_of_le_ofReal (by have := τ.2.le; positivity) hbd
    have hcont : ContinuousAt (fun x : ℝ => C * M ^ 2 * x ^ (1 - 1 / 2 : ℝ)) 0 :=
      continuousAt_const.mul (Real.continuousAt_rpow_const 0 _ (Or.inr (by norm_num)))
    have hlim0 := hcont.tendsto.comp ep_tendsto_val_atBot
    rw [Real.zero_rpow (by norm_num), mul_zero] at hlim0
    refine squeeze_zero' (Eventually.of_forall fun τ => ENNReal.toReal_nonneg) ?_ hlim0
    filter_upwards [eventually_le_atBot (⟨1, one_pos⟩ : PositiveRatio)] with τ hτ
    exact key τ hτ

/-!
## 6. Corollaries through the endpoint theorems
-/

section Corollaries

open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.ClocksCommonPort
open BlockBand.Internal.Contracts.ClocksLeadProfile BlockBand.Internal.Contracts.RingSymmetry
open BlockBand.Internal.Contracts.InputsRing (RingBlockModels)
open BlockBand.External.PSSS (SourceContract)

/-- **The critical endpoints theorem with the Poisson endpoint supplied** by
`poissonEndpoint_of_sameVolume`: the hypotheses of `endpoints_of_inputs` without
`PoissonEndpointStatement`, plus `CriticalDensity`, `RingBlockModels`, `ProjectedWegner`, the
PSSS `SourceContract` and `PeSameVolumeLogError`.
-/
theorem endpoints_of_sameVolume (hMom : FullSourceMomentsContract)
    (hUnifLaw : TransmissionLawEnergyUniformContract)
    (hUnifMom : FullSourceMomentsEnergyUniformContract) (hBdry : DualBoundaryStartContract)
    (hLen : TransmissionLengthUniformContract) (hCount : ConditionalBlockGUECount)
    (hLead : PhysicalLeadProfileContract) (hNeg : NegativeClockContract)
    (hSmall : SmallCriticalContract)
    (source : SourceContract.{0}) (hDens : CriticalDensity) (hRing : RingBlockModels)
    (hWegner : ProjectedWegner) (hSV : PeSameVolumeLogError)
    (hSE : SineEndpointStatement) (hNZ : EpNonzeroResponse)
    (hMS : EpMarkStatisticLimit) (hSW : EpStationaryWeightFree)
    (hFD : EpRotationFourierDiagonal) :
    ∀ (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), (-2 < E ∧ E < 2) →
      ∀ family : PositiveRatio → ProbabilityMeasure MarkedPointMeasure,
        IsCriticalFamily b E hb hb' family →
          HasCriticalEndpoints b E hb hb' family :=
  endpoints_of_inputs hMom hUnifLaw hUnifMom hBdry hLen hCount hLead hNeg hSmall hSE
    (poissonEndpoint_of_sameVolume source hDens hRing hWegner hCount hSV) hNZ hMS hSW hFD

/-- **The critical endpoints theorem, final form.** Both endpoints are supplied by theorems:
`sineEndpoint_of_taggedFlat` and `poissonEndpoint_of_sameVolume`. Hypotheses: the input
statements `ExternalSine`, `PhysicalBlockConditionalCount`, `ConditionalBlockGUECount`,
`CriticalDensity`, `RingBlockModels`, `ProjectedWegner`, `RingRotationInvariance`,
`VanishingBlockAtom`, `MatchedTracesContract`, `CoareaContract`, `FreshEigenpairDensityContract`,
`SmallCriticalContract`, `FullSourceMomentsContract`, `TransmissionLawEnergyUniformContract`,
`FullSourceMomentsEnergyUniformContract`, `DualBoundaryStartContract`,
`TransmissionLengthUniformContract`, `PairRegularEventContract`, `ExactPalmContract`,
`OneBlockPalmContract`, `OneBlockNormalizerContract`, `UniformClockTagsPalmContract`,
`ClockCovarianceStabilityContract`, `BlockRegularEventContract`,
`LeadFieldIdentificationContract`, `UniformClockTagsCommonPortContract`, `NegativeClockContract`,
`ClockSmallBallContract`, `PhysicalLeadProfileContract`, the PSSS `SourceContract`, and
`LmfTaggedFlat`, `FaShiftedMassPalm`, `PeSameVolumeLogError`, `EpNonzeroResponse`, and the variance
steps `EpMarkStatisticLimit`, `EpStationaryWeightFree`, `EpRotationFourierDiagonal`.
-/
theorem endpoints_of_taggedFlat
    
    (hMom : FullSourceMomentsContract) (hUnifLaw : TransmissionLawEnergyUniformContract)
    (hUnifMom : FullSourceMomentsEnergyUniformContract) (hBdry : DualBoundaryStartContract)
    (hLen : TransmissionLengthUniformContract) (hCount : ConditionalBlockGUECount)
    (hLead : PhysicalLeadProfileContract) (hNeg : NegativeClockContract)
    
    (hSmall : SmallCriticalContract)
    
    (source : SourceContract.{0}) (hDens : CriticalDensity) (hRing : RingBlockModels)
    (hWegner : ProjectedWegner)
    
    (hExt : ExternalSine) (hCo : CoareaContract) (hPair : PairRegularEventContract)
    (hPhysCount : PhysicalBlockConditionalCount) (hExact : ExactPalmContract)
    (hRot : RingRotationInvariance) (hAtom : VanishingBlockAtom) (hPalm : OneBlockPalmContract)
    (hNorm : OneBlockNormalizerContract) (hFED : FreshEigenpairDensityContract)
    (hUCT : UniformClockTagsPalmContract) (hCS : ClockCovarianceStabilityContract)
    (hReg : BlockRegularEventContract) (hL : LeadFieldIdentificationContract)
    (hCP : UniformClockTagsCommonPortContract) (hMT : MatchedTracesContract)
    (hSmallBall : ClockSmallBallContract)
    -- further hypotheses
    (hTag : LmfTaggedFlat) (hShift : FaShiftedMassPalm) (hSV : PeSameVolumeLogError)
    (hNZ : EpNonzeroResponse)
    -- variance hypotheses
    (hMS : EpMarkStatisticLimit) (hSW : EpStationaryWeightFree)
    (hFD : EpRotationFourierDiagonal) :
    ∀ (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), (-2 < E ∧ E < 2) →
      ∀ family : PositiveRatio → ProbabilityMeasure MarkedPointMeasure,
        IsCriticalFamily b E hb hb' family →
          HasCriticalEndpoints b E hb hb' family :=
  endpoints_of_sameVolume hMom hUnifLaw hUnifMom hBdry hLen hCount hLead hNeg hSmall source hDens
    hRing hWegner hSV
    (sineEndpoint_of_taggedFlat hExt hCo hPair hPhysCount hExact hShift hRot hAtom hPalm hNorm hFED
      hUCT hCS hReg hL hCP hMT hNeg hSmallBall hDens hTag)
    hNZ hMS hSW hFD

end Corollaries

end BlockBand.Endpoints
